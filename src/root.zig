//! By convention, root.zig is the root source file when making a library.
const std = @import("std");
const testing = std.testing;
const FileReader = std.fs.File.Reader;
const Reader = std.Io.Reader;
const Allocator = std.mem.Allocator;

pub const KaitaiStream = struct {
    reader_impl: union(enum) {
        file: *FileReader,
        bytes: Reader,
    },
    bits_left: u3 = 0,
    bits: u7 = 0,

    pub fn fromFileReader(file_reader: *FileReader) KaitaiStream {
        return .{ .reader_impl = .{
            .file = file_reader,
        } };
    }

    pub fn fromBytes(bytes: []const u8) KaitaiStream {
        return .{ .reader_impl = .{ .bytes = Reader.fixed(bytes) } };
    }

    fn reader(self: *KaitaiStream) *Reader {
        return switch (self.reader_impl) {
            .file => |file_reader| &file_reader.interface,
            .bytes => |*bytes_reader| bytes_reader,
        };
    }

    //#region Stream positioning

    pub fn isEof(self: *KaitaiStream) error{ReadFailed}!bool {
        if (self.bits_left > 0) {
            return false;
        }
        if (self.reader().peekByte()) |_| {
            return false;
        } else |err| {
            return switch (err) {
                error.EndOfStream => true,
                else => |e| e,
            };
        }
    }

    // // NOTE: as of Zig 0.15.1
    // // (https://ziglang.org/documentation/0.15.1/std/#std.fs.File.Reader.atEnd), this implementation
    // // is broken. If the `size` field is set to a non-`null` value (probably because the `size()`
    // // method was called before), it may return `true` when the EOF hasn't been reached yet, because
    // // the `atEnd` method contains `return size - r.pos == 0`, which uses `r.pos` (which includes
    // // bytes that are prebuffered but haven't been read out yet) instead of `logicalPos`.
    // //
    // // If the `size` field is `null` (which is default), it always returns `false`. That may work
    // // for the semantics of the C `feof` function, which is probably intended (the comment "Even if
    // // stat fails, size is set when end is encountered." indicates this). However, in Kaitai Struct
    // // semantics, `_io.eof` is supposed to return `true` even before any explicit read operation
    // // fails, so this is not compatible.
    // pub fn isEof(self: *KaitaiStream) bool {
    //     return self.reader.atEnd();
    // }

    pub fn seek(self: *KaitaiStream, new_pos: u64) FileReader.SeekError!void {
        switch (self.reader_impl) {
            .file => |file_reader| return file_reader.seekTo(new_pos),
            .bytes => |*bytes_reader| {
                const target_pos = std.math.cast(usize, new_pos) orelse return error.Unseekable;
                bytes_reader.seek = target_pos;
            },
        }
    }

    pub fn pos(self: *const KaitaiStream) u64 {
        return switch (self.reader_impl) {
            .file => |file_reader| file_reader.logicalPos(),
            .bytes => |*bytes_reader| bytes_reader.seek,
        };
    }

    pub fn size(self: *KaitaiStream) FileReader.SizeError!u64 {
        return switch (self.reader_impl) {
            .file => |file_reader| file_reader.getSize(),
            .bytes => |*bytes_reader| bytes_reader.end,
        };
    }

    //#endregion

    //#region Integer types

    //#region Signed

    pub fn readS1(self: *KaitaiStream) !i8 {
        return self.reader().takeByteSigned();
    }

    //#region Big-endian

    pub fn readS2be(self: *KaitaiStream) !i16 {
        return self.reader().takeInt(i16, .big);
    }

    pub fn readS4be(self: *KaitaiStream) !i32 {
        return self.reader().takeInt(i32, .big);
    }

    pub fn readS8be(self: *KaitaiStream) !i64 {
        return self.reader().takeInt(i64, .big);
    }

    //#endregion

    //#region Little-endian

    pub fn readS2le(self: *KaitaiStream) !i16 {
        return self.reader().takeInt(i16, .little);
    }

    pub fn readS4le(self: *KaitaiStream) !i32 {
        return self.reader().takeInt(i32, .little);
    }

    pub fn readS8le(self: *KaitaiStream) !i64 {
        return self.reader().takeInt(i64, .little);
    }

    //#endregion

    //#endregion

    //#region Unsigned

    pub fn readU1(self: *KaitaiStream) !u8 {
        return self.reader().takeByte();
    }

    //#region Big-endian

    pub fn readU2be(self: *KaitaiStream) !u16 {
        return self.reader().takeInt(u16, .big);
    }

    pub fn readU4be(self: *KaitaiStream) !u32 {
        return self.reader().takeInt(u32, .big);
    }

    pub fn readU8be(self: *KaitaiStream) !u64 {
        return self.reader().takeInt(u64, .big);
    }

    //#endregion

    //#region Little-endian

    pub fn readU2le(self: *KaitaiStream) !u16 {
        return self.reader().takeInt(u16, .little);
    }

    pub fn readU4le(self: *KaitaiStream) !u32 {
        return self.reader().takeInt(u32, .little);
    }

    pub fn readU8le(self: *KaitaiStream) !u64 {
        return self.reader().takeInt(u64, .little);
    }

    //#endregion

    //#endregion

    //#endregion

    //#region Floating point types

    //#region Big-endian

    pub fn readF4be(self: *KaitaiStream) !f32 {
        return @bitCast(try self.readU4be());
    }

    pub fn readF8be(self: *KaitaiStream) !f64 {
        return @bitCast(try self.readU8be());
    }

    //#endregion

    //#region Little-endian

    pub fn readF4le(self: *KaitaiStream) !f32 {
        return @bitCast(try self.readU4le());
    }

    pub fn readF8le(self: *KaitaiStream) !f64 {
        return @bitCast(try self.readU8le());
    }

    //#endregion

    //#endregion

    //#region Unaligned bit values

    fn alignToByte(self: *KaitaiStream) void {
        self.bits_left = 0;
        self.bits = 0;
    }

    pub fn readBitsIntBe(self: *KaitaiStream, n: u7) !u64 {
        if (n > 64) {
            return error.ReadBitsTooLarge;
        }

        var res: u64 = 0;

        const bits_needed = @as(i8, n) - self.bits_left;
        self.bits_left = @intCast(@mod(-bits_needed, 8));

        if (bits_needed > 0) {
            // 1 bit  => 1 byte
            // 8 bits => 1 byte
            // 9 bits => 2 bytes
            const bytes_needed = std.math.divCeil(usize, @intCast(bits_needed), 8) catch unreachable;
            const buf = try self.reader().take(bytes_needed);
            for (buf) |b| {
                res = res << 8 | b;
            }

            const new_bits: u7 = @truncate(res);
            res = res >> self.bits_left | (if (bits_needed < 64) @as(u64, self.bits) << @intCast(bits_needed) else 0);
            self.bits = new_bits;
        } else {
            res = self.bits >> @intCast(-bits_needed);
        }

        const mask = (@as(u8, 1) << self.bits_left) - 1;
        self.bits &= @intCast(mask);

        return res;
    }

    pub fn readBitsIntLe(self: *KaitaiStream, n: u7) !u64 {
        if (n > 64) {
            return error.ReadBitsTooLarge;
        }

        var res: u64 = 0;
        const bits_needed = @as(i8, n) - self.bits_left;

        if (bits_needed > 0) {
            // 1 bit  => 1 byte
            // 8 bits => 1 byte
            // 9 bits => 2 bytes
            const bytes_needed = std.math.divCeil(usize, @intCast(bits_needed), 8) catch unreachable;
            const buf = try self.reader().take(bytes_needed);
            {
                var i = bytes_needed;
                while (i > 0) {
                    i -= 1;
                    res = res << 8 | buf[i];
                }
            }

            const new_bits: u7 = @truncate(if (bits_needed < 64) res >> @intCast(bits_needed) else 0);
            res = res << self.bits_left | self.bits;
            self.bits = new_bits;
        } else {
            res = self.bits;
            self.bits = if (n < 7) self.bits >> @intCast(n) else 0;
        }

        self.bits_left = @intCast(@mod(-bits_needed, 8));

        if (n < 64) {
            const mask = (@as(u64, 1) << @intCast(n)) - 1;
            res &= mask;
        }

        return res;
    }

    //#endregion

    //#region Byte arrays

    pub fn readBytes(self: *KaitaiStream, allocator: Allocator, len: usize) ![]u8 {
        return self.reader().readAlloc(allocator, len);
    }

    pub fn readBytesFull(self: *KaitaiStream, allocator: Allocator) error{ ReadFailed, OutOfMemory }![]u8 {
        return self.reader().allocRemaining(allocator, .unlimited) catch |err| switch (err) {
            error.StreamTooLong => unreachable, // unlimited is passed
            else => |e| e,
        };
    }

    pub fn readBytesTerm(
        self: *KaitaiStream,
        allocator: Allocator,
        term: u8,
        include_term: bool,
        consume_term: bool,
        eos_error: bool,
    ) error{ ReadFailed, EndOfStream, OutOfMemory }![]u8 {
        var allocating_writer = std.Io.Writer.Allocating.init(allocator);
        defer allocating_writer.deinit();
        const writer = &allocating_writer.writer;
        const r = self.reader();
        _ = r.streamDelimiterEnding(writer, term) catch |err| {
            return switch (err) {
                // As of Zig 0.15.1,
                // [`std.Io.Writer.Allocating.drain`](https://ziglang.org/documentation/0.15.1/std/#std.Io.Writer.Allocating.drain)
                // returns `error.WriteFailed` if and only if
                // [`std.array_list.Aligned.ensureUnusedCapacity`](https://ziglang.org/documentation/0.15.1/std/#std.array_list.Aligned.ensureUnusedCapacity)
                // returns `error.OutOfMemory` - see line
                // https://github.com/ziglang/zig/blob/3db960767d12b6214bcf43f1966a037c7a586a12/lib/std/Io/Writer.zig#L2633.
                // Since the fact that we're using any `std.Io.Writer` here is an implementation
                // detail, it doesn't really make sense to propagate `error.WriteFailed` out to
                // callers of `readBytesTerm`, so we convert it back to `error.OutOfMemory`.
                error.WriteFailed => error.OutOfMemory,
                else => |e| e,
            };
        };
        if (r.seek == r.end) {
            if (eos_error) {
                return error.EndOfStream;
            }
        } else {
            if (include_term) {
                // We deliberately ignore the possibility of combining `include: true` with
                // `consume: false` because it doesn't make sense and will be rejected by the
                // compiler in a future version of Kaitai Struct.
                writer.writeByte(try r.takeByte()) catch return error.OutOfMemory;
            } else if (consume_term) {
                _ = try r.takeByte();
            }
        }
        return allocating_writer.toOwnedSlice();
    }

    //#endregion
};

test "read file" {
    const file = try std.fs.cwd().openFile("test.bin", .{});
    defer file.close();
    var buffer: [4096]u8 = undefined;
    var reader = file.reader(&buffer);
    var _io = KaitaiStream.fromFileReader(&reader);
    try testing.expectEqual(3, _io.size());
    try testing.expectEqual(0, _io.pos());
    try testing.expectEqual(0xc2, _io.readU1());
    try testing.expectEqual(1, _io.pos());
    try testing.expectEqual(-0x5d, _io.readS1());
    try testing.expectEqual(false, _io.isEof());
    try testing.expectEqual(2, _io.pos());
    try testing.expectEqual(0x0a, _io.readS1());
    try testing.expectEqual(true, _io.isEof());
    try testing.expectEqual(3, _io.pos());
    try testing.expectError(error.EndOfStream, _io.readU1());
    try testing.expectError(error.EndOfStream, _io.readS1());
    try _io.seek(0);
    try testing.expectEqual(0, _io.pos());
    try testing.expectEqual(0xa3c2, _io.readU2le());
    try testing.expectError(error.EndOfStream, _io.readS2be());
    try testing.expectEqual(2, _io.pos());
}

test "isEof on reader failure" {
    const file = try std.fs.cwd().openFile("test.bin", .{});
    var buffer: [1]u8 = undefined;
    var reader = file.reader(&buffer);
    var _io = KaitaiStream.fromFileReader(&reader);
    try testing.expectEqual(false, _io.isEof());
    try testing.expectEqual(0xc2, _io.readU1());
    file.close();
    try testing.expectError(error.ReadFailed, _io.isEof());
}

test "readBytes" {
    const file = try std.fs.cwd().openFile("test.bin", .{});
    defer file.close();
    var buffer: [4096]u8 = undefined;
    var reader = file.reader(&buffer);
    var _io = KaitaiStream.fromFileReader(&reader);
    const allocator = std.testing.allocator;
    try testing.expectEqual(0xc2, _io.readU1());
    const bytes = try _io.readBytes(allocator, 2);
    defer allocator.free(bytes);
    try testing.expectEqualStrings("\xa3\x0a", bytes);
}

test "readBytesFull" {
    const file = try std.fs.cwd().openFile("test.bin", .{});
    defer file.close();
    var buffer: [4096]u8 = undefined;
    var reader = file.reader(&buffer);
    var _io = KaitaiStream.fromFileReader(&reader);
    const allocator = std.testing.allocator;
    try testing.expectEqual(0xc2, _io.readU1());
    const bytes = try _io.readBytesFull(allocator);
    defer allocator.free(bytes);
    try testing.expectEqualStrings("\xa3\x0a", bytes);
}

test "readBytesTerm - `include: false`, `consume: true`, `eos-error: true` (default)" {
    const file = try std.fs.cwd().openFile("test.bin", .{});
    defer file.close();
    var buffer: [4096]u8 = undefined;
    var reader = file.reader(&buffer);
    var _io = KaitaiStream.fromFileReader(&reader);
    const allocator = std.testing.allocator;
    const bytes = try _io.readBytesTerm(allocator, '\x0a', false, true, true);
    defer allocator.free(bytes);
    try testing.expectEqualStrings("\xc2\xa3", bytes);
    try testing.expectEqual(3, _io.pos());
}

test "readBytesTerm - `include: false`, `consume: false` (!), `eos-error: true`" {
    const file = try std.fs.cwd().openFile("test.bin", .{});
    defer file.close();
    var buffer: [4096]u8 = undefined;
    var reader = file.reader(&buffer);
    var _io = KaitaiStream.fromFileReader(&reader);
    const allocator = std.testing.allocator;
    const bytes = try _io.readBytesTerm(allocator, '\x0a', false, false, true);
    defer allocator.free(bytes);
    try testing.expectEqualStrings("\xc2\xa3", bytes);
    try testing.expectEqual(2, _io.pos());
}

test "readBytesTerm - `include: true` (!), `consume: true`, `eos-error: true`" {
    const file = try std.fs.cwd().openFile("test.bin", .{});
    defer file.close();
    var buffer: [4096]u8 = undefined;
    var reader = file.reader(&buffer);
    var _io = KaitaiStream.fromFileReader(&reader);
    const allocator = std.testing.allocator;
    const bytes = try _io.readBytesTerm(allocator, '\x0a', true, false, true);
    defer allocator.free(bytes);
    try testing.expectEqualStrings("\xc2\xa3\x0a", bytes);
    try testing.expectEqual(3, _io.pos());
}

test "readBytesTerm - `include: true` (!), `consume: true`, `eos-error: true`, but terminator is not present" {
    const file = try std.fs.cwd().openFile("test.bin", .{});
    defer file.close();
    var buffer: [4096]u8 = undefined;
    var reader = file.reader(&buffer);
    var _io = KaitaiStream.fromFileReader(&reader);
    const allocator = std.testing.allocator;
    try testing.expectError(error.EndOfStream, _io.readBytesTerm(allocator, '\x00', true, true, true));
    try testing.expectEqual(3, _io.pos());
}

test "readBytesTerm - `include: true` (!), `consume: true`, `eos-error: false` (!)" {
    const file = try std.fs.cwd().openFile("test.bin", .{});
    defer file.close();
    var buffer: [4096]u8 = undefined;
    var reader = file.reader(&buffer);
    var _io = KaitaiStream.fromFileReader(&reader);
    const allocator = std.testing.allocator;
    const bytes = try _io.readBytesTerm(allocator, '\x00', true, true, false);
    defer allocator.free(bytes);
    try testing.expectEqualStrings("\xc2\xa3\x0a", bytes);
    try testing.expectEqual(3, _io.pos());
}

test "readF4be" {
    var _io = KaitaiStream.fromBytes(&.{ 0x3f, 0xc0, 0x00, 0x00 });
    try testing.expectEqual(1.5, _io.readF4be());
}

test "readF4le" {
    var _io = KaitaiStream.fromBytes(&.{ 0x00, 0x00, 0xc0, 0x3f });
    try testing.expectEqual(1.5, _io.readF4le());
}

test "readF8be" {
    var _io = KaitaiStream.fromBytes(&.{ 0x3f, 0xf8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 });
    try testing.expectEqual(1.5, _io.readF8be());
}

test "readF8le" {
    var _io = KaitaiStream.fromBytes(&.{ 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xf8, 0x3f });
    try testing.expectEqual(1.5, _io.readF8le());
}

test "readBitsIntBe - aligned b64" {
    var _io = KaitaiStream.fromBytes(&.{ 0xEC, 0xBB, 0xA3, 0x14, 0x8A, 0xD4, 0xCC, 0x34 });
    try testing.expectEqual(0xECBB_A314_8AD4_CC34, _io.readBitsIntBe(64));
}

test "readBitsIntBe - unaligned b64" {
    // See:
    //
    // * https://github.com/kaitai-io/kaitai_struct_tests/blob/8bee144acd5981a78dc6ae0ce815c5d4f574cf2a/formats/bits_unaligned_b64_be.ksy
    // * https://github.com/kaitai-io/kaitai_struct_tests/blob/8bee144acd5981a78dc6ae0ce815c5d4f574cf2a/spec/ks/bits_unaligned_b64_be.kst

    // EC BB A3 14 8A D4 CC 34 8E (1 + 64 + 7) = 1|1101100 10111011 10100011 00010100 10001010 11010100 11001100 00110100 1|000_1110
    var _io = KaitaiStream.fromBytes(&.{ 0xEC, 0xBB, 0xA3, 0x14, 0x8A, 0xD4, 0xCC, 0x34, 0x8E });
    try testing.expectEqual(0b1, _io.readBitsIntBe(1));
    try testing.expectEqual(0b1101100_10111011_10100011_00010100_10001010_11010100_11001100_00110100_1, _io.readBitsIntBe(64));
    try testing.expectEqual(0b000_1110, _io.readBitsIntBe(7));
}

test "readBitsIntLe - aligned b64" {
    var _io = KaitaiStream.fromBytes(&.{ 0xEC, 0xBB, 0xA3, 0x14, 0x8A, 0xD4, 0xCC, 0x34 });
    try testing.expectEqual(0x34CC_D48A_14A3_BBEC, _io.readBitsIntLe(64));
}

test "readBitsIntLe - unaligned b64" {
    // See:
    //
    // * https://github.com/kaitai-io/kaitai_struct_tests/blob/8bee144acd5981a78dc6ae0ce815c5d4f574cf2a/formats/bits_unaligned_b64_le.ksy
    // * https://github.com/kaitai-io/kaitai_struct_tests/blob/8bee144acd5981a78dc6ae0ce815c5d4f574cf2a/spec/ks/bits_unaligned_b64_le.kst

    // EC BB A3 14 8A D4 CC 34 8E (1 + 64 + 7) = 1110110|0 10111011 10100011 00010100 10001010 11010100 11001100 00110100 1000_111|0
    var _io = KaitaiStream.fromBytes(&.{ 0xEC, 0xBB, 0xA3, 0x14, 0x8A, 0xD4, 0xCC, 0x34, 0x8E });
    try testing.expectEqual(0b0, _io.readBitsIntLe(1));
    try testing.expectEqual(0b0_00110100_11001100_11010100_10001010_00010100_10100011_10111011_1110110, _io.readBitsIntLe(64));
    try testing.expectEqual(0b1000_111, _io.readBitsIntLe(7));
}
