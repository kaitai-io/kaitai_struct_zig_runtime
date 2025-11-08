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
        return .{
            .reader_impl = .{
                .file = file_reader,
            },
        };
    }

    pub fn fromBytes(bytes: []const u8) KaitaiStream {
        return .{
            .reader_impl = .{
                .bytes = Reader.fixed(bytes),
            },
        };
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
        self.alignToByte();
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
        self.alignToByte();
        return self.reader().takeByteSigned();
    }

    //#region Big-endian

    pub fn readS2be(self: *KaitaiStream) !i16 {
        self.alignToByte();
        return self.reader().takeInt(i16, .big);
    }

    pub fn readS4be(self: *KaitaiStream) !i32 {
        self.alignToByte();
        return self.reader().takeInt(i32, .big);
    }

    pub fn readS8be(self: *KaitaiStream) !i64 {
        self.alignToByte();
        return self.reader().takeInt(i64, .big);
    }

    //#endregion

    //#region Little-endian

    pub fn readS2le(self: *KaitaiStream) !i16 {
        self.alignToByte();
        return self.reader().takeInt(i16, .little);
    }

    pub fn readS4le(self: *KaitaiStream) !i32 {
        self.alignToByte();
        return self.reader().takeInt(i32, .little);
    }

    pub fn readS8le(self: *KaitaiStream) !i64 {
        self.alignToByte();
        return self.reader().takeInt(i64, .little);
    }

    //#endregion

    //#endregion

    //#region Unsigned

    pub fn readU1(self: *KaitaiStream) !u8 {
        self.alignToByte();
        return self.reader().takeByte();
    }

    //#region Big-endian

    pub fn readU2be(self: *KaitaiStream) !u16 {
        self.alignToByte();
        return self.reader().takeInt(u16, .big);
    }

    pub fn readU4be(self: *KaitaiStream) !u32 {
        self.alignToByte();
        return self.reader().takeInt(u32, .big);
    }

    pub fn readU8be(self: *KaitaiStream) !u64 {
        self.alignToByte();
        return self.reader().takeInt(u64, .big);
    }

    //#endregion

    //#region Little-endian

    pub fn readU2le(self: *KaitaiStream) !u16 {
        self.alignToByte();
        return self.reader().takeInt(u16, .little);
    }

    pub fn readU4le(self: *KaitaiStream) !u32 {
        self.alignToByte();
        return self.reader().takeInt(u32, .little);
    }

    pub fn readU8le(self: *KaitaiStream) !u64 {
        self.alignToByte();
        return self.reader().takeInt(u64, .little);
    }

    //#endregion

    //#endregion

    //#endregion

    //#region Floating point types

    //#region Big-endian

    pub fn readF4be(self: *KaitaiStream) !f32 {
        self.alignToByte();
        return @bitCast(try self.readU4be());
    }

    pub fn readF8be(self: *KaitaiStream) !f64 {
        self.alignToByte();
        return @bitCast(try self.readU8be());
    }

    //#endregion

    //#region Little-endian

    pub fn readF4le(self: *KaitaiStream) !f32 {
        self.alignToByte();
        return @bitCast(try self.readU4le());
    }

    pub fn readF8le(self: *KaitaiStream) !f64 {
        self.alignToByte();
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
        self.alignToByte();
        return self.reader().readAlloc(allocator, len);
    }

    pub fn readBytesFull(self: *KaitaiStream, allocator: Allocator) error{ ReadFailed, OutOfMemory }![]u8 {
        self.alignToByte();
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
        self.alignToByte();
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

    pub fn readBytesTermMulti(
        self: *KaitaiStream,
        allocator: Allocator,
        term: []const u8,
        include_term: bool,
        consume_term: bool,
        eos_error: bool,
    ) error{ ReadFailed, EndOfStream, OutOfMemory }![]u8 {
        self.alignToByte();
        const unit_size = term.len;
        var result: std.ArrayList(u8) = .empty;
        defer result.deinit(allocator);
        var c = try allocator.alloc(u8, unit_size);
        defer allocator.free(c);
        const r = self.reader();
        while (true) {
            const n = try r.readSliceShort(c);
            if (n < unit_size) {
                if (eos_error) {
                    return error.EndOfStream;
                }
                try result.appendSlice(allocator, c[0..n]);
                break;
            }
            if (std.mem.eql(u8, c, term)) {
                if (include_term) {
                    try result.appendSlice(allocator, c);
                } else if (!consume_term) {
                    // We deliberately ignore the possibility of combining `include: true` with
                    // `consume: false` because it doesn't make sense and will be rejected by the
                    // compiler in a future version of Kaitai Struct.
                    self.seek(self.pos() - unit_size) catch return error.ReadFailed;
                }
                break;
            }
            try result.appendSlice(allocator, c);
        }
        return result.toOwnedSlice(allocator);
    }

    pub fn bytesStripRight(bytes: []const u8, pad_byte: u8) []const u8 {
        return std.mem.trimEnd(u8, bytes, &.{pad_byte});
    }

    pub fn bytesTerminate(bytes: []const u8, term: u8, include_term: bool) []const u8 {
        if (std.mem.indexOfScalar(u8, bytes, term)) |term_index| {
            const new_len = term_index + @as(usize, if (include_term) 1 else 0);
            return bytes[0..new_len];
        }
        return bytes;
    }

    pub fn bytesTerminateMulti(bytes: []const u8, term: []const u8, include_term: bool) []const u8 {
        const unit_size = term.len;
        if (unit_size > bytes.len) {
            return bytes;
        }
        var i: usize = 0;
        const end = bytes.len - unit_size;
        while (i <= end) : (i += unit_size) {
            if (std.mem.eql(u8, bytes[i..][0..unit_size], term)) {
                return bytes[0 .. i + (if (include_term) unit_size else 0)];
            }
        }
        return bytes;
    }

    pub fn bytesToStr(allocator: Allocator, bytes: []const u8, comptime encoding: []const u8) error{ IllegalSequence, OutOfMemory }![]u8 {
        if (comptime std.mem.eql(u8, encoding, "ASCII")) {
            for (bytes) |c| {
                if (!std.ascii.isAscii(c)) {
                    return error.IllegalSequence;
                }
            }
            return allocator.dupe(u8, bytes);
        }
        if (comptime std.mem.eql(u8, encoding, "UTF-8")) {
            if (!std.unicode.utf8ValidateSlice(bytes)) {
                return error.IllegalSequence;
            }
            return allocator.dupe(u8, bytes);
        }
        const isUtf16Le = comptime std.mem.eql(u8, encoding, "UTF-16LE");
        const isUtf16Be = comptime std.mem.eql(u8, encoding, "UTF-16BE");
        if (comptime isUtf16Le or isUtf16Be) {
            const endian: std.builtin.Endian = comptime if (isUtf16Le) .little else .big;
            // UTF-16 uses 16-bit (2-byte) code units, so the input slice of bytes must have an even
            // length.
            if (bytes.len % 2 != 0) {
                return error.IllegalSequence;
            }
            var bytes_reader = Reader.fixed(bytes);
            const utf16 = bytes_reader.readSliceEndianAlloc(allocator, u16, @divExact(bytes.len, 2), endian) catch |err| {
                switch (err) {
                    // We read from an in-memory slice of bytes that is known to have an even
                    // length, so these errors should never occur.
                    error.ReadFailed, error.EndOfStream => unreachable,
                    else => |e| return e,
                }
            };
            defer allocator.free(utf16);
            return std.unicode.utf16LeToUtf8Alloc(allocator, utf16) catch |err| switch (err) {
                error.DanglingSurrogateHalf => error.IllegalSequence,
                error.ExpectedSecondSurrogateHalf => error.IllegalSequence,
                error.UnexpectedSecondSurrogateHalf => error.IllegalSequence,
                else => |e| e,
            };
        }
        @compileError("unsupported encoding '" ++ encoding ++ "'");
    }

    //#endregion

    //#region Byte array processing

    pub fn processXorOne(allocator: Allocator, data: []const u8, key: u8) Allocator.Error![]u8 {
        var result = try allocator.alloc(u8, data.len);
        for (data, 0..) |v, i| {
            result[i] = v ^ key;
        }
        return result;
    }

    pub fn processXorMany(allocator: Allocator, data: []const u8, key: []const u8) Allocator.Error![]u8 {
        if (key.len == 0) {
            return allocator.dupe(u8, data);
        }
        var result = try allocator.alloc(u8, data.len);
        var ki: usize = 0;
        for (data, 0..) |v, i| {
            result[i] = v ^ key[ki];
            ki += 1;
            if (ki >= key.len) {
                ki = 0;
            }
        }
        return result;
    }

    pub fn processRotateLeft(allocator: Allocator, data: []const u8, amount: i32) Allocator.Error![]u8 {
        var result = try allocator.alloc(u8, data.len);
        for (data, 0..) |v, i| {
            result[i] = std.math.rotl(u8, v, amount);
        }
        return result;
    }

    pub fn processZlib(allocator: Allocator, data: []const u8) error{ ReadFailed, OutOfMemory }![]u8 {
        var data_reader = Reader.fixed(data);
        var decompress: std.compress.flate.Decompress = .init(&data_reader, .zlib, &.{});
        const decompress_reader = &decompress.reader;

        var allocating_writer = std.Io.Writer.Allocating.init(allocator);
        defer allocating_writer.deinit();
        const writer = &allocating_writer.writer;

        _ = decompress_reader.streamRemaining(writer) catch |err| {
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

test "readBytesTerm - `include: true` (!), `consume: true`, `eos-error: false` (!), but terminator is not present" {
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

test "readBytesTermMulti - empty terminator" {
    var _io = KaitaiStream.fromBytes(&.{ 1, 2 });
    const allocator = std.testing.allocator;
    const bytes = try _io.readBytesTermMulti(allocator, &.{}, true, true, true);
    defer allocator.free(bytes);
    try testing.expectEqualSlices(u8, &.{}, bytes);
}

test "readBytesTermMulti - `include: false`, `consume: true`, `eos-error: true` (default)" {
    var _io = KaitaiStream.fromBytes(&.{ 1, 0, 0, 2, 0, 0, 3, 3 });
    const allocator = std.testing.allocator;
    const bytes = try _io.readBytesTermMulti(allocator, &.{ 0, 0 }, false, true, true);
    defer allocator.free(bytes);
    try testing.expectEqualSlices(u8, &.{ 1, 0, 0, 2 }, bytes);
    try testing.expectEqual(6, _io.pos());
}

test "readBytesTermMulti - `include: false`, `consume: false` (!), `eos-error: true`" {
    var _io = KaitaiStream.fromBytes(&.{ 1, 0, 0, 2, 0, 0, 3, 3 });
    const allocator = std.testing.allocator;
    const bytes = try _io.readBytesTermMulti(allocator, &.{ 0, 0 }, false, false, true);
    defer allocator.free(bytes);
    try testing.expectEqualSlices(u8, &.{ 1, 0, 0, 2 }, bytes);
    try testing.expectEqual(4, _io.pos());
}

test "readBytesTermMulti - `include: true` (!), `consume: true`, `eos-error: true`" {
    var _io = KaitaiStream.fromBytes(&.{ 1, 0, 0, 2, 0, 0, 3, 3 });
    const allocator = std.testing.allocator;
    const bytes = try _io.readBytesTermMulti(allocator, &.{ 0, 0 }, true, true, true);
    defer allocator.free(bytes);
    try testing.expectEqualSlices(u8, &.{ 1, 0, 0, 2, 0, 0 }, bytes);
    try testing.expectEqual(6, _io.pos());
}

test "readBytesTermMulti - `include: true` (!), `consume: true`, `eos-error: true`, but terminator is not present" {
    var _io = KaitaiStream.fromBytes(&.{ 1, 0, 0 });
    const allocator = std.testing.allocator;
    try testing.expectError(
        error.EndOfStream,
        _io.readBytesTermMulti(allocator, &.{ 0, 0 }, true, true, true),
    );
    try testing.expectEqual(3, _io.pos());
}

test "readBytesTermMulti - `include: true` (!), `consume: true`, `eos-error: false` (!), but terminator is not present" {
    var _io = KaitaiStream.fromBytes(&.{ 1, 0, 0 });
    const allocator = std.testing.allocator;
    const bytes = try _io.readBytesTermMulti(allocator, &.{ 0, 0 }, true, true, false);
    defer allocator.free(bytes);
    try testing.expectEqualSlices(u8, &.{ 1, 0, 0 }, bytes);
    try testing.expectEqual(3, _io.pos());
}

test "bytesStripRight - padding present" {
    const res = KaitaiStream.bytesStripRight(&.{ 1, 2, 1, 2, 2 }, 2);
    try testing.expectEqualSlices(u8, &.{ 1, 2, 1 }, res);
}

test "bytesStripRight - no padding" {
    const res = KaitaiStream.bytesStripRight(&.{ 1, 2, 1 }, 2);
    try testing.expectEqualSlices(u8, &.{ 1, 2, 1 }, res);
}

test "bytesTerminate - `include: false`" {
    const res = KaitaiStream.bytesTerminate(&.{ 1, 2, 3, 2 }, 2, false);
    try testing.expectEqualSlices(u8, &.{1}, res);
}

test "bytesTerminate - `include: true`" {
    const res = KaitaiStream.bytesTerminate(&.{ 1, 2, 3, 2 }, 2, true);
    try testing.expectEqualSlices(u8, &.{ 1, 2 }, res);
}

test "bytesTerminate - `include: false`, but terminator is not present" {
    const res = KaitaiStream.bytesTerminate(&.{ 1, 2, 3, 2 }, 0, false);
    try testing.expectEqualSlices(u8, &.{ 1, 2, 3, 2 }, res);
}

test "bytesTerminate - `include: true`, but terminator is not present" {
    const res = KaitaiStream.bytesTerminate(&.{ 1, 2, 3, 2 }, 0, true);
    try testing.expectEqualSlices(u8, &.{ 1, 2, 3, 2 }, res);
}

test "bytesTerminateMulti - empty terminator" {
    const res = KaitaiStream.bytesTerminateMulti(&.{}, &.{}, false);
    try testing.expectEqualSlices(u8, &.{}, res);
}

test "bytesTerminateMulti - terminator is longer than input bytes" {
    const res = KaitaiStream.bytesTerminateMulti(&.{0}, &.{ 0, 0 }, false);
    try testing.expectEqualSlices(u8, &.{0}, res);
}

test "bytesTerminateMulti - input length is not a multiple of terminator length" {
    const res = KaitaiStream.bytesTerminateMulti(&.{ 1, 0, 0 }, &.{ 0, 0 }, false);
    try testing.expectEqualSlices(u8, &.{ 1, 0, 0 }, res);
}

test "bytesTerminateMulti - `include: false`" {
    const res = KaitaiStream.bytesTerminateMulti(&.{ 1, 0, 0, 2, 0, 0, 3, 3 }, &.{ 0, 0 }, false);
    try testing.expectEqualSlices(u8, &.{ 1, 0, 0, 2 }, res);
}

test "bytesTerminateMulti - `include: true`" {
    const res = KaitaiStream.bytesTerminateMulti(&.{ 1, 0, 0, 2, 0, 0, 3, 3 }, &.{ 0, 0 }, true);
    try testing.expectEqualSlices(u8, &.{ 1, 0, 0, 2, 0, 0 }, res);
}

test "bytesToStr - empty ASCII" {
    const allocator = std.testing.allocator;
    const bytes: []const u8 = &.{};
    const str = try KaitaiStream.bytesToStr(allocator, bytes, "ASCII");
    defer allocator.free(str);
    try testing.expectEqualSlices(u8, bytes, str);
}

test "bytesToStr - empty UTF-8" {
    const allocator = std.testing.allocator;
    const bytes: []const u8 = &.{};
    const str = try KaitaiStream.bytesToStr(allocator, bytes, "UTF-8");
    defer allocator.free(str);
    try testing.expectEqualSlices(u8, bytes, str);
}

test "bytesToStr - empty UTF-16LE" {
    const allocator = std.testing.allocator;
    const bytes: []const u8 = &.{};
    const str = try KaitaiStream.bytesToStr(allocator, bytes, "UTF-16LE");
    defer allocator.free(str);
    try testing.expectEqualSlices(u8, bytes, str);
}

test "bytesToStr - empty UTF-16BE" {
    const allocator = std.testing.allocator;
    const bytes: []const u8 = &.{};
    const str = try KaitaiStream.bytesToStr(allocator, bytes, "UTF-16BE");
    defer allocator.free(str);
    try testing.expectEqualSlices(u8, bytes, str);
}

test "bytesToStr - valid ASCII" {
    const allocator = std.testing.allocator;
    const bytes: []const u8 = &.{ 0x00, 0x01, 0x20, 0x7e, 0x7f };
    const str = try KaitaiStream.bytesToStr(allocator, bytes, "ASCII");
    defer allocator.free(str);
    try testing.expectEqualSlices(u8, bytes, str);
}

test "bytesToStr - invalid ASCII (but valid UTF-8)" {
    const allocator = std.testing.allocator;
    const bytes: []const u8 = &.{ 0xc2, 0x80 };
    try testing.expectError(
        error.IllegalSequence,
        KaitaiStream.bytesToStr(allocator, bytes, "ASCII"),
    );
}

test "bytesToStr - valid UTF-8" {
    const allocator = std.testing.allocator;
    // Python 3.6+ code:
    //
    // ```python
    // for codepoint in (0x0000, 0x007F, 0x0080, 0x07FF, 0x0800, 0xFFFF, 0x10000, 0x10FFFF):
    //     print(', '.join(f"{b:#04x}" for b in chr(codepoint).encode('UTF-8')) + f", // U+{codepoint:04X}")
    // ```
    const bytes: []const u8 = &.{
        0x00, // U+0000
        0x7f, // U+007F
        0xc2, 0x80, // U+0080
        0xdf, 0xbf, // U+07FF
        0xe0, 0xa0, 0x80, // U+0800
        0xef, 0xbf, 0xbf, // U+FFFF
        0xf0, 0x90, 0x80, 0x80, // U+10000
        0xf4, 0x8f, 0xbf, 0xbf, // U+10FFFF
    };
    const str = try KaitaiStream.bytesToStr(allocator, bytes, "UTF-8");
    defer allocator.free(str);
    try testing.expectEqualStrings("\u{0000}\u{007F}\u{0080}\u{07FF}\u{0800}\u{FFFF}\u{10000}\u{10FFFF}", str);
}

test "bytesToStr - invalid UTF-8 (surrogate code point)" {
    const allocator = std.testing.allocator;
    // See https://en.wikipedia.org/wiki/UTF-8#Surrogates:
    //
    // > [...] the high and low surrogates used by UTF-16 (U+D800 through
    // > U+DFFF) are not legal Unicode values, and their UTF-8 encodings must be
    // > treated as an invalid byte sequence.
    //
    // Python 3.6+ code:
    //
    // ```python
    // print(', '.join(f"{b:#04x}" for b in '\uD800'.encode('UTF-8', errors='surrogatepass')))
    // ```
    const bytes: []const u8 = &.{ 0xed, 0xa0, 0x80 };
    try testing.expectError(
        error.IllegalSequence,
        KaitaiStream.bytesToStr(allocator, bytes, "UTF-8"),
    );
}

test "bytesToStr - valid UTF-16LE" {
    const allocator = std.testing.allocator;
    const bytes: []const u8 = &.{ 0x3d, 0xd8, 0x00, 0xde };
    const str = try KaitaiStream.bytesToStr(allocator, bytes, "UTF-16LE");
    defer allocator.free(str);
    try testing.expectEqualStrings("\u{1F600}", str);
}

test "bytesToStr - valid UTF-16BE" {
    const allocator = std.testing.allocator;
    const bytes: []const u8 = &.{ 0xd8, 0x3d, 0xde, 0x00 };
    const str = try KaitaiStream.bytesToStr(allocator, bytes, "UTF-16BE");
    defer allocator.free(str);
    try testing.expectEqualStrings("\u{1F600}", str);
}

test "bytesToStr - invalid UTF-16LE (odd length)" {
    const allocator = std.testing.allocator;
    const bytes: []const u8 = &.{ 0x3d, 0xd8, 0x00 };
    try testing.expectError(
        error.IllegalSequence,
        KaitaiStream.bytesToStr(allocator, bytes, "UTF-16LE"),
    );
}

test "bytesToStr - invalid UTF-16BE (odd length)" {
    const allocator = std.testing.allocator;
    const bytes: []const u8 = &.{ 0xd8, 0x3d, 0xde };
    try testing.expectError(
        error.IllegalSequence,
        KaitaiStream.bytesToStr(allocator, bytes, "UTF-16BE"),
    );
}

// Comment on the following "bytesToStr - invalid UTF-16*" tests:
//
// > UTF-16 disallows having high surrogate (any value in the range of 0xd800..0xdbff)
// > not followed by low surrogate (any value in the range of 0xdc00..0xdfff).

test "bytesToStr - invalid UTF-16LE (DanglingSurrogateHalf)" {
    const allocator = std.testing.allocator;
    // Python 3.6+ code:
    //
    // ```python
    // print(', '.join(f"{b:#04x}" for b in '\uD800'.encode('UTF-16LE', errors='surrogatepass')))
    // ```
    const bytes: []const u8 = &.{ 0x00, 0xd8 };
    try testing.expectError(
        error.IllegalSequence,
        KaitaiStream.bytesToStr(allocator, bytes, "UTF-16LE"),
    );
}

test "bytesToStr - invalid UTF-16BE (DanglingSurrogateHalf)" {
    const allocator = std.testing.allocator;
    // Python 3.6+ code:
    //
    // ```python
    // print(', '.join(f"{b:#04x}" for b in '\uD800'.encode('UTF-16BE', errors='surrogatepass')))
    // ```
    const bytes: []const u8 = &.{ 0xd8, 0x00 };
    try testing.expectError(
        error.IllegalSequence,
        KaitaiStream.bytesToStr(allocator, bytes, "UTF-16BE"),
    );
}

test "bytesToStr - invalid UTF-16LE (ExpectedSecondSurrogateHalf)" {
    const allocator = std.testing.allocator;
    // Python 3.6+ code:
    //
    // ```python
    // print(', '.join(f"{b:#04x}" for b in '\uD800\uD800'.encode('UTF-16LE', errors='surrogatepass')))
    // ```
    const bytes: []const u8 = &.{ 0x00, 0xd8, 0x00, 0xd8 };
    try testing.expectError(
        error.IllegalSequence,
        KaitaiStream.bytesToStr(allocator, bytes, "UTF-16LE"),
    );
}

test "bytesToStr - invalid UTF-16BE (ExpectedSecondSurrogateHalf)" {
    const allocator = std.testing.allocator;
    // Python 3.6+ code:
    //
    // ```python
    // print(', '.join(f"{b:#04x}" for b in '\uD800\uD800'.encode('UTF-16BE', errors='surrogatepass')))
    // ```
    const bytes: []const u8 = &.{ 0xd8, 0x00, 0xd8, 0x00 };
    try testing.expectError(
        error.IllegalSequence,
        KaitaiStream.bytesToStr(allocator, bytes, "UTF-16BE"),
    );
}

test "bytesToStr - invalid UTF-16LE (UnexpectedSecondSurrogateHalf)" {
    const allocator = std.testing.allocator;
    // Python 3.6+ code:
    //
    // ```python
    // print(', '.join(f"{b:#04x}" for b in '\uDC00'.encode('UTF-16LE', errors='surrogatepass')))
    // ```
    const bytes: []const u8 = &.{ 0x00, 0xdc };
    try testing.expectError(
        error.IllegalSequence,
        KaitaiStream.bytesToStr(allocator, bytes, "UTF-16LE"),
    );
}

test "bytesToStr - invalid UTF-16BE (UnexpectedSecondSurrogateHalf)" {
    const allocator = std.testing.allocator;
    // Python 3.6+ code:
    //
    // ```python
    // print(', '.join(f"{b:#04x}" for b in '\uDC00'.encode('UTF-16BE', errors='surrogatepass')))
    // ```
    const bytes: []const u8 = &.{ 0xdc, 0x00 };
    try testing.expectError(
        error.IllegalSequence,
        KaitaiStream.bytesToStr(allocator, bytes, "UTF-16BE"),
    );
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

test "processXorOne" {
    const allocator = std.testing.allocator;
    const bytes = try KaitaiStream.processXorOne(allocator, &.{ 0x1a, 0xd0 }, 0x11);
    defer allocator.free(bytes);
    try testing.expectEqualSlices(u8, &.{ 0x0b, 0xc1 }, bytes);
}

test "processXorMany - empty key" {
    const allocator = std.testing.allocator;
    const bytes = try KaitaiStream.processXorMany(allocator, &.{ 0x1a, 0xd0 }, &.{});
    defer allocator.free(bytes);
    try testing.expectEqualSlices(u8, &.{ 0x1a, 0xd0 }, bytes);
}

test "processXorMany" {
    const allocator = std.testing.allocator;
    const bytes = try KaitaiStream.processXorMany(allocator, &.{ 0x1a, 0xd8, 0x52, 0xfd, 0x81 }, &.{ 0xff, 0x00 });
    defer allocator.free(bytes);
    try testing.expectEqualSlices(u8, &.{ 0xe5, 0xd8, 0xad, 0xfd, 0x7e }, bytes);
}

test "processRotateLeft" {
    const allocator = std.testing.allocator;
    const bytes = try KaitaiStream.processRotateLeft(allocator, &.{ 0b0111_0110, 0b1101_0000 }, 2);
    defer allocator.free(bytes);
    try testing.expectEqualSlices(u8, &.{ 0b1101_1001, 0b0100_0011 }, bytes);
}

// Ported from C++: https://github.com/kaitai-io/kaitai_struct_cpp_stl_runtime/blob/c7009877d4b0ca804442e796c996eb4501f3203d/tests/unittest.cpp#L263-L278
test "processZlib - success" {
    const allocator = std.testing.allocator;
    const bytes = try KaitaiStream.processZlib(allocator, &.{ 0x78, 0x9c, 0xf3, 0xc8, 0x04, 0x00, 0x00, 0xfb, 0x00, 0xb2 });
    defer allocator.free(bytes);
    try testing.expectEqualSlices(u8, "Hi", bytes);
}

// Ported from C++: https://github.com/kaitai-io/kaitai_struct_cpp_stl_runtime/blob/c7009877d4b0ca804442e796c996eb4501f3203d/tests/unittest.cpp#L303-L325
test "processZlib - Z_BUF_ERROR" {
    const allocator = std.testing.allocator;
    try testing.expectError(
        error.ReadFailed,
        KaitaiStream.processZlib(allocator, &.{ 0x78, 0x9c, 0xf3, 0xc8, 0x04, 0x00, 0x00, 0xfb, 0x00 }),
    );
}
