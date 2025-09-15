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
        return switch (self.reader_impl) {
            .file => |file_reader| file_reader.seekTo(new_pos),
            .bytes => |*bytes_reader| bytes_reader.seek = new_pos,
        };
    }

    pub fn pos(self: *KaitaiStream) u64 {
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
    var ks_io = KaitaiStream.fromFileReader(&reader);
    try testing.expectEqual(3, ks_io.size());
    try testing.expectEqual(0, ks_io.pos());
    try testing.expectEqual(0xc2, ks_io.readU1());
    try testing.expectEqual(1, ks_io.pos());
    try testing.expectEqual(-0x5d, ks_io.readS1());
    try testing.expectEqual(false, ks_io.isEof());
    try testing.expectEqual(2, ks_io.pos());
    try testing.expectEqual(0x0a, ks_io.readS1());
    try testing.expectEqual(true, ks_io.isEof());
    try testing.expectEqual(3, ks_io.pos());
    try testing.expectError(error.EndOfStream, ks_io.readU1());
    try testing.expectError(error.EndOfStream, ks_io.readS1());
    try ks_io.seek(0);
    try testing.expectEqual(0, ks_io.pos());
    try testing.expectEqual(0xa3c2, ks_io.readU2le());
    try testing.expectError(error.EndOfStream, ks_io.readS2be());
    try testing.expectEqual(2, ks_io.pos());
}

test "isEof on reader failure" {
    const file = try std.fs.cwd().openFile("test.bin", .{});
    var buffer: [1]u8 = undefined;
    var reader = file.reader(&buffer);
    var ks_io = KaitaiStream.fromFileReader(&reader);
    try testing.expectEqual(false, ks_io.isEof());
    try testing.expectEqual(0xc2, ks_io.readU1());
    file.close();
    try testing.expectError(error.ReadFailed, ks_io.isEof());
}

test "readBytes" {
    const file = try std.fs.cwd().openFile("test.bin", .{});
    defer file.close();
    var buffer: [4096]u8 = undefined;
    var reader = file.reader(&buffer);
    var ks_io = KaitaiStream.fromFileReader(&reader);
    const allocator = std.testing.allocator;
    try testing.expectEqual(0xc2, ks_io.readU1());
    const bytes = try ks_io.readBytes(allocator, 2);
    defer allocator.free(bytes);
    try testing.expectEqualStrings("\xa3\x0a", bytes);
}

test "readBytesFull" {
    const file = try std.fs.cwd().openFile("test.bin", .{});
    defer file.close();
    var buffer: [4096]u8 = undefined;
    var reader = file.reader(&buffer);
    var ks_io = KaitaiStream.fromFileReader(&reader);
    const allocator = std.testing.allocator;
    try testing.expectEqual(0xc2, ks_io.readU1());
    const bytes = try ks_io.readBytesFull(allocator);
    defer allocator.free(bytes);
    try testing.expectEqualStrings("\xa3\x0a", bytes);
}

test "readBytesTerm - `include: false`, `consume: true`, `eos-error: true` (default)" {
    const file = try std.fs.cwd().openFile("test.bin", .{});
    defer file.close();
    var buffer: [4096]u8 = undefined;
    var reader = file.reader(&buffer);
    var ks_io = KaitaiStream.fromFileReader(&reader);
    const allocator = std.testing.allocator;
    const bytes = try ks_io.readBytesTerm(allocator, '\x0a', false, true, true);
    defer allocator.free(bytes);
    try testing.expectEqualStrings("\xc2\xa3", bytes);
    try testing.expectEqual(3, ks_io.pos());
}

test "readBytesTerm - `include: false`, `consume: false` (!), `eos-error: true`" {
    const file = try std.fs.cwd().openFile("test.bin", .{});
    defer file.close();
    var buffer: [4096]u8 = undefined;
    var reader = file.reader(&buffer);
    var ks_io = KaitaiStream.fromFileReader(&reader);
    const allocator = std.testing.allocator;
    const bytes = try ks_io.readBytesTerm(allocator, '\x0a', false, false, true);
    defer allocator.free(bytes);
    try testing.expectEqualStrings("\xc2\xa3", bytes);
    try testing.expectEqual(2, ks_io.pos());
}

test "readBytesTerm - `include: true` (!), `consume: true`, `eos-error: true`" {
    const file = try std.fs.cwd().openFile("test.bin", .{});
    defer file.close();
    var buffer: [4096]u8 = undefined;
    var reader = file.reader(&buffer);
    var ks_io = KaitaiStream.fromFileReader(&reader);
    const allocator = std.testing.allocator;
    const bytes = try ks_io.readBytesTerm(allocator, '\x0a', true, false, true);
    defer allocator.free(bytes);
    try testing.expectEqualStrings("\xc2\xa3\x0a", bytes);
    try testing.expectEqual(3, ks_io.pos());
}

test "readBytesTerm - `include: true` (!), `consume: true`, `eos-error: true`, but terminator is not present" {
    const file = try std.fs.cwd().openFile("test.bin", .{});
    defer file.close();
    var buffer: [4096]u8 = undefined;
    var reader = file.reader(&buffer);
    var ks_io = KaitaiStream.fromFileReader(&reader);
    const allocator = std.testing.allocator;
    try testing.expectError(error.EndOfStream, ks_io.readBytesTerm(allocator, '\x00', true, true, true));
    try testing.expectEqual(3, ks_io.pos());
}

test "readBytesTerm - `include: true` (!), `consume: true`, `eos-error: false` (!)" {
    const file = try std.fs.cwd().openFile("test.bin", .{});
    defer file.close();
    var buffer: [4096]u8 = undefined;
    var reader = file.reader(&buffer);
    var ks_io = KaitaiStream.fromFileReader(&reader);
    const allocator = std.testing.allocator;
    const bytes = try ks_io.readBytesTerm(allocator, '\x00', true, true, false);
    defer allocator.free(bytes);
    try testing.expectEqualStrings("\xc2\xa3\x0a", bytes);
    try testing.expectEqual(3, ks_io.pos());
}

test "readF4be" {
    var ks_io = KaitaiStream.fromBytes(&.{ 0x3f, 0xc0, 0x00, 0x00 });
    try testing.expectEqual(1.5, ks_io.readF4be());
}

test "readF4le" {
    var ks_io = KaitaiStream.fromBytes(&.{ 0x00, 0x00, 0xc0, 0x3f });
    try testing.expectEqual(1.5, ks_io.readF4le());
}

test "readF8be" {
    var ks_io = KaitaiStream.fromBytes(&.{ 0x3f, 0xf8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 });
    try testing.expectEqual(1.5, ks_io.readF8be());
}

test "readF8le" {
    var ks_io = KaitaiStream.fromBytes(&.{ 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xf8, 0x3f });
    try testing.expectEqual(1.5, ks_io.readF8le());
}
