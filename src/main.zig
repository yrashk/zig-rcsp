//! Reference-counted Shared Pointer
//!
//! Supports both atomic and non-atomic counters.
//!
//! Here's an example of its usage:
//!
//! ```
//! const AtomicU128Counter = RcSharedPointer(u128, Atomic);
//! var counter = AtomicU128Counter(100, std.heap.page_allocator);
//! defer counter.deinit();
//! var counter1 = counter.strongClone();
//! _ = counter1.ptr();
//! defer counter1.deinit();
//! ```

const std = @import("std");
const builtin = @import("builtin");
const testing = std.testing;

/// Atomic counter
///
/// When used with single threaded builds, will defer to `NonAtomic`
pub const Atomic = if (builtin.single_threaded) NonAtomic else struct {
    const T = usize;
    pub const MAX = std.math.maxInt(T);
    pub const MIN = std.math.minInt(T);

    /// Saturating increment
    inline fn increment(ptr: *T) T {
        const val = @atomicLoad(usize, ptr, .Acquire);
        const incr: T = if (val == MAX) 0 else 1;
        return @atomicRmw(T, ptr, .Add, incr, .Release);
    }

    /// Bottom-clamped saturating increment
    /// (if counter is zero, it will not be incremented)
    inline fn clampedIncrement(ptr: *T) T {
        const val = @atomicLoad(usize, ptr, .Acquire);
        var incr: T = if (val == MAX) 0 else 1;
        if (val == MIN) {
            incr = 0;
        }
        return @atomicRmw(T, ptr, .Add, incr, .Release);
    }

    /// Saturating decrement
    inline fn decrement(ptr: *T) T {
        const val = @atomicLoad(usize, ptr, .Acquire);
        const decr: T = if (val == MIN) 0 else 1;
        return @atomicRmw(T, ptr, .Sub, decr, .Release);
    }

    /// Load counter value
    inline fn load(ptr: *T) T {
        return @atomicLoad(T, ptr, .SeqCst);
    }
};

test "atomic increment" {
    var val: usize = 0;
    testing.expectEqual(@intCast(usize, 0), Atomic.increment(&val));
    testing.expectEqual(@intCast(usize, 1), Atomic.load(&val));
}

test "clamped atomic increment" {
    var val: usize = 0;
    testing.expectEqual(@intCast(usize, 0), Atomic.clampedIncrement(&val));
    testing.expectEqual(@intCast(usize, 0), Atomic.load(&val));
}

test "saturating atomic increment from max usize" {
    var val: usize = std.math.maxInt(usize);
    testing.expectEqual(@intCast(usize, std.math.maxInt(usize)), Atomic.increment(&val));
    testing.expectEqual(@intCast(usize, std.math.maxInt(usize)), Atomic.load(&val));
}

fn increment100(val: *usize) void {
    var i: usize = 0;
    while (i < 100) {
        // this is to ensure the thread doesn't finish too early
        std.time.sleep(10 * std.time.millisecond);
        _ = Atomic.increment(val);
        i += 1;
    }
}

fn decrement100(val: *usize) void {
    var i: usize = 0;
    while (i < 100) {
        // this is to ensure the thread doesn't finish too early
        std.time.sleep(10 * std.time.millisecond);
        _ = Atomic.decrement(val);
        i += 1;
    }
}

test "concurrent atomic increments & decrements" {
    var val: usize = 0;
    const t1 = try std.Thread.spawn(&val, increment100);
    const t2 = try std.Thread.spawn(&val, increment100);
    t1.wait();
    t2.wait();
    testing.expectEqual(@intCast(usize, 200), Atomic.load(&val));
    const t3 = try std.Thread.spawn(&val, decrement100);
    const t4 = try std.Thread.spawn(&val, decrement100);
    t3.wait();
    t4.wait();
    testing.expectEqual(@intCast(usize, 0), Atomic.load(&val));
}

test "saturating concurrent atomic increments" {
    var val: usize = std.math.maxInt(usize) - 100;
    const t1 = try std.Thread.spawn(&val, increment100);
    const t2 = try std.Thread.spawn(&val, increment100);
    t1.wait();
    t2.wait();
    testing.expectEqual(@intCast(usize, std.math.maxInt(usize)), Atomic.load(&val));
}

test "atomic decrement" {
    var val: usize = 1;
    testing.expectEqual(Atomic.decrement(&val), 1);
    testing.expectEqual(Atomic.load(&val), 0);
}

test "saturating atomic decrement from 0" {
    var val: usize = 0;
    testing.expectEqual(Atomic.decrement(&val), 0);
    testing.expectEqual(Atomic.load(&val), 0);
}

test "saturating concurrent atomic decrements" {
    var val: usize = std.math.minInt(usize) + 100;
    const t1 = try std.Thread.spawn(&val, decrement100);
    const t2 = try std.Thread.spawn(&val, decrement100);
    t1.wait();
    t2.wait();
    testing.expectEqual(@intCast(usize, std.math.minInt(usize)), Atomic.load(&val));
}

/// Non-atomic counter
pub const NonAtomic = struct {
    const T = usize;
    pub const MAX = std.math.maxInt(T);
    pub const MIN = std.math.minInt(T);

    /// Saturating increment
    inline fn increment(ptr: *T) T {
        const val = ptr.*;
        if (@addWithOverflow(T, val, 1, ptr)) {
            ptr.* = MAX;
        }
        return val;
    }
    /// Bottom-clamped saturating increment
    /// (if counter is zero, it will not be incremented)
    inline fn clampedIncrement(ptr: *T) T {
        const val = ptr.*;
        if (val == MIN) {
            return MIN;
        }
        if (@addWithOverflow(T, val, 1, ptr)) {
            ptr.* = MAX;
        }
        return val;
    }

    /// Saturating decrement
    inline fn decrement(ptr: *T) T {
        const val = ptr.*;
        if (@subWithOverflow(T, val, 1, ptr)) {
            ptr.* = MIN;
        }
        return val;
    }

    /// Load counter value
    inline fn load(ptr: *T) T {
        return ptr.*;
    }
};

test "non-atomic increment" {
    var val: usize = 0;
    testing.expectEqual(NonAtomic.increment(&val), 0);
    testing.expectEqual(NonAtomic.load(&val), 1);
}

test "clamped non-atomic increment" {
    var val: usize = 0;
    testing.expectEqual(@intCast(usize, 0), NonAtomic.clampedIncrement(&val));
    testing.expectEqual(@intCast(usize, 0), NonAtomic.load(&val));
}

test "non-atomic increment from max usize" {
    var val: usize = std.math.maxInt(usize);
    testing.expectEqual(NonAtomic.increment(&val), std.math.maxInt(usize));
    testing.expectEqual(NonAtomic.load(&val), std.math.maxInt(usize));
}

test "non-atomic decrement" {
    var val: usize = 1;
    testing.expectEqual(NonAtomic.decrement(&val), 1);
    testing.expectEqual(NonAtomic.load(&val), 0);
}

test "non-atomic decrement from 0" {
    var val: usize = 0;
    testing.expectEqual(NonAtomic.decrement(&val), 0);
    testing.expectEqual(NonAtomic.load(&val), 0);
}

/// Reference-counted shared pointer
///
/// Shared pointer with `Atomic` operations should not use
/// the same clone in more than one thread simultaneously.
///
/// Shared pointer with `NonAtomic` operations should not use
/// any clones outside of a single thread simultaneously.
///
/// TODO: RcSharedPointer does not properly handle the sitation
/// when either strong or weak counter saturates at the maximum
/// value of `usize`. Currently, it'll panic in this situation.
pub fn RcSharedPointer(comptime T: type, Ops: type) type {
    const Inner = struct {
        val: T,
        strong_ctr: usize = 1,
        weak_ctr: usize = 0,
        allocator: *std.mem.Allocator,
    };
    return struct {
        const Strong = @This();
        const Weak = struct {
            inner: ?*Inner,
            pub const Type = T;

            // There's seemingly a bug in Zig that messes with
            // creation of RcSharedPointer if the constant below
            // is declared as `Self` (and is later reused in the
            // outer scope)
            // TODO: change this to `Self` when (if) this behaviour
            // will be changed
            const SelfWeak = @This();

            /// Create a strong clone
            ///
            /// Might return zero if no other strong clones are present
            /// (which indicates that the value has been deinitialized,
            /// but not deallocated)
            ///
            /// Instead of upgrading a shared pointer or its
            /// strong clone to a weak one, creation of a weak
            /// clone is used to avoid any potential race conditions
            /// caused by momentarily inconsistent strong and weak
            /// counters (where the total number of counters might
            /// be incorrect during downgrade or upgrade operations)
            pub fn strongClone(self: SelfWeak) ?Strong {
                // the reason we're doing a clamped increment here is
                // because if the counter is already zero, then the value
                // has been deinitialized,..
                const prev = Ops.clampedIncrement(&self.inner.?.*.strong_ctr);
                if (prev == Ops.MAX) {
                    @panic("strong counter has been saturated");
                }
                if (prev == Ops.MIN) {
                    // ..so, we'll not be able to make a strong clone anymore
                    return null;
                }
                return Strong{ .inner = self.inner };
            }

            /// Create a weak clone
            pub fn weakClone(self: SelfWeak) SelfWeak {
                const prev = Ops.increment(&self.inner.?.*.weak_ctr);
                if (prev == Ops.MAX) {
                    @panic("weak counter has been saturated");
                }
                return SelfWeak{ .inner = self.inner };
            }

            /// Number of strong clones
            pub inline fn strongCount(self: SelfWeak) usize {
                return Ops.load(&self.inner.?.*.strong_ctr);
            }

            /// Number of weak clones
            pub inline fn weakCount(self: SelfWeak) usize {
                return Ops.load(&self.inner.?.*.weak_ctr);
            }

            /// Deinitialize weak clone
            ///
            /// Will never deinitialize the value but will
            /// deallocate it if it is the last clone (both strong and weak)
            pub fn deinit(self: *SelfWeak) void {
                const cw_ = Ops.decrement(&self.inner.?.*.weak_ctr);
                const c = Ops.load(&self.inner.?.*.strong_ctr);
                const cw = Ops.load(&self.inner.?.*.weak_ctr);
                var p = self.inner.?;
                // incapacitate self (useful methods will now panic)
                self.inner = null;
                // if weak counter was not saturated and there are
                // no strong clones,
                if (c == 0 and cw == 0 and cw_ > 0) {
                    // then we can deallocate
                    p.*.allocator.destroy(p);
                }
            }
        };

        inner: ?*Inner,
        pub const Type = T;

        const Self = @This();

        /// Initialize the counter with a value
        ///
        /// Allocates memory to hold the value and the counter
        pub fn init(val: T, allocator: *std.mem.Allocator) !Self {
            var allocated = try allocator.create(Inner);
            allocated.* = Inner{
                .val = val,
                .allocator = allocator,
            };
            return Self{ .inner = allocated };
        }

        /// Create a strong clone
        pub fn strongClone(self: *const Self) Self {
            // the reason we're not doing a clampedIncrement here (as we do in `Weak`)
            // is that the presence of non-null `self.inner` is already a guarantee that
            // there's at least one strong clone present (`self`)
            const prev = Ops.increment(&self.inner.?.*.strong_ctr);
            if (prev == Ops.MAX) {
                @panic("strong counter has been saturated");
            }
            return Self{ .inner = self.inner };
        }

        /// Create a weak clone
        ///
        /// Instead of downgrading a shared pointer or its
        /// strong clone to a weak one, creation of a weak
        /// clone is used to avoid any potential race conditions
        /// caused by momentarily inconsistent strong and weak
        /// counters (where the total number of counters might
        /// be incorrect during downgrade or upgrade operations)
        pub fn weakClone(self: Self) Weak {
            const prev = Ops.increment(&self.inner.?.*.weak_ctr);
            if (prev == Ops.MAX) {
                @panic("weak counter has been saturated");
            }
            return Weak{ .inner = self.inner };
        }

        /// Number of strong clones
        pub inline fn strongCount(self: Self) usize {
            return Ops.load(&self.inner.?.*.strong_ctr);
        }

        /// Number of weak clones
        pub inline fn weakCount(self: Self) usize {
            return Ops.load(&self.inner.?.*.weak_ctr);
        }

        /// Const pointer to the value
        ///
        /// As the pointer is constant, if mutability
        /// is desired, use of `std.Mutex` and `unsafePtr`
        /// is recommended
        pub fn ptr(self: Self) *const T {
            return &self.inner.?.*.val;
        }

        /// Unsafe (mutable) pointer to the value
        /// Normally it is recommended to use `std.Mutex`
        /// for concurrent access:
        ///
        /// ```
        /// const T = struct { value: u128, ptr: std.Mutex = std.Mutex.init() };
        /// var counter = RcSharedPointer(T, Atomic).init(T{ .value = 10 });
        /// defer counter.deinit();
        /// var ptr = counter.unsafePtr();
        /// {
        ///     const lock = ptr.*.mutex.aquire();
        ///     defer lock.release();
        ///     ptr.*.value = 100;
        /// }
        /// ```
        pub fn unsafePtr(self: Self) *T {
            return &self.inner.?.*.val;
        }

        /// Deinitialize the shared pointer
        ///
        /// Will deallocate its initial allocation
        pub fn deinit(self: *Self) void {
            self.deinitWithCallback(?void, null, null);
        }

        /// Deinitialize the shared pointer with a callback
        ///
        /// Will first deinitialize the value using the callback
        /// (if there are no other strong clones present) and then
        /// deallocate its initial allocation (if there are no weak
        /// clones present)
        pub fn deinitWithCallback(self: *Self, comptime C: type, context: C, deinitializer: ?fn (*T, C) void) void {
            const c_ = Ops.decrement(&self.inner.?.*.strong_ctr);
            const c = Ops.load(&self.inner.?.*.strong_ctr);
            const cw = Ops.load(&self.inner.?.*.weak_ctr);
            var p = self.inner.?;
            // incapacitate self (useful methods will now panic)
            self.inner = null;
            // if the strong counter was not saturated and
            // the new effective count is zero, then we're...
            if (c == 0 and c_ > 0) {
                // ...ready to deinitialize the value
                if (deinitializer) |deinit_fn| {
                    deinit_fn(&p.*.val, context);
                }
                // also, if there are no outstanding weak counters,
                if (cw == 0) {
                    // then deallocate
                    p.*.allocator.destroy(p);
                }
            }
        }
    };
}

test "initializing a shared pointer with a value" {
    var v = try RcSharedPointer(u128, NonAtomic).init(10, std.heap.page_allocator);
    defer v.deinit();
    testing.expectEqual(v.ptr().*, 10);
}

test "unsafely mutating shared pointer's value" {
    var v = try RcSharedPointer(u128, NonAtomic).init(10, std.heap.page_allocator);
    defer v.deinit();
    const ptr = v.unsafePtr();
    ptr.* = 20;
    testing.expectEqual(v.ptr().*, 20);
}

test "safely mutating shared pointer's value" {
    const MU128 = struct {
        value: u128,
        mutex: std.Mutex = std.Mutex.init(),
    };
    var mutex = MU128{ .value = 10 };
    var v = try RcSharedPointer(MU128, NonAtomic).init(mutex, std.heap.page_allocator);
    defer v.deinit();
    const ptr = v.unsafePtr();
    {
        const lock = ptr.*.mutex.acquire();
        defer lock.release();
        ptr.*.value = 20;
    }
}

fn deinit_copy(val: *u128, ctx: *u128) void {
    ctx.* = val.*;
}
test "deinitializing a shared pointer with a callback" {
    var v = try RcSharedPointer(u128, NonAtomic).init(10, std.heap.page_allocator);
    var v1: u128 = 0;
    v.deinitWithCallback(*u128, &v1, deinit_copy);
    testing.expectEqual(v1, 10);
}

test "strong-cloning a shared pointer" {
    var v = try RcSharedPointer(u128, NonAtomic).init(10, std.heap.page_allocator);
    defer v.deinit();
    testing.expectEqual(@intCast(usize, 1), v.strongCount());
    var v1 = v.strongClone();
    testing.expectEqual(@intCast(usize, 2), v.strongCount());
    v1.deinit();
    testing.expectEqual(@intCast(usize, 1), v.strongCount());
}

fn deinit_incr(val: *u128, ctx: *u128) void {
    ctx.* += val.*;
}
test "deinitializing a shared pointer with a callback and strong copies" {
    var v = try RcSharedPointer(u128, NonAtomic).init(10, std.heap.page_allocator);
    var r: u128 = 0;
    var v1 = v.strongClone();
    v.deinitWithCallback(*u128, &r, deinit_incr);
    v1.deinitWithCallback(*u128, &r, deinit_incr);
    testing.expectEqual(r, 10); // not 20 because the callback should only be called once
}

test "weak-cloning a shared pointer" {
    var v = try RcSharedPointer(u128, NonAtomic).init(10, std.heap.page_allocator);
    defer v.deinit();
    testing.expectEqual(@intCast(usize, 0), v.weakCount());
    var v1 = v.weakClone();
    testing.expectEqual(@intCast(usize, 1), v.weakCount());
    v1.deinit();
    testing.expectEqual(@intCast(usize, 0), v.weakCount());
}

test "weak-cloning a shared pointer" {
    var v = try RcSharedPointer(u128, NonAtomic).init(10, std.heap.page_allocator);
    defer v.deinit();
    testing.expectEqual(@intCast(usize, 0), v.weakCount());
    var v1 = v.weakClone();
    testing.expectEqual(@intCast(usize, 1), v.weakCount());
    var v2 = v.weakClone();
    testing.expectEqual(@intCast(usize, 2), v.weakCount());
    v1.deinit();
    v2.deinit();
    testing.expectEqual(@intCast(usize, 0), v.weakCount());
}

test "strong-cloning a weak clone" {
    var v = try RcSharedPointer(u128, NonAtomic).init(10, std.heap.page_allocator);
    defer v.deinit();
    testing.expectEqual(@intCast(usize, 0), v.weakCount());
    var v1 = v.weakClone();
    testing.expectEqual(@intCast(usize, 1), v.weakCount());
    var v2 = v1.strongClone().?;
    defer v2.deinit();
    v1.deinit();
    testing.expectEqual(@intCast(usize, 0), v.weakCount());
    testing.expectEqual(@intCast(usize, 2), v.strongCount());
}

test "strong-cloning a weak clone with no other strong clones" {
    var v = try RcSharedPointer(u128, NonAtomic).init(10, std.heap.page_allocator);
    var v1 = v.weakClone();
    testing.expectEqual(@intCast(usize, 1), v.weakCount());
    v.deinit();
    testing.expectEqual(@intCast(usize, 0), v1.strongCount());
    testing.expect(v1.strongClone() == null);
    v1.deinit();
}
