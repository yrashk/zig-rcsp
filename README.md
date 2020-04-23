# Reference-counted Shared Pointer for Zig

This is an implementation of (both atomically and non-atomically) reference-counted shared pointer for [Zig](https://ziglang.org). It's somewhat similar to Rust's [Rc](https://doc.rust-lang.org/std/rc/struct.Rc.html) and [Arc](https://doc.rust-lang.org/std/sync/struct.Arc.html) as well as C++'s [shared_ptr](https://en.cppreference.com/w/cpp/memory/shared_ptr).

It's in early stages of development and is **not** proven to be correct or feature-complete. Let's call it a prototype.
