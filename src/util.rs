use core::{fmt, marker, mem, ptr, str};

// do not drop partially written data because:
const _STATIC_ASSERT: () = assert!(!mem::needs_drop::<u8>(), "u8 never needs drop");

/// A write-only cursor over an uninitialized byte buffer.
#[derive(Debug)]
pub struct UninitWriter<'a> {
    // SAFETY: all operations must guarantee the following:
    // - `pointer` must always be aligned and valid for writes of up to `capacity` bytes.
    // - The memory region must remain exclusively and mutably borrowed for lifetime `'a`.
    pointer: *mut u8,
    capacity: usize,
    _lifetime: marker::PhantomData<&'a mut u8>,
}

impl<'a> UninitWriter<'a> {
    /// Creates a new instance from a mutable reference to an uninitialized buffer.
    pub const fn new<const N: usize>(buffer: &'a mut mem::MaybeUninit<[u8; N]>) -> Self {
        Self {
            pointer: buffer.as_mut_ptr().cast::<u8>(),
            capacity: N,
            _lifetime: marker::PhantomData,
        }
    }

    /// Fills the remaining capacity with `filler`, consuming the writer to prevent further writes.
    pub const fn fill_and_finish(self, filler: u8) {
        // SAFETY: ok because the struct invariants guarantee that `pointer` is valid for the write
        unsafe { ptr::write_bytes(self.pointer, filler, self.capacity) };
    }

    /// Writes bytes to the uninitialized memory without checking bounds.
    ///
    /// # Safety
    ///
    /// `bytes` must not be longer than the remaining capacity of the writer.
    pub const unsafe fn write_unchecked(&mut self, bytes: &[u8]) {
        // SAFETY: ok because:
        // - The caller guarantees that `bytes` fit in the remaining capacity.
        // - The struct invariants guarantee that `pointer` is valid for the write.
        // - The exclusive borrow by this struct guarantees that `bytes` do not overlap with the
        //   memory region being written to.
        debug_assert!(bytes.len() <= self.capacity);
        unsafe { ptr::copy_nonoverlapping(bytes.as_ptr(), self.pointer, bytes.len()) };

        // SAFETY: ok because `bytes.len() <= capacity` guarantees that the advanced `pointer` stays
        // within the allocation and remains valid for writes of up to the new `capacity` bytes
        self.capacity -= bytes.len();
        self.pointer = unsafe { self.pointer.add(bytes.len()) };
    }
}

impl fmt::Write for UninitWriter<'_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        if s.len() <= self.capacity {
            // SAFETY: ok because the length is checked above
            unsafe { self.write_unchecked(s.as_bytes()) };
            Ok(())
        } else {
            Err(fmt::Error)
        }
    }
}
