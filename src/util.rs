#![allow(dead_code)]

use core::{cmp::Ordering, hint::assert_unchecked, ptr::NonNull};

/// Mark a code path as cold.
#[inline(always)]
#[cold]
pub const fn cold<T>(x: T) -> T {
    x
}

/// Mark a code path as likely.
#[inline(always)]
#[must_use]
pub const fn likely(b: bool) -> bool {
    if b {
        b
    } else {
        cold(b)
    }
}

/// Mark a code path as unlikely.
#[inline(always)]
#[must_use]
pub const fn unlikely(b: bool) -> bool {
    if b {
        cold(b)
    } else {
        b
    }
}

/// Does a three way comparison on a [`isize`].
#[inline(always)]
#[must_use]
pub const fn cmp_isize(lhs: isize, rhs: isize) -> Ordering {
    if rhs > lhs {
        Ordering::Less
    } else if lhs != rhs {
        Ordering::Greater
    } else {
        Ordering::Equal
    }
}

/// Does a three way comparison on a [`usize`].
#[inline(always)]
#[must_use]
pub const fn cmp_usize(lhs: usize, rhs: usize) -> Ordering {
    // I forget why this offers better codegen lol.
    if rhs > lhs {
        Ordering::Less
    } else if lhs != rhs {
        Ordering::Greater
    } else {
        Ordering::Equal
    }
}

/// Does a three way comparison of two pointers.
///
/// # Safety
///
/// The caller must ensure that:
///
/// - `lhs` and `rhs` are derived from the same allocated object,
///
/// - That the memory range between `lhs` and `rhs` is within
///   the bounds of that object.
///
/// - The distance between the pointers, in bytes, must be an exact
///   multiple of size `T`.
///
/// These rules are derived from the rules of `offset_from`, which cannot
/// be interlinked to from rustdoc as of now. Ahhh technical limitations!
#[inline(always)]
#[must_use]
pub const unsafe fn ptr_cmp<T>(lhs: *const T, rhs: *const T) -> Ordering {
    unsafe { cmp_isize(lhs.offset_from(rhs), 0) }
}

/// Subtract `lhs` from `rhs`.
///
/// # Returns
///
/// Returns `(lhs as usize).unchecked_sub(rhs as usize) / size_of::<T>()`.
///
/// # Safety
///
/// The caller must ensure that `lhs >= rhs`.
///
/// See [`ptr_cmp`] for other invariants.
#[inline(always)]
#[must_use]
pub const unsafe fn ptr_sub<T>(lhs: *const T, rhs: *const T) -> usize {
    // SAFETY: The caller ensures that this is all valid.
    unsafe {
        // Hint the optimizer that `lhs >= rhs`, always.
        assert_unchecked(ptr_cmp(lhs, rhs).is_ge());

        match lhs.offset_from(rhs) {
            ..0 => unreachable!(),
            diff @ 0.. => diff as usize,
        }
    }
}

/// Calculate the length of a slice from it's start and end pointer.
///
/// # Safety
///
/// The caller must ensure that `start <= end`.
///
/// See [`ptr_cmp`] for other invariants.
#[inline(always)]
#[must_use]
pub const unsafe fn slice_len<T>(start: *const T, end: *const T) -> usize {
    // SAFETY: The caller ensures that this is valid.
    unsafe { ptr_sub(end, start) }
}

#[track_caller]
#[allow(dead_code)]
const unsafe fn assert_cmp<T>(lhs: *const T, rhs: *const T, ord: Ordering) {
    let message = match ord {
        Ordering::Less => "unsafe precondition violated: lhs is not less than rhs (`lhs >= rhs`)",
        Ordering::Equal => "unsafe precondition violated: lhs is not equal to rhs (`lhs == rhs`)",
        Ordering::Greater => {
            "unsafe precondition violated: lhs is not greater than rhs (`lhs <= rhs`)"
        }
    };

    let res = ptr_cmp(lhs, rhs);

    if (res as i8) != (ord as i8) {
        panic!("{}", message);
    }
}

// Sanity checks.
const _: () = {
    use core::ops::Range;

    let slice: &[u8] = &[0u8; 10];
    let Range { start, end } = slice.as_ptr_range();

    // SAFETY: We know they're all from the same allocated object.
    unsafe {
        assert_cmp(start, end, Ordering::Less);
        assert_cmp(end, start, Ordering::Greater);
        assert_cmp(start, start, Ordering::Equal);
        assert_cmp(end, end, Ordering::Equal);
    }
};

/// `ptr++` but in Rust.
///
/// # Safety
///
/// The caller must ensure that `ptr++` is not outside the bounds
/// of the allocated object it points to.
#[inline]
#[must_use]
pub const unsafe fn post_inc<T>(ptr: &mut NonNull<T>) -> NonNull<T> {
    let x = *ptr;
    // SAFETY: The caller ensures that this is safe.
    *ptr = unsafe { x.add(1) };
    x
}

/// Mask for UTF-8 continuation byte data.
pub const CONT_MASK: u8 = 0b0011_1111;

/// Returns the initial codepoint accumulator for the first byte.
/// The first byte is special, only want bottom 5 bits for width 2, 4 bits
/// for width 3, and 3 bits for width 4.
///
/// This is stolen from the standard library.
#[inline]
#[must_use]
pub const fn utf8_first_byte(byte: u8, width: u32) -> u32 {
    (byte & (0x7F >> width)) as u32
}

/// Returns the value of `ch` updated with continuation byte `byte`.
///
// This is stolen from the standard library.
#[inline]
#[must_use]
pub const fn utf8_acc_cont_byte(ch: u32, byte: u8) -> u32 {
    (ch << 6) | (byte & CONT_MASK) as u32
}

/// Checks whether the byte is a UTF-8 continuation byte (i.e., starts with the
/// bits `10`).
///
/// This is stolen from the standard library.
#[inline]
#[must_use]
pub const fn utf8_is_cont_byte(byte: u8) -> bool {
    (byte as i8) < -64
}

/// Decode the next code point from some UTF-8-like buffer.
///
/// This is stolen from the standard library, though some safety
/// comments are updated for consistency.
///
/// # Safety
///
/// The caller must ensure that `ptr` is within the buffer, and that
/// it is actually a UTF-8 like string.
#[inline]
#[must_use]
pub const unsafe fn next_code_point(ptr: &mut NonNull<u8>) -> u32 {
    // SAFETY: The caller ensures that `ptr` is within the buffer.
    let x = unsafe { post_inc(ptr).read() };

    // ASCII short path
    if likely(x.is_ascii()) {
        return x as u32;
    }

    // Multibyte case follows
    // Decode from a byte combination out of: [[[x y] z] w]
    //
    // NOTE: Performance is sensitive to the exact formulation here
    let init = utf8_first_byte(x, 2);

    // SAFETY: `ptr` points at a UTF-8 like string, so
    //         the buffer must have a valid value here.
    let y = unsafe { post_inc(ptr).read() };
    let mut ch = utf8_acc_cont_byte(init, y);

    if x >= 0xE0 {
        // [[x y z] w] case
        // 5th bit in 0xE0 .. 0xEF is always clear, so `init` is still valid
        //
        // SAFETY: `ptr` points at a UTF-8 like string, so
        //         the buffer must have a valid value here.
        let z = unsafe { post_inc(ptr).read() };
        let y_z = utf8_acc_cont_byte((y & CONT_MASK) as u32, z);
        ch = init << 12 | y_z;

        if x >= 0xF0 {
            // [x y z w] case
            // use only the lower 3 bits of `init`
            //
            // SAFETY: `ptr` points at a UTF-8 like string, so
            //         the buffer must have a valid value here.
            let w = unsafe { post_inc(ptr).read() };
            ch = (init & 7) << 18 | utf8_acc_cont_byte(y_z, w);
        }
    }

    ch
}

/// Decode the next unicode scalar value from some UTF-8 buffer.
///
/// # Safety
///
/// `ptr` must be a pointer to a UTF-8 buffer, and it must not
///  be empty.
///
/// See [`next_code_point`] for more details.
#[inline]
#[must_use]
pub const unsafe fn next_char(ptr: &mut NonNull<u8>) -> char {
    unsafe {
        let code_point = next_code_point(ptr);

        char::from_u32_unchecked(code_point)
    }
}

/// Determine whether a given byte is a UTF-8 character boundary.
///
/// Stolen from the standard library.
#[inline]
#[must_use]
pub const fn is_utf8_char_boundary(byte: u8) -> bool {
    // This is bit magic equivalent to: b < 128 || b >= 192
    (byte as i8) >= -0x40
}
