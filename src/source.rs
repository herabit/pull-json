use crate::util::{
    cmp_usize, is_utf8_char_boundary, likely, next_char, ptr_cmp, ptr_sub, slice_len,
};
use core::{
    cmp::Ordering,
    hint::assert_unchecked,
    marker::PhantomData,
    ops::Range,
    ptr::{self, NonNull},
};

/// A cursor over a UTF-8 string.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Source<'a> {
    /// The start of the string.
    start: NonNull<u8>,
    /// The end of the string.
    end: NonNull<u8>,

    /// The current position in the string.
    ///
    /// # Safety
    ///
    /// - Must always lie on a UTF-8 character boundary.
    /// - Must always be within `start..end`,
    ///   so `start <= cur` and `cur <= end`
    ///   must always be true.
    cur: NonNull<u8>,
    _marker: PhantomData<&'a str>,
}

impl<'a> Source<'a> {
    /// Create a new [`Source`] from a string.
    #[inline]
    #[must_use]
    pub const fn new(string: &'a str) -> Source<'a> {
        let Range { start, end } = string.as_bytes().as_ptr_range();
        // SAFETY: We know that `start..end` are from a valid string slice,
        //         so both must be nonnull.
        let (start, end) = unsafe {
            (
                NonNull::new_unchecked(start as *mut u8),
                NonNull::new_unchecked(end as *mut u8),
            )
        };

        Source {
            start,
            end,
            cur: start,
            _marker: PhantomData,
        }
    }

    /// Returns the length of the input.
    #[inline]
    #[must_use]
    pub const fn input_len(&self) -> usize {
        // SAFETY: We know that the input string was valid.
        unsafe { slice_len(self.start.as_ptr(), self.end.as_ptr()) }
    }

    /// Returns the length of the consumed input.
    #[inline]
    #[must_use]
    pub const fn consumed_len(&self) -> usize {
        // SAFETY: We know that the input was valid and `cur`
        //         always lies on a UTF-8 character boundary.
        unsafe { slice_len(self.start.as_ptr(), self.cur.as_ptr()) }
    }

    /// Returns the length of the remaining input.
    #[inline]
    #[must_use]
    pub const fn remaining_len(&self) -> usize {
        // SAFETY: We know that `cur` lies on a valid UTF-8
        //         character boundary and that `end` also does.
        unsafe { slice_len(self.cur.as_ptr(), self.end.as_ptr()) }
    }

    /// Returns the input.
    #[inline]
    #[must_use]
    pub const fn input(&self) -> &'a str {
        let slice = ptr::slice_from_raw_parts(self.start.as_ptr(), self.input_len());

        // SAFETY: We know that the input was a valid UTF-8 string.
        unsafe { &*(slice as *const str) }
    }

    /// Returns the input bytes.
    #[inline]
    #[must_use]
    pub const fn input_bytes(&self) -> &'a [u8] {
        self.input().as_bytes()
    }

    /// Returns the consumed input.
    #[inline]
    #[must_use]
    pub const fn consumed(&self) -> &'a str {
        let slice = ptr::slice_from_raw_parts(self.start.as_ptr(), self.consumed_len());

        // SAFETY: We know that the input was valid and that
        //         `cur` lies on a valid UTF-8 boundary.
        unsafe { &*(slice as *const str) }
    }

    /// Returns the consumed input bytes.
    #[inline]
    #[must_use]
    pub const fn consumed_bytes(&self) -> &'a [u8] {
        self.consumed().as_bytes()
    }

    /// Returns the remaining input.
    #[inline]
    #[must_use]
    pub const fn remaining(&self) -> &'a str {
        let slice = ptr::slice_from_raw_parts(self.cur.as_ptr(), self.remaining_len());

        // SAFETY: We know that `cur` and `end` both lie on UTF-8
        //        character boundaries.
        unsafe { &*(slice as *const str) }
    }

    /// Returns the remaining input bytes.
    #[inline]
    #[must_use]
    pub const fn remaining_bytes(&self) -> &'a [u8] {
        self.remaining().as_bytes()
    }

    /// Returns whether the input is depleted.
    #[inline]
    #[must_use]
    pub const fn is_eof(&self) -> bool {
        // SAFETY: We know that `cur` and `end` are derived from the same
        //         allocated object.
        unsafe { ptr_cmp(self.cur.as_ptr(), self.end.as_ptr()).is_eq() }
    }

    /// Returns the current offset of the cursor in the input.
    #[inline]
    #[must_use]
    pub const fn offset(&self) -> usize {
        // SAFETY: We know that `start <= cur` and that both exist
        //         within the same allocated object.
        unsafe { ptr_sub(self.cur.as_ptr(), self.start.as_ptr()) }
    }

    /// Returns whether the specified offset in the remaining input
    /// is a UTF-8 character boundary.
    ///
    /// In other words, it determines whether the byte at the specified
    /// index is the first byte in a UTF-8 code point sequence,
    /// or if it is at the end of the string.
    #[inline]
    #[must_use]
    #[no_mangle]
    pub const fn is_char_boundary(&self, index: usize) -> bool {
        if index == 0 {
            return true;
        }

        match cmp_usize(index, self.remaining_len()) {
            // NOTE: The optimizer should omit the bounds check just fine here.
            Ordering::Less => is_utf8_char_boundary(self.remaining_bytes()[index]),
            Ordering::Equal => true,
            Ordering::Greater => false,
        }
    }
}

impl<'a> Source<'a> {
    /// Peek the next byte without consuming input,
    /// and without checking whether we're at the EOF.
    ///
    /// # Safety
    ///
    /// The caller must ensure that we're not at the EOF.
    #[inline]
    #[must_use]
    pub const unsafe fn peek_byte_unchecked(&self) -> u8 {
        // SAFETY: The caller ensures we're not at the
        //         EOF.
        unsafe {
            assert_unchecked(!self.is_eof());
            self.cur.read()
        }
    }

    /// Peek the next byte without consuming input.
    #[inline]
    #[must_use]
    pub const fn peek_byte(&self) -> Option<u8> {
        if likely(!self.is_eof()) {
            Some(unsafe { self.peek_byte_unchecked() })
        } else {
            None
        }
    }

    /// Peek the next `N` bytes without consuming input,
    /// and without bounds checks.
    ///
    /// # Safety
    ///
    /// The caller must ensure that there are at least
    /// `N` bytes remaining in the source.
    #[inline]
    #[must_use]
    pub const unsafe fn peek_bytes_unchecked<const N: usize>(&self) -> [u8; N] {
        // SAFETY: The caller ensures that there are at least `N`
        //         bytes remaining in the source.
        unsafe {
            assert_unchecked(self.remaining_len() >= N);

            self.cur.cast::<[u8; N]>().read()
        }
    }

    /// Peek the next `N` bytes without consuming input.
    #[inline]
    #[must_use]
    pub const fn peek_bytes<const N: usize>(&self) -> Option<[u8; N]> {
        if likely(self.remaining_len() >= N) {
            Some(unsafe { self.peek_bytes_unchecked() })
        } else {
            None
        }
    }

    /// Peek the next char without consuming input and without bounds checks.
    #[inline]
    #[must_use]
    pub const unsafe fn peek_char_unchecked(&self) -> char {
        unsafe {
            assert_unchecked(!self.is_eof());
            next_char(&mut { self.cur })
        }
    }

    /// Peek the next char without consuming input.
    #[inline]
    #[must_use]
    pub const fn peek_char(&self) -> Option<char> {
        if likely(!self.is_eof()) {
            Some(unsafe { self.peek_char_unchecked() })
        } else {
            None
        }
    }
}

impl Default for Source<'_> {
    #[inline]
    fn default() -> Self {
        Source::new("")
    }
}

// SAFETY: [`Source`] is just a wrapper around what amounts
//         to an immutable string slice. We will however,
//         just add some sanity checks through the where
//         clause.
unsafe impl<'a> Send for Source<'a> where &'a str: Send {}
unsafe impl<'a> Sync for Source<'a> where &'a str: Sync {}
