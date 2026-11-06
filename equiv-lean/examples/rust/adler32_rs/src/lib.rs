//! zlib 1.3.1's Adler-32 (`adler32.c`, tag commit 51b7f2a) in safe Rust.
//!
//! Written by equiv-lean's agents in an Aeneas-friendly form: no `unsafe`, `while` loops with no
//! `return` inside, `u64` for `uLong`, `usize` for `z_size_t`, `u32` for `uInt`, `i64` for
//! `z_off_t`/`z_off64_t` (x86_64 LP64), `Option<&[u8]>` for `buf` (`None` is `Z_NULL`).
//! The default configuration (no `NO_DIVIDE`): `MOD`, `MOD28` and `MOD63` are `% BASE`.
//! The unrolled `DO1`..`DO16` sums are the helper `do_bytes`, which adds the same bytes in the
//! same order; the paths and the reductions (the single subtraction of `BASE` on the `len == 1`
//! and `len < 16` paths, `% BASE` after each `NMAX` block and after the tail) are those of the C.

/// Largest prime smaller than 65536.
pub const BASE: u64 = 65521;

/// The largest n such that 255n(n+1)/2 + (n+1)(BASE-1) <= 2^32-1.
pub const NMAX: usize = 5552;

/// `DO1` for `n` bytes: adds `buf[i]`, ..., `buf[i + n - 1]` to `adler` and each new `adler` to
/// `sum2`; returns the two sums.
pub fn do_bytes(buf: &[u8], i: usize, n: usize, adler: u64, sum2: u64) -> (u64, u64) {
    let mut a = adler;
    let mut s = sum2;
    let mut k = 0;
    while k < n {
        a += buf[i + k] as u64;
        s += a;
        k += 1;
    }
    (a, s)
}

/// `adler32_z(adler, buf, len)`.  With `buf == Z_NULL` and `len == 1` the C reads `buf[0]`
/// (undefined behaviour); this translation returns 1 there.
pub fn adler32_z(adler: u64, buf: Option<&[u8]>, len: usize) -> u64 {
    // split Adler-32 into component sums
    let sum2 = (adler >> 16) & 0xffff;
    let a = adler & 0xffff;
    if len == 1 {
        // in case user likes doing a byte at a time, keep it fast
        match buf {
            Some(b) => {
                let mut a1 = a + b[0] as u64;
                if a1 >= BASE {
                    a1 -= BASE;
                }
                let mut s1 = sum2 + a1;
                if s1 >= BASE {
                    s1 -= BASE;
                }
                a1 | (s1 << 16)
            }
            None => 1,
        }
    } else {
        match buf {
            // initial Adler-32 value (deferred check for len == 1 speed)
            None => 1,
            Some(b) => {
                if len < 16 {
                    // in case short lengths are provided, keep it somewhat fast
                    let (a1, s1) = do_bytes(b, 0, len, a, sum2);
                    let mut a2 = a1;
                    if a2 >= BASE {
                        a2 -= BASE;
                    }
                    let s2 = s1 % BASE; // MOD28: only added so many BASE's
                    a2 | (s2 << 16)
                } else {
                    let mut aa = a;
                    let mut ss = sum2;
                    let mut i = 0;
                    let mut rest = len;
                    // do length NMAX blocks -- requires just one modulo operation
                    while rest >= NMAX {
                        rest -= NMAX;
                        let (a1, s1) = do_bytes(b, i, NMAX, aa, ss);
                        i += NMAX;
                        aa = a1 % BASE;
                        ss = s1 % BASE;
                    }
                    // do remaining bytes (less than NMAX, still just one modulo)
                    if rest != 0 {
                        // avoid modulos if none remaining
                        let (a1, s1) = do_bytes(b, i, rest, aa, ss);
                        aa = a1 % BASE;
                        ss = s1 % BASE;
                    }
                    // return recombined sums
                    aa | (ss << 16)
                }
            }
        }
    }
}

/// `adler32(adler, buf, len)`: the `uInt` wrapper.
pub fn adler32(adler: u64, buf: Option<&[u8]>, len: u32) -> u64 {
    adler32_z(adler, buf, len as usize)
}

/// `adler32_combine_(adler1, adler2, len2)`.
fn adler32_combine_(adler1: u64, adler2: u64, len2: i64) -> u64 {
    // for negative len, return invalid adler32 as a clue for debugging
    if len2 < 0 {
        0xffffffff
    } else {
        // the derivation of this formula is left as an exercise for the reader
        let rem = (len2 % (BASE as i64)) as u32; // MOD63, then (unsigned)
        let sum1 = adler1 & 0xffff;
        let sum2 = (rem as u64 * sum1) % BASE; // MOD(sum2)
        let mut sum1 = sum1 + (adler2 & 0xffff) + BASE - 1;
        let mut sum2 = sum2 + ((adler1 >> 16) & 0xffff) + ((adler2 >> 16) & 0xffff) + BASE
            - rem as u64;
        if sum1 >= BASE {
            sum1 -= BASE;
        }
        if sum1 >= BASE {
            sum1 -= BASE;
        }
        if sum2 >= BASE << 1 {
            sum2 -= BASE << 1;
        }
        if sum2 >= BASE {
            sum2 -= BASE;
        }
        sum1 | (sum2 << 16)
    }
}

/// `adler32_combine(adler1, adler2, len2)` (`z_off_t` is 64 bits on LP64).
pub fn adler32_combine(adler1: u64, adler2: u64, len2: i64) -> u64 {
    adler32_combine_(adler1, adler2, len2)
}

/// `adler32_combine64(adler1, adler2, len2)`.
pub fn adler32_combine64(adler1: u64, adler2: u64, len2: i64) -> u64 {
    adler32_combine_(adler1, adler2, len2)
}
