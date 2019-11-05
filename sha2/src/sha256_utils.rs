#![cfg_attr(feature = "cargo-clippy", allow(many_single_char_names))]

#[cfg(not(target_feature = "sha"))]
use simd::u32x4;

/// Not an intrinsic, but works like an unaligned load.
#[inline]
#[cfg(not(target_feature = "sha"))]
fn sha256load(v2: u32x4, v3: u32x4) -> u32x4 {
    u32x4(v3.3, v2.0, v2.1, v2.2)
}

/// Not an intrinsic, but useful for swapping vectors.
#[inline]
#[cfg(not(target_feature = "sha"))]
fn sha256swap(v0: u32x4) -> u32x4 {
    u32x4(v0.2, v0.3, v0.0, v0.1)
}

/// Emulates `llvm.x86.sha256msg1` intrinsic.
// #[inline]
#[cfg(not(target_feature = "sha"))]
fn sha256msg1(v0: u32x4, v1: u32x4) -> u32x4 {
    // sigma 0 on vectors
    #[inline]
    fn sigma0x4(x: u32x4) -> u32x4 {
        ((x >> u32x4(7, 7, 7, 7)) | (x << u32x4(25, 25, 25, 25)))
            ^ ((x >> u32x4(18, 18, 18, 18)) | (x << u32x4(14, 14, 14, 14)))
            ^ (x >> u32x4(3, 3, 3, 3))
    }

    v0 + sigma0x4(sha256load(v0, v1))
}

/// Emulates `llvm.x86.sha256msg2` intrinsic.
// #[inline]
#[cfg(not(target_feature = "sha"))]
fn sha256msg2(v4: u32x4, v3: u32x4) -> u32x4 {
    macro_rules! sigma1 {
        ($a:expr) => {
            $a.rotate_right(17) ^ $a.rotate_right(19) ^ ($a >> 10)
        };
    }

    let u32x4(x3, x2, x1, x0) = v4;
    let u32x4(w15, w14, _, _) = v3;

    let w16 = x0.wrapping_add(sigma1!(w14));
    let w17 = x1.wrapping_add(sigma1!(w15));
    let w18 = x2.wrapping_add(sigma1!(w16));
    let w19 = x3.wrapping_add(sigma1!(w17));

    u32x4(w19, w18, w17, w16)
}

/*
/// Performs 4 rounds of the SHA-256 message schedule update.
fn sha256_schedule_x4(v0: u32x4, v1: u32x4, v2: u32x4, v3: u32x4) -> u32x4 {
    sha256msg2(sha256msg1(v0, v1) + sha256load(v2, v3), v3)
}*/

/// Emulates `llvm.x86.sha256rnds2` intrinsic.
// #[inline]
#[cfg(not(target_feature = "sha"))]
fn sha256_digest_round_x2(cdgh: u32x4, abef: u32x4, wk: u32x4) -> u32x4 {
    macro_rules! big_sigma0 {
        ($a:expr) => {
            ($a.rotate_right(2) ^ $a.rotate_right(13) ^ $a.rotate_right(22))
        };
    }
    macro_rules! big_sigma1 {
        ($a:expr) => {
            ($a.rotate_right(6) ^ $a.rotate_right(11) ^ $a.rotate_right(25))
        };
    }
    macro_rules! bool3ary_202 {
        ($a:expr, $b:expr, $c:expr) => {
            $c ^ ($a & ($b ^ $c))
        };
    } // Choose, MD5F, SHA1C
    macro_rules! bool3ary_232 {
        ($a:expr, $b:expr, $c:expr) => {
            ($a & $b) ^ ($a & $c) ^ ($b & $c)
        };
    } // Majority, SHA1M

    let u32x4(_, _, wk1, wk0) = wk;
    let u32x4(a0, b0, e0, f0) = abef;
    let u32x4(c0, d0, g0, h0) = cdgh;

    // a round
    let x0 = big_sigma1!(e0)
        .wrapping_add(bool3ary_202!(e0, f0, g0))
        .wrapping_add(wk0)
        .wrapping_add(h0);
    let y0 = big_sigma0!(a0).wrapping_add(bool3ary_232!(a0, b0, c0));
    let (a1, b1, c1, d1, e1, f1, g1, h1) = (
        x0.wrapping_add(y0),
        a0,
        b0,
        c0,
        x0.wrapping_add(d0),
        e0,
        f0,
        g0,
    );

    // a round
    let x1 = big_sigma1!(e1)
        .wrapping_add(bool3ary_202!(e1, f1, g1))
        .wrapping_add(wk1)
        .wrapping_add(h1);
    let y1 = big_sigma0!(a1).wrapping_add(bool3ary_232!(a1, b1, c1));
    let (a2, b2, _, _, e2, f2, _, _) = (
        x1.wrapping_add(y1),
        a1,
        b1,
        c1,
        x1.wrapping_add(d1),
        e1,
        f1,
        g1,
    );

    u32x4(a2, b2, e2, f2)
}

/// Process a block with the SHA-256 algorithm.
#[cfg(not(target_feature = "sha"))]
fn sha256_digest_block_u32(state: &mut [u32; 8], block: &[u32; 16]) {
    use consts;

    let k = &consts::K32X4;

    macro_rules! schedule {
        ($v0:expr, $v1:expr, $v2:expr, $v3:expr) => {
            sha256msg2(sha256msg1($v0, $v1) + sha256load($v2, $v3), $v3)
        };
    }

    macro_rules! rounds4 {
        ($abef:ident, $cdgh:ident, $rest:expr) => {{
            $cdgh = sha256_digest_round_x2($cdgh, $abef, $rest);
            $abef = sha256_digest_round_x2($abef, $cdgh, sha256swap($rest));
        }};
    }

    let mut abef = u32x4(state[0], state[1], state[4], state[5]);
    let mut cdgh = u32x4(state[2], state[3], state[6], state[7]);

    // Rounds 0..64
    let mut w0 = u32x4(block[3], block[2], block[1], block[0]);
    rounds4!(abef, cdgh, k[0] + w0);
    let mut w1 = u32x4(block[7], block[6], block[5], block[4]);
    rounds4!(abef, cdgh, k[1] + w1);
    let mut w2 = u32x4(block[11], block[10], block[9], block[8]);
    rounds4!(abef, cdgh, k[2] + w2);
    let mut w3 = u32x4(block[15], block[14], block[13], block[12]);
    rounds4!(abef, cdgh, k[3] + w3);
    let mut w4 = schedule!(w0, w1, w2, w3);
    rounds4!(abef, cdgh, k[4] + w4);
    w0 = schedule!(w1, w2, w3, w4);
    rounds4!(abef, cdgh, k[5] + w0);
    w1 = schedule!(w2, w3, w4, w0);
    rounds4!(abef, cdgh, k[6] + w1);
    w2 = schedule!(w3, w4, w0, w1);
    rounds4!(abef, cdgh, k[7] + w2);
    w3 = schedule!(w4, w0, w1, w2);
    rounds4!(abef, cdgh, k[8] + w3);
    w4 = schedule!(w0, w1, w2, w3);
    rounds4!(abef, cdgh, k[9] + w4);
    w0 = schedule!(w1, w2, w3, w4);
    rounds4!(abef, cdgh, k[10] + w0);
    w1 = schedule!(w2, w3, w4, w0);
    rounds4!(abef, cdgh, k[11] + w1);
    w2 = schedule!(w3, w4, w0, w1);
    rounds4!(abef, cdgh, k[12] + w2);
    w3 = schedule!(w4, w0, w1, w2);
    rounds4!(abef, cdgh, k[13] + w3);
    w4 = schedule!(w0, w1, w2, w3);
    rounds4!(abef, cdgh, k[14] + w4);
    w0 = schedule!(w1, w2, w3, w4);
    rounds4!(abef, cdgh, k[15] + w0);

    let u32x4(a, b, e, f) = abef;
    let u32x4(c, d, g, h) = cdgh;

    state[0] = state[0].wrapping_add(a);
    state[1] = state[1].wrapping_add(b);
    state[2] = state[2].wrapping_add(c);
    state[3] = state[3].wrapping_add(d);
    state[4] = state[4].wrapping_add(e);
    state[5] = state[5].wrapping_add(f);
    state[6] = state[6].wrapping_add(g);
    state[7] = state[7].wrapping_add(h);
}

/// Process a block with the SHA-256 algorithm.
/// Based on https://github.com/noloader/SHA-Intrinsics/blob/master/sha256-x86.c
#[cfg(target_feature = "sha")]
pub fn compress256(state: &mut [u32; 8], block: &[u8; 64]) {
    #[cfg(target_arch = "x86")]
    use core::arch::x86::*;
    #[cfg(target_arch = "x86_64")]
    use core::arch::x86_64::*;

    // TODO: Process multiple blocks

    unsafe {
        let mut state0: __m128i;
        let mut state1: __m128i;

        let mut msg: __m128i;
        let mut tmp: __m128i;

        let mut msg0: __m128i;
        let mut msg1: __m128i;
        let mut msg2: __m128i;
        let mut msg3: __m128i;

        let mut abef_save: __m128i;
        let mut cdgh_save: __m128i;

        #[allow(non_snake_case)]
        let MASK: __m128i = _mm_set_epi64x(
            0x0c0d_0e0f_0809_0a0bu64 as i64,
            0x0405_0607_0001_0203u64 as i64,
        );

        let mut block_offset = 0;
        let mut length = 64;

        // Load initial values
        tmp = _mm_loadu_si128(state.as_ptr().add(0) as *const __m128i);
        state1 = _mm_loadu_si128(state.as_ptr().add(4) as *const __m128i);

        tmp = _mm_shuffle_epi32(tmp, 0xB1); // CDAB
        state1 = _mm_shuffle_epi32(state1, 0x1B); // EFGH
        state0 = _mm_alignr_epi8(tmp, state1, 8); // ABEF
        state1 = _mm_blend_epi16(state1, tmp, 0xF0); // CDGH

        while length >= 64 {
            // Save current state
            abef_save = state0;
            cdgh_save = state1;

            // Rounds 0-3
            msg = _mm_loadu_si128(block.as_ptr().add(block_offset + 0) as *const __m128i);
            msg0 = _mm_shuffle_epi8(msg, MASK);
            msg = _mm_add_epi32(
                msg0,
                _mm_set_epi64x(0xE9B5DBA5B5C0FBCFu64 as i64, 0x71374491428A2F98u64 as i64),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);

            // Rounds 4-7
            msg1 = _mm_loadu_si128(block.as_ptr().add(block_offset + 16) as *const __m128i);
            msg1 = _mm_shuffle_epi8(msg1, MASK);
            msg = _mm_add_epi32(
                msg1,
                _mm_set_epi64x(0xAB1C5ED5923F82A4u64 as i64, 0x59F111F13956C25Bu64 as i64),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg0 = _mm_sha256msg1_epu32(msg0, msg1);

            // Rounds 8-11
            msg2 = _mm_loadu_si128(block.as_ptr().add(block_offset + 32) as *const __m128i);
            msg2 = _mm_shuffle_epi8(msg2, MASK);
            msg = _mm_add_epi32(
                msg2,
                _mm_set_epi64x(0x550C7DC3243185BEu64 as i64, 0x12835B01D807AA98u64 as i64),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg1 = _mm_sha256msg1_epu32(msg1, msg2);

            // Rounds 12-15
            msg3 = _mm_loadu_si128(block.as_ptr().add(block_offset + 48) as *const __m128i);
            msg3 = _mm_shuffle_epi8(msg3, MASK);
            msg = _mm_add_epi32(
                msg3,
                _mm_set_epi64x(0xC19BF1749BDC06A7u64 as i64, 0x80DEB1FE72BE5D74u64 as i64),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg3, msg2, 4);
            msg0 = _mm_add_epi32(msg0, tmp);
            msg0 = _mm_sha256msg2_epu32(msg0, msg3);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg2 = _mm_sha256msg1_epu32(msg2, msg3);

            // Rounds 16-19
            msg = _mm_add_epi32(
                msg0,
                _mm_set_epi64x(0x240CA1CC0FC19DC6u64 as i64, 0xEFBE4786E49B69C1u64 as i64),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg0, msg3, 4);
            msg1 = _mm_add_epi32(msg1, tmp);
            msg1 = _mm_sha256msg2_epu32(msg1, msg0);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg3 = _mm_sha256msg1_epu32(msg3, msg0);

            // Rounds 20-23
            msg = _mm_add_epi32(
                msg1,
                _mm_set_epi64x(0x76F988DA5CB0A9DCu64 as i64, 0x4A7484AA2DE92C6Fu64 as i64),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg1, msg0, 4);
            msg2 = _mm_add_epi32(msg2, tmp);
            msg2 = _mm_sha256msg2_epu32(msg2, msg1);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg0 = _mm_sha256msg1_epu32(msg0, msg1);

            // Rounds 24-27
            msg = _mm_add_epi32(
                msg2,
                _mm_set_epi64x(0xBF597FC7B00327C8u64 as i64, 0xA831C66D983E5152u64 as i64),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg2, msg1, 4);
            msg3 = _mm_add_epi32(msg3, tmp);
            msg3 = _mm_sha256msg2_epu32(msg3, msg2);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg1 = _mm_sha256msg1_epu32(msg1, msg2);

            // Rounds 28-31
            msg = _mm_add_epi32(
                msg3,
                _mm_set_epi64x(0x1429296706CA6351u64 as i64, 0xD5A79147C6E00BF3u64 as i64),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg3, msg2, 4);
            msg0 = _mm_add_epi32(msg0, tmp);
            msg0 = _mm_sha256msg2_epu32(msg0, msg3);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg2 = _mm_sha256msg1_epu32(msg2, msg3);

            // Rounds 32-35
            msg = _mm_add_epi32(
                msg0,
                _mm_set_epi64x(0x53380D134D2C6DFCu64 as i64, 0x2E1B213827B70A85u64 as i64),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg0, msg3, 4);
            msg1 = _mm_add_epi32(msg1, tmp);
            msg1 = _mm_sha256msg2_epu32(msg1, msg0);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg3 = _mm_sha256msg1_epu32(msg3, msg0);

            // Rounds 36-39
            msg = _mm_add_epi32(
                msg1,
                _mm_set_epi64x(0x92722C8581C2C92Eu64 as i64, 0x766A0ABB650A7354u64 as i64),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg1, msg0, 4);
            msg2 = _mm_add_epi32(msg2, tmp);
            msg2 = _mm_sha256msg2_epu32(msg2, msg1);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg0 = _mm_sha256msg1_epu32(msg0, msg1);

            // Rounds 40-43
            msg = _mm_add_epi32(
                msg2,
                _mm_set_epi64x(0xC76C51A3C24B8B70u64 as i64, 0xA81A664BA2BFE8A1u64 as i64),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg2, msg1, 4);
            msg3 = _mm_add_epi32(msg3, tmp);
            msg3 = _mm_sha256msg2_epu32(msg3, msg2);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg1 = _mm_sha256msg1_epu32(msg1, msg2);

            // Rounds 44-47
            msg = _mm_add_epi32(
                msg3,
                _mm_set_epi64x(0x106AA070F40E3585u64 as i64, 0xD6990624D192E819u64 as i64),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg3, msg2, 4);
            msg0 = _mm_add_epi32(msg0, tmp);
            msg0 = _mm_sha256msg2_epu32(msg0, msg3);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg2 = _mm_sha256msg1_epu32(msg2, msg3);

            // Rounds 48-51
            msg = _mm_add_epi32(
                msg0,
                _mm_set_epi64x(0x34B0BCB52748774Cu64 as i64, 0x1E376C0819A4C116u64 as i64),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg0, msg3, 4);
            msg1 = _mm_add_epi32(msg1, tmp);
            msg1 = _mm_sha256msg2_epu32(msg1, msg0);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
            msg3 = _mm_sha256msg1_epu32(msg3, msg0);

            // Rounds 52-55
            msg = _mm_add_epi32(
                msg1,
                _mm_set_epi64x(0x682E6FF35B9CCA4Fu64 as i64, 0x4ED8AA4A391C0CB3u64 as i64),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg1, msg0, 4);
            msg2 = _mm_add_epi32(msg2, tmp);
            msg2 = _mm_sha256msg2_epu32(msg2, msg1);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);

            // Rounds 56-59
            msg = _mm_add_epi32(
                msg2,
                _mm_set_epi64x(0x8CC7020884C87814u64 as i64, 0x78A5636F748F82EEu64 as i64),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            tmp = _mm_alignr_epi8(msg2, msg1, 4);
            msg3 = _mm_add_epi32(msg3, tmp);
            msg3 = _mm_sha256msg2_epu32(msg3, msg2);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);

            // Rounds 60-63
            msg = _mm_add_epi32(
                msg3,
                _mm_set_epi64x(0xC67178F2BEF9A3F7u64 as i64, 0xA4506CEB90BEFFFAu64 as i64),
            );
            state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
            msg = _mm_shuffle_epi32(msg, 0x0E);
            state0 = _mm_sha256rnds2_epu32(state0, state1, msg);

            // Combine state
            state0 = _mm_add_epi32(state0, abef_save);
            state1 = _mm_add_epi32(state1, cdgh_save);

            block_offset += 64;
            length -= 64;
        }

        tmp = _mm_shuffle_epi32(state0, 0x1B); // FEBA
        state1 = _mm_shuffle_epi32(state1, 0xB1); // DCHG
        state0 = _mm_blend_epi16(tmp, state1, 0xF0); // DCBA
        state1 = _mm_alignr_epi8(state1, tmp, 8); // ABEF

        // Save state
        _mm_storeu_si128(state.as_ptr().add(0) as *mut __m128i, state0);
        _mm_storeu_si128(state.as_ptr().add(4) as *mut __m128i, state1);
    }
}

/// Process a block with the SHA-256 algorithm. (See more...)
///
/// Internally, this uses functions which resemble the new Intel SHA instruction
/// sets, and so it's data locality properties may improve performance. However,
/// to benefit the most from this implementation, replace these functions with
/// x86 intrinsics to get a possible speed boost.
///
/// # Implementation
///
/// The `Sha256` algorithm is implemented with functions that resemble the new
/// Intel SHA instruction set extensions. These intructions fall into two
/// categories: message schedule calculation, and the message block 64-round
/// digest calculation. The schedule-related instructions allow 4 rounds to be
/// calculated as:
///
/// ```ignore
/// use std::simd::u32x4;
/// use self::crypto::sha2::{
///     sha256msg1,
///     sha256msg2,
///     sha256load
/// };
///
/// fn schedule4_data(work: &mut [u32x4], w: &[u32]) {
///
///     // this is to illustrate the data order
///     work[0] = u32x4(w[3], w[2], w[1], w[0]);
///     work[1] = u32x4(w[7], w[6], w[5], w[4]);
///     work[2] = u32x4(w[11], w[10], w[9], w[8]);
///     work[3] = u32x4(w[15], w[14], w[13], w[12]);
/// }
///
/// fn schedule4_work(work: &mut [u32x4], t: usize) {
///
///     // this is the core expression
///     work[t] = sha256msg2(sha256msg1(work[t - 4], work[t - 3]) +
///                          sha256load(work[t - 2], work[t - 1]),
///                          work[t - 1])
/// }
/// ```
///
/// instead of 4 rounds of:
///
/// ```ignore
/// fn schedule_work(w: &mut [u32], t: usize) {
///     w[t] = sigma1!(w[t - 2]) + w[t - 7] + sigma0!(w[t - 15]) + w[t - 16];
/// }
/// ```
///
/// and the digest-related instructions allow 4 rounds to be calculated as:
///
/// ```ignore
/// use std::simd::u32x4;
/// use self::crypto::sha2::{K32X4,
///     sha256rnds2,
///     sha256swap
/// };
///
/// fn rounds4(state: &mut [u32; 8], work: &mut [u32x4], t: usize) {
///     let [a, b, c, d, e, f, g, h]: [u32; 8] = *state;
///
///     // this is to illustrate the data order
///     let mut abef = u32x4(a, b, e, f);
///     let mut cdgh = u32x4(c, d, g, h);
///     let temp = K32X4[t] + work[t];
///
///     // this is the core expression
///     cdgh = sha256rnds2(cdgh, abef, temp);
///     abef = sha256rnds2(abef, cdgh, sha256swap(temp));
///
///     *state = [abef.0, abef.1, cdgh.0, cdgh.1,
///               abef.2, abef.3, cdgh.2, cdgh.3];
/// }
/// ```
///
/// instead of 4 rounds of:
///
/// ```ignore
/// fn round(state: &mut [u32; 8], w: &mut [u32], t: usize) {
///     let [a, b, c, mut d, e, f, g, mut h]: [u32; 8] = *state;
///
///     h += big_sigma1!(e) +   choose!(e, f, g) + K32[t] + w[t]; d += h;
///     h += big_sigma0!(a) + majority!(a, b, c);
///
///     *state = [h, a, b, c, d, e, f, g];
/// }
/// ```
///
/// **NOTE**: It is important to note, however, that these instructions are not
/// implemented by any CPU (at the time of this writing), and so they are
/// emulated in this library until the instructions become more common, and gain
///  support in LLVM (and GCC, etc.).
#[cfg(not(target_feature = "sha"))]
pub fn compress256(state: &mut [u32; 8], block: &[u8; 64]) {
    use block_buffer::byteorder::{ByteOrder, BE};
    use consts::BLOCK_LEN;

    let mut block_u32 = [0u32; BLOCK_LEN];
    BE::read_u32_into(block, &mut block_u32[..]);
    sha256_digest_block_u32(state, &block_u32);
}
