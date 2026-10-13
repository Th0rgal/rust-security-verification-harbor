//! Rollup batch transcript framing and header digest helpers for sequencer telemetry.

use crate::constants::*;
use crate::word_math::{extract_high_u32, extract_low_u32};

/// Framed batch transcript header metadata.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TranscriptHeader {
    pub version: u64,
    pub domain_tag: u64,
    pub payload_low32: u64,
    pub checksum_word: u64,
}

/// Extracts the 8-bit domain tag from a parameter word, defaulting to
/// `SEQUENCER_DOMAIN_TAG` when the low byte is zero.
#[inline]
pub fn decode_domain_tag(word: u64) -> u64 {
    let raw_tag: u64 = word & CODEC_TAG_MASK;
    if raw_tag == 0u64 {
        SEQUENCER_DOMAIN_TAG
    } else {
        raw_tag
    }
}

/// Builds a framed `TranscriptHeader` from `(amount, fee)` for batch indexing.
#[inline]
pub fn build_transcript_header(amount: u64, fee: u64) -> TranscriptHeader {
    let version: u64 = CODEC_VERSION_V3;
    let domain_tag: u64 = decode_domain_tag(fee);
    let payload_low32: u64 = extract_low_u32(amount);
    let hi_fee: u64 = extract_high_u32(fee);
    let checksum_word: u64 = (payload_low32 ^ hi_fee) + (domain_tag << 8u64) + version;
    TranscriptHeader {
        version,
        domain_tag,
        payload_low32,
        checksum_word,
    }
}

/// Checks whether a `TranscriptHeader` carries the canonical v3 version tag.
#[inline]
pub fn verify_header_version(header: TranscriptHeader) -> bool {
    header.version == CODEC_VERSION_V3
}

/// Folds a `TranscriptHeader` into a 64-bit diagnostic digest word.
#[inline]
pub fn fold_header_digest(header: TranscriptHeader) -> u64 {
    (header.checksum_word & LOW32_MASK) + (header.domain_tag << 32u64)
}

/// Mixes two `TranscriptHeader` digests for two-leaf Merkle batch telemetry.
#[inline]
pub fn mix_batch_header_digests(left: TranscriptHeader, right: TranscriptHeader) -> u64 {
    let d_left: u64 = fold_header_digest(left);
    let d_right: u64 = fold_header_digest(right);
    (d_left ^ (d_right >> 16u64)).wrapping_add(left.domain_tag + right.domain_tag)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn transcript_header_framing_and_digest() {
        let h = build_transcript_header(0x1111_2222_3333_4444u64, 0u64);
        assert!(verify_header_version(h));
        assert_eq!(h.domain_tag, SEQUENCER_DOMAIN_TAG);
        assert_eq!(h.payload_low32, 0x3333_4444u64);
        assert!(fold_header_digest(h) > 0u64);

        let h_custom = build_transcript_header(42u64, 0x7Bu64);
        assert_eq!(h_custom.domain_tag, 0x7Bu64);
        assert!(mix_batch_header_digests(h, h_custom) > 0u64);
    }
}
