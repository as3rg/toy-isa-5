use std::iter::zip;

use crate::globals::{Itarget, Utarget};

pub fn bit_deposit(value: Utarget, mask: Utarget) -> Utarget {
    let positions = (0..Utarget::BITS)
        .into_iter()
        .filter(|x| ((mask & (1 << x)) != 0));
    let values = (0..Utarget::BITS)
        .into_iter()
        .map(|x| ((value & (1 << x)) != 0));

    zip(positions, values)
        .map(|(pos, val)| ((val as Utarget) << pos))
        .sum()
}

pub fn saturate_signed(value: Itarget, bits: Utarget) -> Itarget {
    assert!(bits <= Itarget::BITS);
    let min_bound = Itarget::min_value().unbounded_shr(Itarget::BITS - bits);
    let max_bound = Itarget::max_value().unbounded_shr(Itarget::BITS - bits);
    value.clamp(min_bound, max_bound)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bit_deposit() {
        let params: &[(Utarget, Utarget, Utarget)] = &[
            (239, 0, 0),
            (0, 239, 0),
            (0xffffffff, 0, 0),
            (0, 0xffffffff, 0),
            (0b101010, 0b010101, 0b000100),
            (0b101, 0b1001001, 0b1000001),
            (0x239, 0xffffffff, 0x239),
            (0x239, 0x00ff00ff, 0x20039),
        ];
        for (value, mask, expected) in params.into_iter().copied() {
            assert_eq!(bit_deposit(value, mask), expected);
        }
    }

    #[test]
    fn test_saturate_signed() {
        let params: &[(Itarget, Utarget, Itarget)] = &[
            (Itarget::MIN, 32, -2147483648),
            (Itarget::MAX, 32, 2147483647),
            (Itarget::MIN, 31, -1073741824),
            (Itarget::MAX, 31, 1073741823),
            (Itarget::MIN, 16, -32768),
            (Itarget::MAX, 16, 32767),
            (Itarget::MIN, 2, -2),
            (Itarget::MAX, 2, 1),
            (Itarget::MIN, 1, -1),
            (Itarget::MAX, 1, 0),
            (Itarget::MIN, 0, -1),
            (Itarget::MAX, 0, 0),
        ];
        for (value, bits, expected) in params.into_iter().copied() {
            assert_eq!(saturate_signed(value, bits), expected);
        }
    }
}
