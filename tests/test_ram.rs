use my_cpu::ram::{RAM, RamAddr};


/// These tests test [`RAM`]
#[cfg(test)]
mod tests {
    use super::{*};

    #[test]
    #[should_panic]
    fn test_no_space() {
        let mut ram = RAM::new(16);
        ram.allocate(17).unwrap();
    }

    #[test]
    fn test_general_alloc_free() {
        let mut ram = RAM::new(16);

        let start = ram.allocate(16).unwrap();

        assert_eq!(ram.free_size(), 0);
        ram.free(start, 16).unwrap();
        assert_eq!(ram.used_size(), 0);

        ram.allocate(8).unwrap();
        ram.allocate(8).unwrap();
        assert_eq!(ram.free_size(), 0);
    }

    #[test]
    fn test_contagious_alloc_free() {
        let mut ram = RAM::new(16);
        let start1 = ram.allocate(8).unwrap();
        let start2 = ram.allocate(8).unwrap();

        assert_eq!(start2, start1.add(8).unwrap());

        assert_eq!(ram.used_size(), 16);
        assert_eq!(ram.free_size(), 0);

        ram.free(start1, 8).unwrap();
        assert_eq!(ram.free_size(), 8);
        assert_eq!(ram.used_size(), 8);

        ram.free(start2, 8).unwrap();
        assert_eq!(ram.free_size(), 16);
    }

    #[test]
    fn test_alloc_free_numbers() {
        const SIZE: usize = (1 + 2 + 4 + 8 + 16) * 2;

        let mut ram = RAM::new(SIZE);

        let u1 = ram.alloc_u8(u8::MAX).unwrap();
        let u2 = ram.alloc_u16(u16::MAX).unwrap();
        let u3 = ram.alloc_u32(u32::MAX).unwrap();
        let u4 = ram.alloc_u64(u64::MAX).unwrap();
        let u5 = ram.alloc_u128(u128::MAX).unwrap();

        let i1 = ram.alloc_i8(i8::MIN).unwrap();
        let i2 = ram.alloc_i16(i16::MIN).unwrap();
        let i3 = ram.alloc_i32(i32::MIN).unwrap();
        let i4 = ram.alloc_i64(i64::MIN).unwrap();
        let i5 = ram.alloc_i128(i128::MIN).unwrap();

        assert_eq!(ram.used_size(), SIZE);

        ram.free(u1, 1).unwrap();
        ram.free(u2, 2).unwrap();
        ram.free(u3, 4).unwrap();
        ram.free(u4, 8).unwrap();
        ram.free(u5, 16).unwrap();

        ram.free(i5, 16).unwrap();
        ram.free(i4, 8).unwrap();
        ram.free(i3, 4).unwrap();
        ram.free(i2, 2).unwrap();
        ram.free(i1, 1).unwrap();

        assert_eq!(ram.free_size(), SIZE);
    }

    #[test]
    fn test_alloc_at_1() {
        let mut ram = RAM::new(16);
        ram.allocate_at(8, RamAddr(8)).unwrap();
        ram.allocate(8).unwrap();

        assert_eq!(ram.free_size(), 0);
        ram.free(RamAddr(0), 16).unwrap();
        assert_eq!(ram.used_size(), 0);
    }

    #[test]
    #[should_panic]
    fn test_alloc_at_2() {
        let mut ram = RAM::new(24);
        // Start:
        //          24
        // ........................

        ram.alloc_u64(u64::MAX).unwrap();

        // Now should be:
        //    8           16
        // ########................
        //    ^ u64

        ram.allocate_at(8, RamAddr(13)).unwrap();
        // Now should be:
        //    8           16
        // ########.....########...
        //    ^ u64        ^ 8 bytes

        ram.alloc_u64(u64::MAX).unwrap(); // Should panic, no free contagious 8 bytes
    }

    #[test]
    #[should_panic]
    fn test_alloc_at_3() {
        let mut ram = RAM::new(16);
        ram.allocate_at(9, RamAddr(8)).unwrap();
    }
}

