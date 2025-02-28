use my_cpu::ram::RamAddr;


/// These tests test [`RamAddr`]
#[cfg(test)]
mod tests {
    use super::{*};

    #[test]
    fn test_operations() {
        let mut addr = RamAddr(0);
        addr.inc(10).unwrap();
        assert_eq!(addr, RamAddr(10));
        addr.dec(10).unwrap();
        assert_eq!(addr, RamAddr(0));
    }
    
    #[test]
    #[should_panic]
    fn test_add_addr() {
        let addr = RamAddr(usize::MAX);
        addr.add(1usize).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_inc_addr() {
        let mut addr = RamAddr(usize::MAX);
        addr.inc(1usize).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_sub_addr() {
        let addr = RamAddr(usize::MIN);
        addr.sub(1usize).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_dec_addr() {
        let mut addr = RamAddr(usize::MIN);
        addr.dec(1usize).unwrap();
    }
}

