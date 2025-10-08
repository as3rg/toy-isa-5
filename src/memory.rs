use std::collections::HashMap;

use crate::globals::{ExecResult, Utarget};

pub const PAGE_SIZE: Utarget = 4096;
pub type Page = [u8; PAGE_SIZE as _];

#[derive(Default, Debug)]
pub struct Memory {
    pages: HashMap<Utarget, Box<Page>>,
}

impl Memory {
    pub fn decompose(addr: Utarget) -> (Utarget, Utarget) {
        const MASK: Utarget = PAGE_SIZE - 1;
        (addr & !MASK, addr & MASK)
    }

    pub fn read(&self, addr: Utarget, buf: &mut [u8]) -> ExecResult {
        if buf.is_empty() {
            return Ok(());
        }

        let (page_addr, page_offset) = Self::decompose(addr);
        let cnt = ((PAGE_SIZE - page_offset) as usize).min(buf.len());
        let (dst_buf, dst_buf_other) = buf.split_at_mut(cnt);

        if let Some(page) = self.pages.get(&page_addr) {
            dst_buf.copy_from_slice(&page[(page_offset as _)..][..cnt]);
        } else {
            dst_buf.fill(0);
        }

        self.read(page_addr + PAGE_SIZE, dst_buf_other)
    }

    pub fn write(&mut self, addr: Utarget, buf: &[u8]) -> ExecResult {
        if buf.is_empty() {
            return Ok(());
        }

        let (page_addr, page_offset) = Self::decompose(addr);
        let page = self
            .pages
            .entry(page_addr)
            .or_insert_with(|| Box::new([0; PAGE_SIZE as _]));

        let cnt = ((PAGE_SIZE - page_offset) as usize).min(buf.len());
        let (src_buf, src_buf_other) = buf.split_at(cnt);
        page[(page_offset as _)..][..cnt].copy_from_slice(src_buf);

        self.write(page_addr + PAGE_SIZE, src_buf_other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_read_write() {
        let mut mem = Memory::default();
        const ADDR: Utarget = 1234;
        const SIZE: usize = 6;

        let buf: [u8; SIZE] = [0, 1, 2, 3, 4, 5];
        assert!(mem.write(ADDR, &buf).is_ok());

        let mut buf2 = [0u8; SIZE];
        assert!(mem.read(ADDR, &mut buf2).is_ok());
        assert_eq!(buf, buf2);
    }

    #[test]
    fn test_write_multipage() {
        let mut mem = Memory::default();
        const ADDR: Utarget = 1234;
        const SIZE: usize = PAGE_SIZE as usize * 3;

        let buf: [u8; SIZE] = core::array::from_fn(|i| (i + 1) as u8);
        assert!(mem.write(ADDR, &buf).is_ok());

        for (i, x) in buf.iter().copied().enumerate() {
            let mut buf2 = [0];
            assert!(mem.read(ADDR + i as Utarget, &mut buf2).is_ok());
            assert_eq!(buf2[0], x);
        }
    }

    #[test]
    fn test_read_multipage() {
        let mut mem = Memory::default();
        const ADDR: Utarget = 1234;
        const SIZE: usize = PAGE_SIZE as usize * 3;

        let buf: [u8; SIZE] = core::array::from_fn(|i| (i + 1) as u8);
        for (i, x) in buf.iter().copied().enumerate() {
            assert!(mem.write(ADDR + i as Utarget, &[x]).is_ok());
        }

        let mut buf2 = [0u8; SIZE];
        assert!(mem.read(ADDR, &mut buf2).is_ok());
        assert_eq!(buf, buf2);
    }
}
