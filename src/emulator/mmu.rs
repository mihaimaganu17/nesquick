use core::ops::Range;

/// Represents the NES CPU memory management unit.
// Why we are not using a Vec directly? Simply because we want to control the
// indexing and the maximum fixed size.
#[derive(Debug)]
pub struct CpuMmu {
    // Size
    size: usize,
    // Data
    data: Vec<u8>,
}

impl CpuMmu {
    pub fn with_size(size: usize) -> Self {
        // Initialize the data
        let mut data = Vec::with_capacity(size);
        // Fill it with zeros
        data.resize(size, 0);

        CpuMmu {
            size,
            data,
        }
    }

    /// Sets the received `bytes` at the specified `offset` in the memory unit
    pub fn set_bytes(
        &mut self,
        offset: usize,
        bytes: &[u8]
    ) -> Result<(), CpuMmuError> {
        // Define a range, which is easier to work with
        let range = offset..(offset + bytes.len());

        // Set that specific range with the given bytes
        self.data.get_mut(range.clone())
            .ok_or(CpuMmuError::OutOfBoundsAccess(range))?
            .clone_from_slice(bytes);

        // If the size of the bytes is only 16KB, or even less(which should not
        // happen, but we don't take chances)
        // AND
        // If the offset is at 0x8000, we know that we have a ROM and we have
        // to load it at $8000-$bfff and $c000-$ffff
        if bytes.len() <= (16 * 1024) && offset == 0x8000 {
            // Define another range, that mirrors the address
            let range_mirror = 0xc000..(0xc000 + bytes.len());
            self.data[range_mirror].clone_from_slice(bytes);
        }

        Ok(())
    }

    /// Sets each byte in the given `range` of memory to the specified `value`.
    pub fn set_with_value(
        &mut self,
        range: Range<usize>,
        value: u8,
    ) -> Result<(), CpuMmuError> {
        // Set that specific range with the given bytes
        self.data.get_mut(range.clone())
            .ok_or(CpuMmuError::OutOfBoundsAccess(range.clone()))?
            .clone_from_slice(
                &std::iter::repeat(value).take(range.end).collect::<Vec<u8>>()
            );
        Ok(())
    }

    /// Read a u16, with Little Endian at the specified `addr`
    pub fn read_u16_le(&self, addr: usize) -> Option<u16> {
        // Read 2 bytes from the address
        let bytes = self.data.get(addr..(addr + 2))?;
        // Convert them into a u16 value
        let value = u16::from_le_bytes(bytes.try_into().ok()?);
        // Return that value
        Some(value)
    }

    /// Read a byte at the specified `addr`
    pub fn read_u8(&self, addr: usize) -> Option<u8> {
        self.data.get(addr).copied()
    }
}

#[derive(Debug)]
pub enum CpuMmuError {
    OutOfBoundsAccess(Range<usize>),
}
