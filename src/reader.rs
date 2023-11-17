/// Represents a safe structure that reads and parses the underlying buffer
pub struct Reader {
    // Current position of the cursor inside the buffer
    pos: usize,
    // The buffer that owns the data
    data: Vec<u8>,
}

impl Reader {
    pub fn new(data: Vec<u8>) -> Self {
        Self { pos: 0, data }
    }

    pub fn read_bytes(&mut self, nbytes: usize) -> Result<&[u8], ReaderError> {
        // Get the desired slice from the buffer
        let Some(bytes) = self.data.get(self.pos..self.pos + nbytes) else {
            return Err(ReaderError::OutOfBounds(RangeToRead::from(self.pos, self.data.len(), nbytes)));
        };
        // Increment the position by the amount of read bytes
        self.pos += nbytes;
        // Return the slice
        Ok(bytes)
    }

    pub fn read<P: PrimitiveFromBytes, E: Endianness>(&mut self) -> Result<P, ReaderError> {
        // Read the ammount of bytes needed
        let bytes = self.read_bytes(std::mem::size_of::<P>())?;

        let primitive = match E::endian() {
            Endian::Big => P::from_bytes_be(bytes)?,
            Endian::Little => P::from_bytes_le(bytes)?,
        };

        Ok(primitive)
    }
}

// Type of endian we can parse
#[derive(Debug)]
enum Endian {
    Little,
    Big,
}

// Handy trait we use to sugar coat the `read` function from the `Reader`
trait Endianness {
    fn endian() -> Endian;
}

/// Represent a Big Endiannes encoding
#[derive(Debug)]
pub struct BE;
/// Represent a Little Endiannes encoding
#[derive(Debug)]
pub struct LE;

impl Endianness for BE {
    fn endian() -> Endian { Endian::Big }
}

impl Endianness for LE {
    fn endian() -> Endian { Endian::Little }
}

/// Implementors of this trait are able to utilize the `Reader` interface to be parsed directly
/// from the buffer in a safe and clean manner.
pub trait PrimitiveFromBytes: Sized {
    fn from_bytes_le(bytes: &[u8]) -> Result<Self, ReaderError>;
    fn from_bytes_be(bytes: &[u8]) -> Result<Self, ReaderError>;
}

impl PrimitiveFromBytes for u8 {
    fn from_bytes_le(bytes: &[u8]) -> Result<Self, ReaderError> {
        // For u8 there is no difference between the way we parse the endianness
        Self::from_bytes_be(bytes)
    }
    fn from_bytes_be(bytes: &[u8]) -> Result<Self, ReaderError> {
        let size = std::mem::size_of::<Self>();
        let Some(value) = bytes.get(0) else {
            return Err(ReaderError::OutOfBounds(RangeToRead::from(0, bytes.len(), size)));
        };
        Ok(*value)
    }
}

#[derive(Debug)]
pub enum ReaderError {
    /// Returned when trying to access data outside of the buffer's limits.
    OutOfBounds(RangeToRead),
}

/// Represents a buffer range inside which we want to access and the according number of bytes we
/// want to access
//We could also use `core::ops::Range<T>` but that would just complicate things.
#[derive(Debug)]
pub struct RangeToRead {
    // Start of the buffer that is accessed
    start: usize,
    // End of the buffer that is accessed
    end: usize,
    // Number of bytes we want to read from the buffer
    nbytes: usize,
}

impl RangeToRead {
    // We could implement the `From` trait, but we would have to pass a tuple, which is a annoying
    pub fn from(start: usize, end: usize, nbytes: usize) -> Self {
        Self { start, end, nbytes }
    }
}
