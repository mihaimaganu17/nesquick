mod emulator;
mod nes;
mod reader;

#[cfg(test)]
mod test {
    use crate::nes::INes;
    use crate::reader::Reader;

    //#[test]
    fn parse_ines() {
        let path = "testdata/cpu_dummy_reads.nes";
        let data = std::fs::read(path).expect("Failed to read file from disk");
        let mut reader = Reader::new(data);
        let ines = INes::parse(&mut reader).expect("Failed to parse INes");

        // Check that we read all bytes from the file
        assert!(0 == reader.bytes_left());
        assert!(ines.trainer().is_none());

        //println!("INes {:#?}", ines.header());
    }

    //#[test]
    fn ppu_color_test() {
        let path = "testdata/color_test.nes";
        let data = std::fs::read(path).expect("Failed to read file from disk");
        let mut reader = Reader::new(data);
        let ines = INes::parse(&mut reader).expect("Failed to parse INes");

        // Check that we read all bytes from the file
        assert!(0 == reader.bytes_left());
        assert!(ines.trainer().is_none());

        println!("INes {:#x?}", ines.header());
    }
}
