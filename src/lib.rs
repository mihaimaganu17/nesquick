mod reader;
mod nes;
mod emulator;

#[cfg(test)]
mod test {
    use crate::reader::Reader;
    use crate::nes::INes;

    #[test]
    fn works() {
        assert!(2 + 2 == 4);
    }

    //#[test]
    fn parse_ines() {
        let path = "testdata/cpu_dummy_reads.nes";
        let data = std::fs::read(path).expect("Failed to read file from disk");
        let mut reader = Reader::new(data);
        let ines = INes::parse(&mut reader).expect("Failed to parse INes");

        // Check that we read all bytes from the file
        assert!(0 == reader.bytes_left());
        assert!(ines.trainer().is_none());

        println!("INes {:#?}", ines.header());
        //println!("PRG rom {:#?}", ines.prg_rom().get(0..50));
    }
    #[test]
    fn ppu_color_test() {
        let path = "testdata/color_test.nes";
        let data = std::fs::read(path).expect("Failed to read file from disk");
        let mut reader = Reader::new(data);
        let ines = INes::parse(&mut reader).expect("Failed to parse INes");

        // Check that we read all bytes from the file
        assert!(0 == reader.bytes_left());
        assert!(ines.trainer().is_none());

        println!("INes {:#?}", ines.header());
        //println!("PRG rom {:#?}", ines.prg_rom().get(0..50));
    }
}
