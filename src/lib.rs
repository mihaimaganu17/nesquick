mod reader;
mod parser;

#[cfg(test)]
mod test {
    use crate::reader::Reader;
    use crate::parser::INes;

    #[test]
    fn works() {
        assert!(2 + 2 == 4);
    }

    #[test]
    fn parse_ines() {
        let path = "testdata/cpu_dummy_reads.nes";
        let data = std::fs::read(path).expect("Failed to read file from disk");
        let mut reader = Reader::new(data);
        INes::parse(&mut reader).expect("Failed to parse INes");
    }
}
