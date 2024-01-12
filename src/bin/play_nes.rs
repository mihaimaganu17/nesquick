use nesquick::{reader::Reader, nes::INes, emulator::Emulator};
use std::time::Duration;

fn main() {
    let path = "/Users/ace/magic/nesquick/testdata/cpu_dummy_reads.nes";
    let data = std::fs::read(path).expect("Failed to read file from disk");
    let mut reader = Reader::new(data);
    let ines = INes::parse(&mut reader).expect("Failed to parse INes");

    let mut emu = Emulator::new();
    emu.load_nes(ines).expect("Failed to load file in Emulator");
}
