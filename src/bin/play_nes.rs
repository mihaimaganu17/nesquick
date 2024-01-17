use nesquick::{reader::Reader, nes::INes, emulator::Emulator, emulator::LivingRoomTV};
use std::time::Duration;

fn main() {
    let path = "/Users/ace/magic/nesquick/testdata/cpu_dummy_reads.nes";
    let data = std::fs::read(path).expect("Failed to read file from disk");
    let mut reader = Reader::new(data);
    let ines = INes::parse(&mut reader).expect("Failed to parse INes");

    let mut emu = Emulator::new();

    let mut lr_tv = LivingRoomTV::init()
        .expect("Failed to install Living Room TV");
    emu.load_nes(ines, Some(&mut lr_tv)).expect("Failed to load file in Emulator");
}
