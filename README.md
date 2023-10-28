# Big question: What system do we want to emulate?

# NES
## General information
First sold as Famicon on 1983
8-bit third generation console
CPU: Ricoh 2A03, at 1.79 MHz with 2 KBs of RAM.

## Main components
- Ricoh 2A03 CPU based on the 6502 8-bit microprocessor
- 2 KiB of RAM for use by the CPU
- 2C02 PPU (picture processing unit)
- 2 KiB of RAM for use by the PPU
- Cartridges (game hardware packs)

## ROM images

## CPU -> Ricoh 2A03
[NES CPU](https://www.nesdev.org/wiki/CPU)
The NES CPU core is based on the 6502 processor and runs at appoximately 1.79 MHz. Lack the
MOS6502's decimal mode. It also integrates:
- An APU (audio processing unit) featuring 22 Memory-mapped I/0 registers
- audio output comprising four tone generators and a delta modulation playback device
- DMA(Direct Memory Access)
- Game controller polling / serial input for game controllers
[CPU Memory Map](https://www.nesdev.org/wiki/CPU_memory_map)

## Hardware extensions
- Family Computer Disk System(FDS): Offered slighly higher data storage and slighly enhanced sound
  processing.
- MMC: Solved all the NES problems with [bank
  switching](https://en.wikipedia.org/wiki/Bank_switching)

## Memory
2 KiB of RAM for use by the PPU

## Mappers
Mappers or Memory Management Controllers(MMC):
- No mapper
- Official mappers: UNROM, AOROM, MMC1-6
- Third-party mappers: VRC6/VRC7 from Konami

## Disk Support
Games dumped off the Famicom Disk System come into 2 major types:
- .fds format: Most common format. Ubiquitous in ROM sets(GoodSet, No-Intro). Omits some checksum
  data
    - [Family Computer Disk System](https://www.nesdev.org/wiki/Family_Computer_Disk_System)
    - [FDS file format](https://www.nesdev.org/wiki/FDS_file_format)
    - [FDS disk format](https://www.nesdev.org/wiki/FDS_disk_format)
    - [FDS BIOS](https://www.nesdev.org/wiki/FDS_BIOS)

## NES PPU -> 2C02
[PPU](https://www.nesdev.org/wiki/PPU)
The NES Picture Processing Unit(PPU) generates a composite video signal with 240 lines of pixels.
[PPU power up state](https://www.nesdev.org/wiki/PPU_power_up_state)
Features:
- tile-based background image
- 64 sprites (individually moving objects)
- 25 colors out of 53
- 256x240 pixel progressive picture generator
- NTSC color encoder

## Cartridges -> Kind of like Diskettes with programs
16 KiB or more PRG ROM, for use by the CPU
8 KiB or more CHR ROM or CHR RAM, for use the PPU
(optional) Bank switching hardware for the ROMs
(optional) Logic to generate interrupts

# NES Emulators
Most accurate NES emulator is [Messen](https://emulation.gametechwiki.com/index.php/Mesen)
List of other contenders:
- puNES
- Messen2
- Nestopia
- Nintendulator
[NES
Emulators](https://emulation.gametechwiki.com/index.php/Nintendo_Entertainment_System_emulators)
[3rd generation computers]()


# Internet resources
[First and second generations of video game
consoles](https://emulation.gametechwiki.com/index.php/First_and_second_generations_of_video_game_consoles)


# Already developed systems
[MAME](https://www.mamedev.org/)
[x86 List from
EmuGen](https://emulation.gametechwiki.com/index.php/POS_(Pong_Consoles)_CPUs_and_Other_Chips)

