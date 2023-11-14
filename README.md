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

[Opcode Matrix](http://www.oxyron.de/html/opcodes02.html)

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

# Pins
Aha moment:
A series of pins are just a way for 2 devices to connect and communicate with each other.
[PPU Pinout](https://www.nesdev.org/wiki/PPU_pinout)
[Cartridge connector](https://www.nesdev.org/wiki/Cartridge_connector)

# Registers

## CPU Registers
Same as for the 6502.
1. Accumulator (A) - byte-wide and along with the arithmetic logic unit (ALU), supports using the
   status register for carrying, overflow detection, etc.
2. X and Y are byte-wide and used for several addressing modes. They can be used as loop counters
   easily, using INC/DEC and branch instructions.
3. Program Counter (PC) - supports 65536 direct (unbanked) memory location, however not all values
   are sent to the cartridge. It can be accessed either by allowing CPU's internal fetch logic
   increment the address bus, and interrupt (NMI, Reset, IRQ/BRQ) and using the RTS/JMP/JSR/Branch
   instructions.
4. Stack pointer (S) is byte-wide and can be accessed using interrupts, pull, pushes and transfers.
   It indexes into a 256-byte stack at $0100 - $01FF.
5. Status Register (P) has 6 bits used by the ALU but is byte-wide. PHP, PLP, arithmetic, testing
   and branch instructions can access this register.

## PPU Registers
[PPU Registers](https://www.nesdev.org/wiki/PPU_registers)
The PPU exposes 8 memory-mapped registers to the CPU. These nominally sit at $2000 through $2007 in
the CPU's address space, but because they're incompletely decoded, they're mirrored in every 8
bytes from $2008 through $3FFF, so a write to $3456 is the same as a write to $2006.
[PPU power up state](https://www.nesdev.org/wiki/PPU_power_up_state)

The PPU has an internal data bus that it uses for communication with the CPU. This bus, behaves as
an 8-bit dynamic latch due to capacitance of very long traces that run in various parts of the PPU.
Writing any value to any PPU port, even to read-only PPUSTATUS, will fill this latch.
Reading any readable port: PPUSTATUS, OAMDATA or PPUDATA) also fills the latch with the bits read.
Reading a nominally "write-only" register returns the latch's current value, as do the unused bits
of PPUSTATUS.

Accesses as marked as: Can write to, read to register 1. 2., etc
1. Controller - PPUCTRL - write, address $2000
2. Mask - PPUMASK - write, address $2001
3. Status - PPUSTATUS - read, address $2002
4. Objet attribute memory address - OAMADDR - write, address $2003. Write the address of OAM you
   want to access here.
5. OAM Data - OAMDATA - read/write, address $2004. Write OAM data here. Writes will increment
   OAMADDR after the write; reads do not.
6. Scroll - PPUSCROLL - write x2(twice), address $2005. This register is used to change the scroll position,
   telling the PPU which pixel of the nametable selected through PPUCTRL should be at the top left
   corner of the rendered screen. Typically, this register is written to during vertical blanking to
   make the next frame start rendering from the desired location, but it can also be modified
   during rendering in order to split the screen.
7. Address - PPUADDR - write x2(twice), address $2006. Because the CPU and the PPU are on separate
   buses, neither has direct access to the othre's memory. The CPU writes to VRAM through a pair of
   registers on the PPU. First it loads the address into PPUADDR and then it write repeatedly to
   PPUDATA to fill VRAM. Valid addressed are $0000-$3FFF; higher addresses will be mirrored down.
8. Data - PPUDATA - read/write, address $2007. VRAM read/write data register. After access, the
   video memory address will increment by an amount determined by bit 2 of $2000.
5b. OAM DMA - OAMDMA - write. This porst is located on the CPU. Writing $XX will upload 256 bytes of
data from CPU page $XX00-$XXFF to the internal PPU OAM. This page is typically located in internal
RAM, commonly $0200-$02FF, but cartridhe RAM or ROM can be used as well.

## Vertical blanking

## PPU Nametables
[PPU Nametables](https://www.nesdev.org/wiki/PPU_nametables)

# Sprites
[Sprite size](https://www.nesdev.org/wiki/Sprite_size)

[Visual Simulators](https://www.nesdev.org/wiki/Visual_2C02)
[Mirroring](https://www.nesdev.org/wiki/Mirroring#Memory_Mirroring)

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

