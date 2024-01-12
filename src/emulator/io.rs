use sdl2::{
    pixels::{Color, PixelFormatEnum},
    render::{Canvas,TextureValueError, UpdateTextureError},
    video::{Window, WindowBuildError},
    rect::{Rect, Point},
    keyboard::Keycode,
    event::Event,
    EventPump,
    IntegerOrSdlError,
};
use core::time::Duration;

pub struct LivingRoomTV {
    canvas: Canvas<Window>,
    event_pump: EventPump,
}

impl LivingRoomTV {
    /// Initialize the canvas which we will draw onto
    pub fn init() -> Result<Self, LivingRoomTVError> {
        // Initialize the SDL library
        let sdl_context = sdl2::init()?;

        // Initialize the video subsystem
        let video_subsystem = sdl_context.video()?;

        // Create a window which is essentially our TV mainframe.
        let window = video_subsystem
            .window("X", 800, 800).build()?;

        // We need to convert the window into a `Canvas` since we cannot draw
        // directly on the window
        let mut canvas: Canvas<Window> = window.into_canvas()
            // This means the screen cannot render faster than your display
            // rate (usually 60Hz or 144Hz)
            .present_vsync()
            .build()?;

        canvas.clear();
        canvas.present();

        let event_pump = sdl_context.event_pump()?;

        Ok(Self {
            canvas,
            event_pump,
        })
    }

    pub fn add_texture(
        &mut self,
        data: &[u8],
        x: i32,
        y: i32,
        width: u32,
        height: u32,
    ) -> Result<(), LivingRoomTVError> {
        // Initialize a texture creator
        let mut texture_creator = self.canvas.texture_creator();
        // Create a streaming texture, which is a way of saying to SDL that we
        // will update this texture frequently.
        let mut texture = texture_creator
            .create_texture_streaming(PixelFormatEnum::RGB24, width, height)?;
        // Update the new texture with the `data` passed by to the function.
        // We want to update the entire texture, so we pass `None` and since
        // a pixel is represented by 3 bytes, our `pitch` is 3 times the width
        texture.update(None, data, (width * 3) as usize)?;

        println!("rendering at x: {}, y: {}", x, y);

        // Now we add the texture to the canvas
        self.canvas.copy(&texture, None, Some(Rect::new(x, y, width, height)))?;
        //self.canvas.present();

        Ok(())
    }

    pub fn render_frame(&mut self) -> Result<(), LivingRoomTVError> {
        // Fills the canvas with the color we set in `set_draw_color`.
        // Essentially it blacks out the entire screen.
        // self.canvas.clear();

        // Change the color of our drawing with an orange-color
        //self.canvas.set_draw_color(Color::RGB(173, 0xA5, 0x00));
        // Draw a rectangle which almost fills our window with it!
        //self.canvas.fill_rect(Rect::new(10, 10, 700, 500));

        // However the canvas has not been updated to the window yet,
        // // everything has been processed to an internal buffer,
        // // but if we want our buffer to be displayed on the window,
        // // we need to call `present`. We need to call this every time
        // // we want to render a new frame on the window.
        // self.canvas.present();
        // // present does not "clear" the buffer, that means that
        // // you have to clear it yourself before rendering again,
        // // otherwise leftovers of what you've renderer before might
        // // show up on the window !
        // //
        // // A good rule of thumb is to `clear()`, draw every texture
        // // needed, and then `present()`; repeat this every new frame.

        /*
        texture.with_lock(None, |buffer: &mut [u8], pitch: usize| {
            // `pitch` is the length of row of pixels in bytes.
            for y in 0..256 {
                for x in 0..256 {
                    // There a are 3 bytes for each pixel because it is RGB
                    let offset  = y * pitch + x * 3;
                    buffer[offset] = x as u8;
                    buffer[offset + 1] = y as u8;
                    buffer[offset + 2] = 0;
                }
            }
        })?;
        */

        //let mut buffer = [0; 256 * 256 * 3];

        /*
        // `pitch` is the length of row of pixels in bytes.
        for y in 0..256 {
            for x in 0..256 {
                // There a are 3 bytes for each pixel because it is RGB
                let offset  = y * pitch + x * 3;
                buffer[offset] = x as u8;
                buffer[offset + 1] = y as u8;
                buffer[offset + 2] = 0;
            }
        }*/

        //self.canvas.clear();

        /*
        let mut x = 0;
        let mut y = 0;

        println!("Data {:#?}", data.len());
        while let Some(color) = data.get(8*y + x) {
            let color = *color;
            self.canvas.set_draw_color(Color::RGB(color, color, color));
            let point = Point::new(x as i32, y as i32);
            println!("Points {point:?}");
            self.canvas.draw_point(point)?;

            x += 1;

            if x % 8 == 0 {
                y += 1;
                x = 0;
            }
            self.canvas.clear();
            self.canvas.present();
        }*/

        'running: loop {
            for event in self.event_pump.poll_iter() {
                match event {
                    Event::Quit { .. }
                    | Event::KeyDown {
                        keycode: Some(Keycode::Escape),
                        ..
                    } => break 'running,
                    _ => {

                    }
                }
            }
            self.canvas.present();
            std::thread::sleep(Duration::new(100, 0));
            // The rest of the game loop goes here...
        }

        Ok(())
    }
}

#[derive(Debug)]
pub enum LivingRoomTVError {
    Sdl2Error(String),
    WindowBuildError(WindowBuildError),
    IntegerOrSdlError(IntegerOrSdlError),
    TextureValueError(TextureValueError),
    UpdateTextureError(UpdateTextureError),
}

impl From<String> for LivingRoomTVError {
    fn from(err: String) -> Self {
        Self::Sdl2Error(err)
    }
}

impl From<WindowBuildError> for LivingRoomTVError {
    fn from(err: WindowBuildError) -> Self {
        Self::WindowBuildError(err)
    }
}

impl From<IntegerOrSdlError> for LivingRoomTVError {
    fn from(err: IntegerOrSdlError) -> Self {
        Self::IntegerOrSdlError(err)
    }
}

impl From<TextureValueError> for LivingRoomTVError {
    fn from(err: TextureValueError) -> Self {
        Self::TextureValueError(err)
    }
}

impl From<UpdateTextureError> for LivingRoomTVError {
    fn from(err: UpdateTextureError) -> Self {
        Self::UpdateTextureError(err)
    }
}
