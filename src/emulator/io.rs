use sdl2::{
    pixels::{PixelFormatEnum},
    render::{Canvas,TextureValueError, UpdateTextureError},
    video::{Window, WindowBuildError},
    rect::{Rect},
    keyboard::Keycode,
    event::Event,
    EventPump,
    IntegerOrSdlError,
};

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
            .window("X", 800, 800)
            .build()?;

        // We need to convert the window into a `Canvas` since we cannot draw
        // directly on the window
        let mut canvas: Canvas<Window> = window.into_canvas()
            // This means the screen cannot render faster than your display
            // rate (usually 60Hz or 144Hz)
            //.present_vsync()
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

        Ok(())
    }

    pub fn render_frame(&mut self) -> Result<(), LivingRoomTVError> {
        // Display the frame
        self.canvas.present();

        // Wait for events so that the window shows up
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
