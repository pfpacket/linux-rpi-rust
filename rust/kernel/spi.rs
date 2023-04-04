// SPDX-License-Identifier: GPL-2.0

//! This module provides safer and higher level abstraction over the kernel's SPI types
//! and functions.
//!
//! C header: [`include/linux/spi/spi.h`](../../../../include/linux/spi/spi.h)

use crate::bindings;
use crate::error::{code::*, Error, Result};
use crate::str::CStr;
use alloc::boxed::Box;
use core::pin::Pin;

/// Wrapper struct around the kernel's `spi_device`.
#[derive(Clone, Copy)]
pub struct SpiDevice(*mut bindings::spi_device);

impl SpiDevice {
    /// Create an [`SpiDevice`] from a mutable spi_device raw pointer. This function is unsafe
    /// as the pointer might be invalid.
    ///
    /// The pointer must be valid. This can be achieved by calling `to_ptr` on a previously
    /// constructed, safe `SpiDevice` instance, or by making sure that the pointer points
    /// to valid memory.
    ///
    /// You probably do not want to use this abstraction directly. It is mainly used
    /// by this abstraction to wrap valid pointers given by the Kernel to the different
    /// SPI methods: `probe`, `remove` and `shutdown`.
    pub unsafe fn from_ptr(dev: *mut bindings::spi_device) -> Self {
        SpiDevice(dev)
    }

    /// Access the raw pointer from an [`SpiDevice`] instance.
    pub fn to_ptr(&mut self) -> *mut bindings::spi_device {
        self.0
    }
}

/// Registration of an SPI driver.
pub struct DriverRegistration {
    this_module: &'static crate::ThisModule,
    registered: bool,
    name: &'static CStr,
    spi_driver: bindings::spi_driver,
}

/// Represents which methods of the SPI driver shall be implemented.
pub struct ToUse {
    /// The `probe` field of `spi_driver`.
    pub probe: bool,

    /// The `remove` field of `spi_driver`.
    pub remove: bool,

    /// The `shutdown` field of `spi_driver`.
    pub shutdown: bool,
}

/// Default table to use for SPI methods. All fields are set to false, meaning that the
/// kernel's default implementations will be used.
pub const USE_NONE: ToUse = ToUse {
    probe: false,
    remove: false,
    shutdown: false,
};

/// Corresponds to the kernel's spi_driver's methods. Implement this trait on a type to
/// express the need of a custom probe, remove or shutdown function for your SPI driver.
/// Use the [`declare_spi_methods`] macro to declare which methods you wish to use.
pub trait SpiMethods {
    /// The methods to define. Use [`declare_spi_methods`] to declare them.
    const TO_USE: ToUse;

    /// Corresponds to the kernel's `spi_driver`'s `probe` method field.
    fn probe(mut _spi_dev: SpiDevice) -> Result {
        Ok(())
    }

    /// Corresponds to the kernel's `spi_driver`'s `remove` method field.
    fn remove(mut _spi_dev: SpiDevice) {}

    /// Corresponds to the kernel's `spi_driver`'s `shutdown` method field.
    fn shutdown(mut _spi_dev: SpiDevice) {}
}

/// Populate the `TO_USE` field in the [`SpiMethods`] implementer.
///
/// # Examples
///
/// ```
/// impl SpiMethods for MySpiMethods {
///     /// Let's say you only want a probe and remove method, no shutdown.
///     declare_spi_methods!(probe, remove);
///
///     /// Define your probe and remove methods. If you don't, default implementations
///     /// will be used instead. These default implementations do *not* correspond to the
///     /// kernel's default implementations! If you wish to use the kernel's default
///     /// SPI functions implementations, do not declare them using the `declare_spi_methods`
///     /// macro. For example, here our driver will use the kernel's `shutdown` method.
///     fn probe(spi_dev: SpiDevice) -> Result {
///         // ...
///
///         Ok(())
///     }
///
///     fn remove(spi_dev: SpiDevice) -> Result {
///         // ...
///
///         Ok(())
///     }
/// }
/// ```
#[macro_export]
macro_rules! declare_spi_methods {
    () => {
        const TO_USE: $crate::spi::ToUse = $crate::spi::USE_NONE;
    };
    ($($method:ident),+) => {
        const TO_USE: $crate::spi::ToUse = $crate::spi::ToUse {
            $($method: true),+,
            ..$crate::spi::USE_NONE
        };
    };
}

impl DriverRegistration {
    fn new(this_module: &'static crate::ThisModule, name: &'static CStr) -> Self {
        DriverRegistration {
            this_module,
            name,
            registered: false,
            spi_driver: bindings::spi_driver::default(),
        }
    }

    /// Create a new `DriverRegistration` and register it. This is equivalent to creating
    /// a static `spi_driver` and then calling `spi_driver_register` on it in C.
    ///
    /// # Examples
    ///
    /// ```
    /// let spi_driver =
    ///     spi::DriverRegistration::new_pinned::<MySpiMethods>(&THIS_MODULE, cstr!("my_driver_name"))?;
    /// ```
    pub fn new_pinned<T: SpiMethods>(
        this_module: &'static crate::ThisModule,
        name: &'static CStr,
    ) -> Result<Pin<Box<Self>>> {
        let mut registration = Pin::from(Box::try_new(Self::new(this_module, name))?);

        registration.as_mut().register::<T>()?;

        Ok(registration)
    }

    unsafe extern "C" fn probe_wrapper<T: SpiMethods>(
        spi_dev: *mut bindings::spi_device,
    ) -> core::ffi::c_int {
        // SAFETY: The `spi_dev` pointer is provided by the kernel and is sure to be valid.
        match T::probe(unsafe { SpiDevice::from_ptr(spi_dev) }) {
            Ok(_) => 0,
            Err(e) => e.to_kernel_errno(),
        }
    }

    unsafe extern "C" fn remove_wrapper<T: SpiMethods>(spi_dev: *mut bindings::spi_device) {
        // SAFETY: The `spi_dev` pointer is provided by the kernel and is sure to be valid.
        T::remove(unsafe { SpiDevice::from_ptr(spi_dev) });
    }

    unsafe extern "C" fn shutdown_wrapper<T: SpiMethods>(spi_dev: *mut bindings::spi_device) {
        // SAFETY: The `spi_dev` pointer is provided by the kernel and is sure to be valid.
        T::shutdown(unsafe { SpiDevice::from_ptr(spi_dev) })
    }

    /// Register a [`DriverRegistration`]. This is equivalent to calling `spi_driver_register`
    /// on your `spi_driver` in C, without creating it first.
    fn register<T: SpiMethods>(self: Pin<&mut Self>) -> Result {
        // SAFETY: We do not move out of the reference we get, and are only registering
        // `this` once over the course of the module, since we check that the `registered`
        // field was not already set to true.
        let this = unsafe { self.get_unchecked_mut() };
        if this.registered {
            return Err(EINVAL);
        }

        this.spi_driver.driver.name = this.name.as_ptr() as *const core::ffi::c_char;
        this.spi_driver.probe = T::TO_USE
            .probe
            .then(|| DriverRegistration::probe_wrapper::<T> as _);
        this.spi_driver.remove = T::TO_USE
            .remove
            .then(|| DriverRegistration::remove_wrapper::<T> as _);
        this.spi_driver.shutdown = T::TO_USE
            .shutdown
            .then(|| DriverRegistration::shutdown_wrapper::<T> as _);

        // SAFETY: Since we are using a pinned `self`, we can register the driver safely as
        // if we were using a static instance. The kernel will access this driver over the
        // entire lifespan of a module and therefore needs a pointer valid for the entirety
        // of this lifetime.
        let res =
            unsafe { bindings::__spi_register_driver(this.this_module.0, &mut this.spi_driver) };

        if res != 0 {
            return Err(Error::from_kernel_errno(res));
        }

        this.registered = true;
        Ok(())
    }
}

impl Drop for DriverRegistration {
    fn drop(&mut self) {
        // SAFETY: We are simply unregistering an `spi_driver` that we know to be valid.
        // [`DriverRegistration`] instances can only be created by being registered at the
        // same time, so we are sure that we'll never unregister an unregistered `spi_driver`.
        unsafe { bindings::driver_unregister(&mut self.spi_driver.driver) }
    }
}

// SAFETY: The only method is `register()`, which requires a (pinned) mutable `Registration`, so it
// is safe to pass `&Registration` to multiple threads because it offers no interior mutability.
unsafe impl Sync for DriverRegistration {}

// SAFETY: All functions work from any thread.
unsafe impl Send for DriverRegistration {}

/// High level abstraction over the kernel's SPI functions such as `spi_write_then_read`.
pub struct Spi;

impl Spi {
    /// Corresponds to the kernel's `spi_write_then_read`.
    ///
    /// # Examples
    ///
    /// ```
    /// let to_write = "rust-for-linux".as_bytes();
    /// let mut to_receive = [0u8; 10]; // let's receive 10 bytes back
    ///
    /// // `spi_device` was previously provided by the kernel in that case
    /// let transfer_result = Spi::write_then_read(spi_device, &to_write, &mut to_receive);
    /// ```
    pub fn write_then_read(dev: &mut SpiDevice, tx_buf: &[u8], rx_buf: &mut [u8]) -> Result {
        // SAFETY: The `dev` argument must uphold the safety guarantees made when creating
        // the [`SpiDevice`] instance. It should therefore point to a valid `spi_device`
        // and valid memory. We also know that a rust slice will always contain a proper
        // size and that it is safe to use as is. Converting from a Rust pointer to a
        // generic C `void*` pointer is normal, and does not pose size issues on the
        // kernel's side, which will use the given Transfer Receive sizes as bytes.
        let res = unsafe {
            bindings::spi_write_then_read(
                dev.to_ptr(),
                tx_buf.as_ptr() as *const core::ffi::c_void,
                tx_buf.len() as core::ffi::c_uint,
                rx_buf.as_mut_ptr() as *mut core::ffi::c_void,
                rx_buf.len() as core::ffi::c_uint,
            )
        };

        match res {
            0 => Ok(()),                               // 0 indicates a valid transfer,
            err => Err(Error::from_kernel_errno(err)), // A negative number indicates an error
        }
    }

    /// Corresponds to the kernel's `spi_write`.
    ///
    /// # Examples
    ///
    /// ```
    /// let to_write = "rust-for-linux".as_bytes();
    ///
    /// // `spi_device` was previously provided by the kernel in that case
    /// let write_result = Spi::write(spi_device, &to_write);
    /// ```
    pub fn write(dev: &mut SpiDevice, tx_buf: &[u8]) -> Result {
        Spi::write_then_read(dev, tx_buf, &mut [0u8; 0])
    }

    /// Corresponds to the kernel's `spi_read`.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut to_receive = [0u8; 10]; // let's receive 10 bytes
    ///
    /// // `spi_device` was previously provided by the kernel in that case
    /// let transfer_result = Spi::read(spi_device, &mut to_receive);
    /// ```
    pub fn read(dev: &mut SpiDevice, rx_buf: &mut [u8]) -> Result {
        Spi::write_then_read(dev, &[0u8; 0], rx_buf)
    }
}
