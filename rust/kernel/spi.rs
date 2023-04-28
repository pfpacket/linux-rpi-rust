// SPDX-License-Identifier: GPL-2.0

//! This module provides safer and higher level abstraction over the kernel's SPI types
//! and functions.
//!
//! C header: [`include/linux/spi/spi.h`](../../../../include/linux/spi/spi.h)

use crate::{
    bindings,
    device::{self, RawDevice},
    driver,
    error::{code::*, from_kernel_result, Result},
    of,
    str::{BStr, CStr},
    to_result,
    types::ForeignOwnable,
    AlwaysRefCounted, ThisModule,
};

/// A registration of a SPI driver.
pub type Registration<T> = driver::Registration<Adapter<T>>;

/// An adapter for the registration of SPI drivers.
pub struct Adapter<T: Driver>(T);

impl<T: Driver> driver::DriverOps for Adapter<T> {
    type RegType = bindings::spi_driver;

    unsafe fn register(
        reg: *mut bindings::spi_driver,
        name: &'static CStr,
        module: &'static ThisModule,
    ) -> Result {
        // SAFETY: By the safety requirements of this function (defined in the trait definition),
        // `reg` is non-null and valid.
        let spidrv = unsafe { &mut *reg };

        spidrv.driver.name = name.as_char_ptr();
        spidrv.probe = Some(Self::probe_callback);
        spidrv.remove = Some(Self::remove_callback);
        spidrv.shutdown = Some(Self::shutdown_callback);

        if let Some(t) = T::SPI_DEVICE_ID_TABLE {
            spidrv.id_table = t.as_ref();
        }

        if let Some(t) = T::OF_DEVICE_ID_TABLE {
            spidrv.driver.of_match_table = t.as_ref();
        }

        // SAFETY:
        //   - `spidrv` lives at least until the call to `spi_driver_unregister()` returns.
        //   - `name` pointer has static lifetime.
        //   - `module.0` lives at least as long as the module.
        //   - `probe()` and `remove()` are static functions.
        //   - `of_match_table` is either a raw pointer with static lifetime,
        //      as guaranteed by the [`driver::IdTable`] type, or null.
        to_result(unsafe { bindings::__spi_register_driver(module.0, reg) })
    }

    unsafe fn unregister(reg: *mut bindings::spi_driver) {
        // SAFETY: By the safety requirements of this function (defined in the trait definition),
        // `reg` was passed (and updated) by a previous successful call to
        // `spi_driver_register`.
        unsafe { bindings::spi_unregister_driver(reg) };
    }
}

impl<T: Driver> Adapter<T> {
    fn get_of_id_info(dev: &Device) -> Option<&'static T::IdInfo> {
        let table = T::OF_DEVICE_ID_TABLE?;

        // SAFETY: `table` has static lifetime, so it is valid for read. `dev` is guaranteed to be
        // valid while it's alive, so is the raw device returned by it.
        let id = unsafe { bindings::of_match_device(table.as_ref(), dev.raw_device()) };
        if id.is_null() {
            return None;
        }

        // SAFETY: `id` is a pointer within the static table, so it's always valid.
        let offset = unsafe { (*id).data };
        if offset.is_null() {
            return None;
        }

        // SAFETY: The offset comes from a previous call to `offset_from` in `IdArray::new`, which
        // guarantees that the resulting pointer is within the table.
        let ptr = unsafe {
            id.cast::<u8>()
                .offset(offset as _)
                .cast::<Option<T::IdInfo>>()
        };

        // SAFETY: The id table has a static lifetime, so `ptr` is guaranteed to be valid for read.
        #[allow(clippy::needless_borrow)]
        unsafe {
            (&*ptr).as_ref()
        }
    }

    fn get_spi_id_info(dev: &Device) -> Option<&'static T::IdInfo> {
        // SAFETY: `dev` is guaranteed to be valid while it's alive.
        let id = unsafe { bindings::spi_get_device_id(dev.0) };
        if id.is_null() {
            return None;
        }

        // SAFETY: `id` is a pointer within the static table, so it's always valid.
        let offset = unsafe { (*id).driver_data };

        // SAFETY: The offset comes from a previous call to `offset_from` in `IdArray::new`, which
        // guarantees that the resulting pointer is within the table.
        let ptr = unsafe {
            id.cast::<u8>()
                .offset(offset as _)
                .cast::<Option<T::IdInfo>>()
        };

        // SAFETY: The id table has a static lifetime, so `ptr` is guaranteed to be valid for read.
        #[allow(clippy::needless_borrow)]
        unsafe {
            (&*ptr).as_ref()
        }
    }

    extern "C" fn probe_callback(spidev: *mut bindings::spi_device) -> core::ffi::c_int {
        from_kernel_result! {
            // SAFETY: `spidev` is valid by the contract with the C code. `dev` is alive only for the
            // duration of this call, so it is guaranteed to remain alive for the lifetime of
            // `spidev`.
            unsafe { Device::from_ptr(spidev) }
                .and_then(|dev| {
                    let of_info = Self::get_of_id_info(&dev);
                    let spi_info = Self::get_spi_id_info(&dev);
                    let data = T::probe(dev, of_info, spi_info)?;
                    // SAFETY: `spidev` is guaranteed to be a valid, non-null pointer.
                    unsafe { bindings::spi_set_drvdata(spidev, data.into_foreign() as _) };
                    Ok(0)
                })
        }
    }

    extern "C" fn remove_callback(spidev: *mut bindings::spi_device) {
        // SAFETY: `spidev` is guaranteed to be a valid, non-null pointer.
        if let Ok(dev) = unsafe { Device::from_ptr(spidev) } {
            // SAFETY: `spidev` is guaranteed to be a valid, non-null pointer.
            let ptr = unsafe { bindings::spi_get_drvdata(spidev) };
            // SAFETY:
            //   - we allocated this pointer using `T::Data::into_foreign`,
            //     so it is safe to turn back into a `T::Data`.
            //   - the allocation happened in `probe`, no-one freed the memory,
            //     `remove` is the canonical kernel location to free driver data. so OK
            //     to convert the pointer back to a Rust structure here.
            let data = unsafe { T::Data::from_foreign(ptr) };
            T::remove(dev, &data);
            <T::Data as driver::DeviceRemoval>::device_remove(&data);
        }
    }

    extern "C" fn shutdown_callback(spidev: *mut bindings::spi_device) {
        // SAFETY: `spidev` is guaranteed to be a valid, non-null pointer.
        if let Ok(dev) = unsafe { Device::from_ptr(spidev) } {
            // SAFETY: `spidev` is guaranteed to be a valid, non-null pointer.
            let ptr = unsafe { bindings::spi_get_drvdata(spidev) };
            // SAFETY: the driver data stored is valid until `remove_callback` drops it.
            let data = unsafe { T::Data::borrow(ptr) };
            T::shutdown(dev, data);
        }
    }
}

/// A SPI deivce ID
#[derive(Copy, Clone)]
pub struct DeviceId(pub &'static BStr);

unsafe impl const driver::RawDeviceId for DeviceId {
    type RawType = bindings::spi_device_id;

    const ZERO: Self::RawType = bindings::spi_device_id {
        name: [0; bindings::SPI_NAME_SIZE as _],
        driver_data: 0,
    };

    fn to_rawid(&self, offset: isize) -> Self::RawType {
        let mut id = bindings::spi_device_id {
            driver_data: offset as _,
            ..Self::ZERO
        };

        let mut i = 0;
        while i < self.0.len() {
            id.name[i] = self.0[i] as _;
            i += 1;
        }
        id.name[i] = b'\0' as _;

        id
    }
}

/// Define a const SPI device ID table
///
/// The name of the const is `SPI_DEVICE_ID_TABLE`.
///
/// # Example
///
/// ```
/// use kernel::spi;
///
/// define_i2c_id_table! {u32, [
///     (spi::DeviceId(b"test-device1"), Some(0xff)),
///     (spi::DeviceId(b"test-device2"), None),
/// ]};
/// ```
#[macro_export]
macro_rules! define_spi_id_table {
    ($data_type:ty, $($t:tt)*) => {
        $crate::define_id_table!(SPI_DEVICE_ID_TABLE, $crate::spi::DeviceId, $data_type, $($t)*);
    }
}

/// A SPI driver.
pub trait Driver {
    /// Data stored on device by driver.
    ///
    /// Corresponds to the data set or retrieved via the kernel's
    /// `spi_{set,get}_drvdata()` functions.
    ///
    /// Require that `Data` implements `ForeignOwnable`. We guarantee to
    /// never move the underlying wrapped data structure. This allows
    type Data: ForeignOwnable + Send + Sync + driver::DeviceRemoval = ();

    /// The type holding information about each device id supported by the driver.
    type IdInfo: 'static = ();

    /// The table of device ids supported by the driver.
    const OF_DEVICE_ID_TABLE: Option<driver::IdTable<'static, of::DeviceId, Self::IdInfo>> = None;

    /// The table of device ids supported by the driver.
    const SPI_DEVICE_ID_TABLE: Option<driver::IdTable<'static, DeviceId, Self::IdInfo>> = None;

    /// SPI driver probe.
    ///
    /// Called when a new SPI device is added or discovered.
    /// Implementers should attempt to initialize the device here.
    fn probe(
        dev: Device,
        of_id_info: Option<&Self::IdInfo>,
        spi_id_info: Option<&Self::IdInfo>,
    ) -> Result<Self::Data>;

    /// SPI driver remove.
    ///
    /// Called when a SPI device is removed.
    /// Implementers should prepare the device for complete removal here.
    fn remove(_dev: Device, _data: &Self::Data) {}

    /// SPI driver shutdown.
    ///
    /// Called during system state transitions such as powerdown/halt and kexec.
    /// Implementers should attempt to shutdown the device here.
    fn shutdown(_dev: Device, _data: <Self::Data as ForeignOwnable>::Borrowed<'_>) {}
}

/// A SPI device.
///
/// # Invariants
///
/// The field `ptr` is non-null and valid for the lifetime of the object.
#[repr(transparent)]
pub struct Device(*mut bindings::spi_device);

unsafe impl AlwaysRefCounted for Device {
    fn inc_ref(&self) {
        // SAFETY: The existence of a shared reference means that the refcount is nonzero.
        unsafe { bindings::spi_dev_get(self.0) };
    }

    unsafe fn dec_ref(obj: core::ptr::NonNull<Self>) {
        // SAFETY: The safety requirements guarantee that the refcount is nonzero.
        unsafe { bindings::spi_dev_put(obj.cast().as_ptr()) };
    }
}

// SAFETY:
//  - `Device` holds the lock of the device when needed.
//  - `Device` does not let you touch the underlying pointer to `spi_device`.
unsafe impl Send for Device {}

impl Device {
    /// Creates a new device from the given pointer.
    ///
    /// # Safety
    ///
    /// `ptr` must be non-null and valid. It must remain valid for the lifetime of the returned
    /// instance.
    unsafe fn from_ptr(ptr: *mut bindings::spi_device) -> Result<Self> {
        // SAFETY: increment refcount to ensure `spi_device` is alive until `Device` gets dropped.
        let ptr = unsafe { bindings::spi_dev_get(ptr) };

        if ptr.is_null() {
            Err(EINVAL)
        } else {
            // INVARIANT: The safety requirements of the function ensure the lifetime invariant.
            Ok(Self(ptr))
        }
    }

    /// Get IRQ number of the SPI device.
    pub fn get_irq(&self) -> isize {
        // SAFETY: `Device` is alive until it gets dropped
        unsafe { (*self.0).irq as _ }
    }

    /// SPI synchronous write followed by read.
    pub fn write_then_read(&self, tx_buf: &[u8], rx_buf: &mut [u8]) -> Result {
        // SAFETY: `Device` is alive until it gets dropped
        to_result(unsafe {
            bindings::spi_write_then_read(
                self.0,
                tx_buf.as_ptr() as *const core::ffi::c_void,
                tx_buf.len() as core::ffi::c_uint,
                rx_buf.as_mut_ptr() as *mut core::ffi::c_void,
                rx_buf.len() as core::ffi::c_uint,
            )
        })
    }

    /// Blocking/synchronous SPI data transfers
    ///
    /// This call may only be used from a context that may sleep.  The sleep
    /// is non-interruptible, and has no timeout.  Low-overhead controller
    /// drivers may DMA directly into and out of the message buffers.
    ///
    /// # Safety
    /// `tx_buf` and `rx_buf` must be DMA-safe otherwise UB.
    pub unsafe fn sync(&self, tx_buf: &[u8], rx_buf: &mut [u8]) -> Result {
        let mut tx_transfer = bindings::spi_transfer {
            tx_buf: tx_buf.as_ptr() as _,
            len: tx_buf.len() as _,
            ..Default::default()
        };
        let mut rx_transfer = bindings::spi_transfer {
            rx_buf: rx_buf.as_mut_ptr() as _,
            len: rx_buf.len() as _,
            ..Default::default()
        };

        let mut message: bindings::spi_message = Default::default();
        unsafe {
            bindings::spi_message_init(&mut message as _);
            bindings::spi_message_add_tail(&mut tx_transfer as _, &mut message as _);
            bindings::spi_message_add_tail(&mut rx_transfer as _, &mut message as _);

            // SAFETY: `Device` is alive until it gets dropped
            to_result(bindings::spi_sync(self.0, &mut message as _))
        }
    }

    /// SPI synchronous write
    pub fn write(&self, tx_buf: &[u8]) -> Result {
        to_result(unsafe {
            bindings::spi_write(
                self.0,
                tx_buf.as_ptr() as *const core::ffi::c_void,
                tx_buf.len() as core::ffi::c_size_t,
            )
        })
    }

    /// SPI synchronous read
    pub fn read(&self, rx_buf: &mut [u8]) -> Result {
        to_result(unsafe {
            bindings::spi_read(
                self.0,
                rx_buf.as_ptr() as *mut core::ffi::c_void,
                rx_buf.len() as core::ffi::c_size_t,
            )
        })
    }
}

impl Drop for Device {
    fn drop(&mut self) {
        // SAFETY: The refcount of `spi_device` was incremented when constructing `Device`.
        unsafe { bindings::spi_dev_put(self.0) };
    }
}

// SAFETY: The device returned by `raw_device` is the raw SPI device.
unsafe impl device::RawDevice for Device {
    fn raw_device(&self) -> *mut bindings::device {
        // SAFETY: By the type invariants, we know that `self.ptr` is non-null and valid.
        unsafe { &mut (*self.0).dev }
    }
}

/// Declares a kernel module that exposes a single SPI driver.
///
/// # Examples
///
/// ```ignore
/// # use kernel::{spi, define_of_id_table, module_spi_driver};
/// #
/// struct MyDriver;
/// impl spi::Driver for MyDriver {
///     // [...]
/// #   fn probe(_dev: &mut spi::Device, _id_info: Option<&Self::IdInfo>) -> Result {
/// #       Ok(())
/// #   }
/// #   define_of_id_table! {(), [
/// #       (of::DeviceId::Compatible(b"brcm,bcm2835-rng"), None),
/// #   ]}
/// }
///
/// module_spi_driver! {
///     type: MyDriver,
///     name: "module_name",
///     author: "Author name",
///     license: "GPL",
/// }
/// ```
#[macro_export]
macro_rules! module_spi_driver {
    ($($f:tt)*) => {
        $crate::module_driver!(<T>, $crate::spi::Adapter<T>, { $($f)* });
    };
}
