#![deny(missing_docs)]

//! # Legion Type Uuid
//!
//! legion-typeuuid provides the `SerializableTypeUuid` type key, which can be used with legion's `Registry` to provide stable component type ID mappings for world serialization.
//!
//! ```rust
//! # use legion::*;
//! # use legion_typeuuid::*;
//! # #[derive(serde::Serialize, serde::Deserialize)]
//! # struct Position;
//! let mut registry = Registry::default();
//! let uuid = SerializableTypeUuid::parse_str("1d97d71a-76bf-41d1-94c3-fcaac8231f12");
//! registry.register::<Position>(uuid);
//! ```
//!
//! ## Feature Flags
//!
//! ### `type-uuid`
//!
//! Allows type UUIDs defined with the `type-uuid` crate to be used with `SerializableTypeUuid`.
//!
//! ```rust
//! # #[cfg(feature = "type-uuid")] {
//! # use legion::*;
//! # use legion_typeuuid::*;
//! # use serde::{Serialize, Deserialize};
//! # use type_uuid::TypeUuid;
//! #[derive(Serialize, Deserialize, TypeUuid)]
//! #[uuid = "1d97d71a-76bf-41d1-94c3-fcaac8231f12"]
//! struct Position;
//!
//! let mut registry = Registry::<SerializableTypeUuid>::default();
//! registry.register_auto_mapped::<Position>();
//! # }
//! ```
//!
//! ### `collect`
//!
//! Allows automatic component type registration with the `register_serialize!` macro and `collect_registry()` function. This feature requires your crate to also declare a dependency to the `inventory` crate.
//!
//! ```rust
//! # #[cfg(feature = "collect")] {
//! # use legion::*;
//! # use legion_typeuuid::*;
//! # use serde::{Serialize, Deserialize};
//! #[derive(Serialize, Deserialize)]
//! struct Position;
//!
//! register_serialize!(Position, "1d97d71a-76bf-41d1-94c3-fcaac8231f12");
//!
//! let registry = collect_registry();
//! # }
//! ```
//!
//! This can be used together with the `type-uuid` feature.
//!
//! ```rust
//! # #[cfg(all(feature = "type-uuid", feature = "collect"))] {
//! # use legion::*;
//! # use legion_typeuuid::*;
//! # use serde::{Serialize, Deserialize};
//! # use type_uuid::TypeUuid;
//! #[derive(Serialize, Deserialize, TypeUuid)]
//! #[uuid = "1d97d71a-76bf-41d1-94c3-fcaac8231f12"]
//! struct Position;
//!
//! register_serialize!(Position);
//!
//! let registry = collect_registry();
//! # }
//! ```

use serde::{Deserialize, Serialize};
use uuid::Uuid;

#[cfg(feature = "collect")]
pub use crate::collect::{collect_registry, TypeUuidRegistration};

/// Maps component types to stable UUIDs for (de)serialization via the `type_uuid` crate.
#[derive(Copy, Clone, PartialOrd, Ord, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct SerializableTypeUuid(Uuid);

impl SerializableTypeUuid {
    /// Parses a UUID string into a `SerializableTypeUuid`.
    pub fn parse_str(uuid: &str) -> Option<Self> {
        let uuid = Uuid::parse_str(uuid).ok()?;
        Some(Self(uuid))
    }
}

impl From<[u8; 16]> for SerializableTypeUuid {
    fn from(bytes: [u8; 16]) -> Self {
        Self(Uuid::from_bytes(bytes))
    }
}

#[cfg(feature = "type-uuid")]
impl<T: legion::storage::Component + type_uuid::TypeUuid> legion::serialize::AutoTypeKey<T>
    for SerializableTypeUuid
{
    fn new() -> Self {
        Self::from(T::UUID)
    }
}

#[cfg(feature = "collect")]
mod collect {
    use super::SerializableTypeUuid;
    use legion::Registry;

    /// Holds information required to register a type with legion's Registry.
    pub struct TypeUuidRegistration {
        /// A function which registers a type with the given `Registry`.
        pub builder: fn(&mut Registry<SerializableTypeUuid>),
    }

    inventory::collect!(TypeUuidRegistration);

    /// Constructs a `Registry` which is pre-loaded with all types which have been
    /// registered with the `register_serialize` macro.
    pub fn collect_registry() -> Registry<SerializableTypeUuid> {
        let mut registry = Registry::default();
        for registration in inventory::iter::<TypeUuidRegistration> {
            (registration.builder)(&mut registry);
        }
        registry
    }

    /// Registers a component type with a UUID for serialization.
    #[macro_export]
    #[cfg(not(feature = "type-uuid"))]
    macro_rules! register_serialize {
        ($component:ty, $uuid:literal) => {
            ::inventory::submit! {
                ::legion_typeuuid::TypeUuidRegistration {
                    builder: |registry| {
                        let id = ::legion_typeuuid::SerializableTypeUuid::parse_str($uuid)
                            .expect(&format!("could not parse uuid for {}", std::any::type_name::<$component>()));
                        registry.register::<$component>(id);
                    }
                }
            }
        };
    }

    /// Registers a component type with a UUID for serialization.
    #[macro_export]
    #[cfg(feature = "type-uuid")]
    macro_rules! register_serialize {
        ($component:ty, $uuid:literal) => {
            ::inventory::submit! {
                ::legion_typeuuid::TypeUuidRegistration {
                    builder: |registry| {
                        let id = ::legion_typeuuid::SerializableTypeUuid::parse_str($uuid)
                            .expect(&format!("could not parse uuid for {}", std::any::type_name::<$component>()));
                        registry.register::<$component>(id);
                    }
                }
            }
        };
        ($component:ty) => {
            ::inventory::submit! {
                ::legion_typeuuid::TypeUuidRegistration {
                    builder: |registry| {
                        let uuid = <$component as ::type_uuid::TypeUuid>::UUID;
                        registry.register::<$component>(uuid.into());
                    }
                }
            }
        };
    }

    macro_rules! register_serialize_external {
        ($component:ty, $uuid:literal) => {
            ::inventory::submit! {
                crate::TypeUuidRegistration {
                    builder: |registry| {
                        let uuid = ::uuid::Uuid::parse_str($uuid).unwrap();
                        let id = crate::SerializableTypeUuid(uuid);
                        registry.register::<$component>(id);
                    }
                }
            }
        };
    }

    register_serialize_external!(bool, "abea8c1e-6910-43e4-b579-9ef1b5a95226");
    register_serialize_external!(isize, "0d3b0c08-45ff-43f4-a145-b2bdef69d1d2");
    register_serialize_external!(i8, "92fd5f7b-2102-46cb-9b1b-662df636625a");
    register_serialize_external!(i16, "a02dfda1-8603-4d69-818a-1e1c47b154b6");
    register_serialize_external!(i32, "6dd1ba7e-fa8b-4aa1-ac22-c28773798975");
    register_serialize_external!(i64, "3103622f-fdfa-4ae3-8ede-67b56bd332fd");
    register_serialize_external!(usize, "1d4562ce-b27d-4e99-af44-a40aca248c2e");
    register_serialize_external!(u8, "b0fe47a9-fd37-41c6-b2ab-bed5d385ccde");
    register_serialize_external!(u16, "3ad2a84b-c5a6-414c-8628-75613e11e67e");
    register_serialize_external!(u32, "f6cc80b8-94e8-4c05-80b1-a8fbbaeb67af");
    register_serialize_external!(u64, "da9a3e45-516c-4412-87d2-96ea17bebd21");
    register_serialize_external!(i128, "0dbb7b33-9f27-4b3f-aebc-11426c464323");
    register_serialize_external!(u128, "46eaab86-9268-4e98-ac9f-76eb71a1f0b4");
    register_serialize_external!(f32, "5b1d1734-9fcc-43e7-8cc6-452ba16ff1fd");
    register_serialize_external!(f64, "76b2ebf4-cd06-41de-96dc-2f402ffa46b2");
    register_serialize_external!(char, "9786a9f4-1195-4dd1-875d-3e469454d9c4");
    register_serialize_external!(String, "7edbc10a-2147-499c-af9a-498723c7b35f");
    register_serialize_external!(std::ffi::CString, "d26a39da-d0e2-46b1-aeab-481fe57d0f23");
    #[cfg(any(unix, windows))]
    register_serialize_external!(std::ffi::OsString, "38485fce-f5d0-48df-b5cb-98e510c26a8d");
    register_serialize_external!(std::num::NonZeroU8, "284b98ec-ecb5-463c-9744-23b8669c5553");
    register_serialize_external!(std::num::NonZeroU16, "38f030e4-6046-45c9-96b4-1830b1aa3f35");
    register_serialize_external!(std::num::NonZeroU32, "b32f7cc7-2841-48b3-8d8e-760414b4c4ab");
    register_serialize_external!(std::num::NonZeroU64, "b43c6dad-6608-4f02-817a-8eac8c6345cb");
    register_serialize_external!(std::time::Duration, "449a4224-4665-47ce-88a2-8d0310d20572");
    register_serialize_external!(
        std::time::SystemTime,
        "b8dfc518-faf7-4590-91ba-82acd78b1685"
    );
    register_serialize_external!(std::net::IpAddr, "a3c248b7-94e1-4d4a-8b7e-fd1915f4c81b");
    register_serialize_external!(std::net::Ipv4Addr, "a62542a2-6a38-4980-9467-f093bb546140");
    register_serialize_external!(std::net::Ipv6Addr, "a6ba4f16-f436-4ae2-ae62-69dd08150b33");
    register_serialize_external!(std::net::SocketAddr, "fe76891f-3e0a-49f7-b32e-14fc11768844");
    register_serialize_external!(
        std::net::SocketAddrV4,
        "e951fa30-50d9-4832-8bc9-c49c06037697"
    );
    register_serialize_external!(
        std::net::SocketAddrV6,
        "8840455b-ad6c-41ae-8694-e50873d952c4"
    );
    register_serialize_external!(std::path::PathBuf, "d6db3123-4c95-45de-a28f-5a48d574b9c4");

    #[allow(dead_code)]
    type Unit = ();
    register_serialize_external!(Unit, "03748d1a-0d0c-472f-9fdd-424856157064");
}

#[cfg(test)]
mod tests {
    #[test]
    #[cfg(feature = "collect")]
    fn serialize_json_uuid() {
        use super::*;
        use legion::*;

        let universe = Universe::new();
        let mut world = universe.create_world();

        let entity = world.extend(vec![
            (1usize, false, 1isize),
            (2usize, false, 2isize),
            (3usize, false, 3isize),
            (4usize, false, 4isize),
        ])[0];

        let registry = collect_registry();

        let json = serde_json::to_value(&world.as_serializable(any(), &registry)).unwrap();
        println!("{:#}", json);

        use serde::de::DeserializeSeed;
        let world: World = registry
            .as_deserialize(&universe)
            .deserialize(json)
            .unwrap();
        let entry = world.entry_ref(entity).unwrap();
        assert_eq!(entry.get_component::<usize>().unwrap(), &1usize);
        assert_eq!(entry.get_component::<bool>().unwrap(), &false);
        assert_eq!(entry.get_component::<isize>().unwrap(), &1isize);

        assert_eq!(4, world.len());
    }
}
