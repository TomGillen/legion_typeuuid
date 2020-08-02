# Legion Type Uuid

legion-typeuuid provides the `SerializableTypeUuid` type key, which can be used with legion's `Registry` to provide stable component type ID mappings for world serialization.

```rust
let mut registry = Registry::new();
let uuid = SerializableTypeUuid::parse_str("1d97d71a-76bf-41d1-94c3-fcaac8231f12");
registry.register::<Position>(uuid);
```

## Feature Flags

### `type-uuid`

Allows type UUIDs defined with the `type-uuid` crate to be used with `SerializableTypeUuid`.

```rust
#[derive(Serialize, Deserialize, TypeUuid)]
#[uuid = "1d97d71a-76bf-41d1-94c3-fcaac8231f12"]
struct Position;

let mut registry = Registry::new();
registry.register_auto_mapped::<Position>();
```

### `collect`

Allows automatic component type registration with the `register_serialize!` macro and `collect_registry()` function. This feature requires your crate to also declare a dependency to the `inventory` crate.

```rust
#[derive(Serialize, Deserialize)]
struct Position;

register_serialize!(Position, "1d97d71a-76bf-41d1-94c3-fcaac8231f12");

let registry = collect_registry();
```

This can be used together with the `type-uuid` feature.

```rust
#[derive(Serialize, Deserialize, TypeUuid)]
#[uuid = "1d97d71a-76bf-41d1-94c3-fcaac8231f12"]
struct Position;

register_serialize!(Position);

let registry = collect_registry();
```
