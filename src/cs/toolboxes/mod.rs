// pub mod gate_config;
// pub mod static_toolbox;

pub mod simplified;

pub use self::simplified::simple_toolbox as static_toolbox;
pub use self::simplified::simple_type_combinator as gate_config;
