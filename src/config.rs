//! A collection of configuration settings for the prover.
use std::marker::PhantomData;

use derivative::*;

// pub const DEBUG_SATISFIABLE: bool = true;
pub const DEBUG_SATISFIABLE: bool = false;

pub trait CSWitnessEvaluationConfig:
    'static + Send + Sync + Clone + Copy + std::fmt::Debug
{
    const EVALUATE_WITNESS: bool = true;
}

pub trait CSDebugConfig: 'static + Send + Sync + Clone + Copy + std::fmt::Debug {
    const PERFORM_RUNTIME_ASSERTS: bool = true;
}

pub trait CSSetupConfig: 'static + Send + Sync + Clone + Copy + std::fmt::Debug {
    const KEEP_SETUP: bool = true;
}

pub trait CSResolverConfig: 'static + Send + Sync + Clone + Copy + std::fmt::Debug {
    type DebugConfig: CSDebugConfig;
}

pub trait CSConfig: 'static + Send + Sync + Clone + Copy + std::fmt::Debug {
    type WitnessConfig: CSWitnessEvaluationConfig;
    type DebugConfig: CSDebugConfig;
    type SetupConfig: CSSetupConfig;
    type ResolverConfig: CSResolverConfig;
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct DoEvaluateWitenss;

impl CSWitnessEvaluationConfig for DoEvaluateWitenss {
    const EVALUATE_WITNESS: bool = true;
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct DontEvaluateWitenss;

impl CSWitnessEvaluationConfig for DontEvaluateWitenss {
    const EVALUATE_WITNESS: bool = false;
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct DoPerformRuntimeAsserts;

impl CSDebugConfig for DoPerformRuntimeAsserts {
    const PERFORM_RUNTIME_ASSERTS: bool = true;
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct DontPerformRuntimeAsserts;

impl CSDebugConfig for DontPerformRuntimeAsserts {
    const PERFORM_RUNTIME_ASSERTS: bool = false;
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct DoKeepSetup;

impl CSSetupConfig for DoKeepSetup {
    const KEEP_SETUP: bool = true;
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct DontKeepSetup;

impl CSSetupConfig for DontKeepSetup {
    const KEEP_SETUP: bool = false;
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct Resolver<Dbg: CSDebugConfig>(PhantomData<Dbg>);

impl<Dbg: CSDebugConfig> CSResolverConfig for Resolver<Dbg> {
    type DebugConfig = Dbg;
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct DevCSConfig;

impl CSConfig for DevCSConfig {
    type WitnessConfig = DoEvaluateWitenss;
    type DebugConfig = DoPerformRuntimeAsserts;
    type SetupConfig = DoKeepSetup;
    type ResolverConfig = Resolver<DoPerformRuntimeAsserts>;
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct ProvingCSConfig;

impl CSConfig for ProvingCSConfig {
    type WitnessConfig = DoEvaluateWitenss;
    type DebugConfig = DontPerformRuntimeAsserts;
    type SetupConfig = DontKeepSetup;
    type ResolverConfig = Resolver<DontPerformRuntimeAsserts>;
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct SetupCSConfig;

impl CSConfig for SetupCSConfig {
    type WitnessConfig = DontEvaluateWitenss;
    type DebugConfig = DontPerformRuntimeAsserts;
    type SetupConfig = DoKeepSetup;
    type ResolverConfig = Resolver<DontPerformRuntimeAsserts>;
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct VerifierCSConfig;

impl CSConfig for VerifierCSConfig {
    type WitnessConfig = DontEvaluateWitenss;
    type DebugConfig = DontPerformRuntimeAsserts;
    type SetupConfig = DontKeepSetup;
    type ResolverConfig = Resolver<DontPerformRuntimeAsserts>;
}
