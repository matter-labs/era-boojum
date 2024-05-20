use crate::{dag::primitives::ResolverIx, log};
use std::collections::HashMap;

use crate::cs::Place;

#[derive(Debug, Clone)]
pub(crate) struct Stats {
    total_resolvers: usize,
    total_delayed_resolvers: usize,
    total_used_places: usize,
    max_resolvers_per_place: usize,
    avg_resolvers_per_place: usize,
    pub secondary_resolutions: usize,
}

/// The Registrar keeps track of all variables in accordance to their place in the resolver, and
/// keeps tabs on how many variables are tracked in total in the circuit.
///
/// Unlike the deferrer, it is responsible with deciding whether a resolver should be deferred,
/// and can handle any non circular dependency among the deferred resolvers.
pub(crate) struct Registrar {
    pub max_tracked_variable: Place,
    vars: HashMap<Place, Vec<ResolverIx>>,
    pub stats: Stats,
}

impl Registrar {
    pub(crate) fn new() -> Self {
        Self {
            max_tracked_variable: Place::placeholder(),
            vars: HashMap::new(),
            stats: Stats {
                total_resolvers: 0,
                total_delayed_resolvers: 0,
                total_used_places: 0,
                max_resolvers_per_place: 0,
                avg_resolvers_per_place: 0,
                secondary_resolutions: 0,
            },
        }
    }

    /// Delays the resolver if the input variables are not tracked. Returns `Ok`
    /// with the resolver index if the resolver is accepted, or `Err` with the
    /// max input place in the parameter list.
    pub(crate) fn accept(
        &mut self,
        inputs: &[Place],
        resolver_ix: ResolverIx,
    ) -> Result<ResolverIx, Place> {
        use std::cmp::Ordering::*;

        assert!(inputs.iter().all(|x| x.is_copiable_variable()));

        self.stats.total_resolvers += 1;

        if inputs.is_empty() {
            return Ok(resolver_ix);
        }

        let max_input_place = inputs.iter().max_by_key(|x| x.0).unwrap();

        match max_input_place.partial_cmp(&self.max_tracked_variable) {
            Some(Less) | Some(Equal) => Ok(resolver_ix),

            Some(Greater) | None => {
                // None means that `advance()` was never called, which means
                // that there are no tracked values yet, thus any resolver with
                // a dependency can't be registered.
                self.stats.total_delayed_resolvers += 1;

                if self.vars.contains_key(max_input_place) == false {
                    self.stats.total_used_places += 1;
                }

                self.vars
                    .entry(*max_input_place)
                    .or_default()
                    .push(resolver_ix);

                self.stats.max_resolvers_per_place = self
                    .stats
                    .max_resolvers_per_place
                    .max(self.vars[max_input_place].len());

                self.stats.avg_resolvers_per_place =
                    self.stats.total_delayed_resolvers / self.stats.total_used_places;

                Err(*max_input_place)
            }
        }
    }

    pub(crate) fn advance(&mut self, to: Place) -> Vec<ResolverIx> {
        let mut resolvers = Vec::new();

        for (place, resolver_ixs) in self.vars.iter_mut() {
            if place.0 <= to.0 {
                resolvers.append(resolver_ixs);

                if super::PARANOIA
                    && resolver_ixs
                        .iter()
                        .any(|x| *x == ResolverIx::new_resolver(0))
                {
                    println!("CRR: advancing with resolver_ix 0");
                }
            }
        }

        self.vars.retain(|place, _| place.0 > to.0);

        self.max_tracked_variable = to;

        resolvers
    }

    pub(crate) fn is_empty(&self) -> bool {
        if cfg!(feature = "cr_paranoia_mode") {
            log!(
                "CRR: total remaining resolvers: {}",
                self.vars.values().map(|x| x.len()).sum::<usize>()
            );
            log!(
                "CRR: min tracked variable: {:?}",
                self.vars
                    .keys()
                    .min_by_key(|x| x.as_any_index())
                    .unwrap_or(&Place(0))
            );
            log!(
                "CRR: current max tracked variable: {:?}",
                self.max_tracked_variable
            );
        }

        self.vars.is_empty()
    }

    pub(crate) fn peek_vars(&'_ self) -> &'_ HashMap<Place, Vec<ResolverIx>> {
        &self.vars
    }
}

#[cfg(test)]
mod test {
    use super::*;

    // variables that are not tracked are delayed
    #[test]
    fn test1() {
        let mut registrar = Registrar {
            max_tracked_variable: Place(0),
            vars: HashMap::new(),
            stats: Stats {
                total_resolvers: 0,
                total_delayed_resolvers: 0,
                total_used_places: 0,
                max_resolvers_per_place: 0,
                avg_resolvers_per_place: 0,
                secondary_resolutions: 0,
            },
        };

        let inputs = vec![Place(1), Place(2), Place(3)];
        let resolver_ix = ResolverIx(0);

        let resolvers = registrar.accept(&inputs, resolver_ix);

        assert!(resolvers.is_err());
    }

    // variables that are tracked are not delayed
    #[test]
    fn test2() {
        let mut registrar = Registrar {
            max_tracked_variable: Place(3),
            vars: HashMap::new(),
            stats: Stats {
                total_resolvers: 0,
                total_delayed_resolvers: 0,
                total_used_places: 0,
                max_resolvers_per_place: 0,
                avg_resolvers_per_place: 0,
                secondary_resolutions: 0,
            },
        };

        let inputs = vec![Place(1), Place(2), Place(3)];
        let resolver_ix = ResolverIx(0);

        let resolvers = registrar.accept(&inputs, resolver_ix);

        assert!(resolvers.is_ok());
    }

    // delayed resolvers are returned when the variable is advanced
    #[test]
    fn test3() {
        let mut registrar = Registrar {
            max_tracked_variable: Place(0),
            vars: HashMap::new(),
            stats: Stats {
                total_resolvers: 0,
                total_delayed_resolvers: 0,
                total_used_places: 0,
                max_resolvers_per_place: 0,
                avg_resolvers_per_place: 0,
                secondary_resolutions: 0,
            },
        };

        let inputs = vec![Place(1), Place(2), Place(3)];
        let resolver_ix = ResolverIx(0);

        let resolver = registrar.accept(&inputs, resolver_ix);

        assert!(resolver.is_err());

        let resolvers = registrar.advance(Place(3));

        assert_eq!(1, resolvers.len());
    }

    // delayed resolvers from multiple places are returned when the variable is advanced
    #[test]
    fn test4() {
        let mut registrar = Registrar {
            max_tracked_variable: Place(0),
            vars: HashMap::new(),
            stats: Stats {
                total_resolvers: 0,
                total_delayed_resolvers: 0,
                total_used_places: 0,
                max_resolvers_per_place: 0,
                avg_resolvers_per_place: 0,
                secondary_resolutions: 0,
            },
        };

        let inputs = vec![Place(1), Place(2), Place(3)];
        let resolver_ix = ResolverIx(0);

        let resolvers = registrar.accept(&inputs, resolver_ix);

        assert!(resolvers.is_err());

        let inputs = vec![Place(1), Place(2), Place(4)];
        let resolver_ix = ResolverIx(1);

        let resolvers = registrar.accept(&inputs, resolver_ix);

        assert!(resolvers.is_err());

        let resolvers = registrar.advance(Place(4));

        assert_eq!(2, resolvers.len());
    }
}
