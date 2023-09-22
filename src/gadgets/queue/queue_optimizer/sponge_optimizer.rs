use super::*;

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Debug, Copy)]
pub struct SpongeRoundRequest<F: SmallField, const SWIDTH: usize> {
    pub initial_state: [Num<F>; SWIDTH],
    pub claimed_final_state: [Num<F>; SWIDTH],
}

pub struct SpongeOptimizer<
    F: SmallField,
    R: CircuitRoundFunction<F, AW, SW, CW> + AlgebraicRoundFunction<F, AW, SW, CW>,
    const AW: usize,
    const SW: usize,
    const CW: usize,
    const N: usize,
> {
    pub(crate) requests: [Vec<(SpongeRoundRequest<F, SW>, Boolean<F>)>; N],
    pub(crate) capacity: usize,
    pub(crate) _marker: std::marker::PhantomData<R>,
}

impl<
        F: SmallField,
        R: CircuitRoundFunction<F, AW, SW, CW> + AlgebraicRoundFunction<F, AW, SW, CW>,
        const AW: usize,
        const SW: usize,
        const CW: usize,
        const N: usize,
    > SpongeOptimizer<F, R, AW, SW, CW, N>
{
    pub fn new(capacity: usize) -> Self {
        Self {
            requests: std::array::from_fn(|_| Vec::new()),
            capacity,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn capacity(&self) -> usize {
        self.capacity
    }

    pub fn add_request(
        &mut self,
        request: SpongeRoundRequest<F, SW>,
        applies: Boolean<F>,
        id: usize,
    ) {
        if self.requests[id].capacity() == 0 {
            self.requests[id] = Vec::with_capacity(self.capacity);
        } else if self.requests[id].len() >= self.capacity {
            panic!(
                "over capacity: capacity is {}, but request ID {} already has {} requests",
                self.capacity,
                id,
                self.requests[id].len()
            );
        }
        self.requests[id].push((request, applies));
    }

    pub fn enforce<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) {
        for request_id in 0..self.capacity {
            use arrayvec::ArrayVec;
            let mut per_round_requests = ArrayVec::<_, N>::new();
            for i in 0..N {
                if let Some(request) = self.requests[i].get(request_id) {
                    per_round_requests.push(request);
                }
            }

            let len = per_round_requests.len();
            if len == 0 {
                continue;
            }

            let (request, applies) = if len == 1 {
                *per_round_requests[0]
            } else {
                // Check that bitmask is correct (at most one bit can be true)
                let request_bits_for_lc: ArrayVec<_, N> = per_round_requests
                    .iter()
                    .map(|(_, b)| (b.get_variable(), F::ONE))
                    .collect();
                let bit_sum = Num::linear_combination(cs, &request_bits_for_lc[..]);
                let _bit_sum = Boolean::from_variable_checked(cs, bit_sum.get_variable());

                // Select the correct request
                let mut it = per_round_requests.into_iter();
                let (mut current, _) = it.next().expect("is some");

                let mut request_flags = ArrayVec::<_, N>::new();
                for (el, flag) in it {
                    current = SpongeRoundRequest::conditionally_select(cs, *flag, el, &current);
                    request_flags.push(*flag);
                }
                let applies = Boolean::multi_or(cs, &request_flags[..]);

                (current, applies)
            };

            // Check the request
            conditionaly_check_request::<F, CS, R, AW, SW, CW>(cs, request, applies);
        }

        for i in 0..N {
            self.requests[i].clear();
        }
    }

    pub fn is_fresh(&self) -> bool {
        self.requests.iter().all(|el| el.is_empty())
    }
}

// impl<
//         F: SmallField,
//         R: CircuitRoundFunction<F, AW, SW, CW> + AlgebraicRoundFunction<F, AW, SW, CW>,
//         const AW: usize,
//         const SW: usize,
//         const CW: usize,
//         const N: usize,
//     > Drop for SpongeOptimizer<F, R, AW, SW, CW, N>
// {
//     fn drop(&mut self) {
//         for i in 0..N {
//             assert!(self.requests[i].is_empty(), "requests were not enforced!");
//         }
//     }
// }

pub fn conditionaly_check_request<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, AW, SW, CW>,
    const AW: usize,
    const SW: usize,
    const CW: usize,
>(
    cs: &mut CS,
    request: SpongeRoundRequest<F, SW>,
    applies: Boolean<F>,
) {
    let SpongeRoundRequest {
        initial_state,
        claimed_final_state,
    } = request;

    let application_result = R::compute_round_function_over_nums(cs, initial_state);

    for (res, claimed) in application_result.iter().zip(claimed_final_state.iter()) {
        Num::conditionally_enforce_equal(cs, applies, res, claimed);
    }
}
