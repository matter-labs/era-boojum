# Boojum

[![Logo](eraLogo.png)](https://zksync.io/)

zkSync Era is a layer 2 rollup that uses zero-knowledge proofs to scale Ethereum without compromising on security or
decentralization. Since it's EVM compatible (Solidity/Vyper), 99% of Ethereum projects can redeploy without refactoring
or re-auditing a single line of code. zkSync Era also uses an LLVM-based compiler that will eventually let developers
write smart contracts in C++, Rust and other popular languages.

## About

The purpose of this library is to work with a very specific arithmetization with additional assumptions about the field size. Roughly, we expect to have a field `F` with |F| ~ 64 bits (the size of a machine word) (the assumption about field size is not important for the strategy of arithmetization and gate placement, but it is asserted in gadget implementations for particular functions which rely on a specific field size).

The system has a hierarchy of logical function (gadgets) - gates (entities that can inscribe itself into trace) - and evaluators (relations between polynomials). Evaluators are written in the form of a trait that allows us to later on automatically compose functions to check satisfiability and compute proofs, as well as synthesize plain and recursive verifiers. Gates have additional tooling attached to them that allows the gates themselves to track the logic of where they should be placed in the trace. Note that we rely on Plonk's copy constraints and work on the copiable logical entities of "variables" to compose a final provable statement. The system is not intended for AIR arithmetization and doesn't allow to express constraints that span multiple rows of the trace.

In general, the trace contrains few varieties of columns. The main separation is between:
- General purpose columns - where one can allow some columns of variables (copiable), witnesses (non-copiable, also sometimes called "advice" columns) and constants to be used by **DIFFERENT TYPES** of gates, leading to the necessity to place selectors in front of the corresponding terms in the quotient polynomial. For these general purpose columns, the placement logic is simple: we try to put in as many repetitions of the same relation as the gate/evaluator allows, based on the designated number of columns of the corresponding type in the system. Later on, when selectors are materialized, a few extra constant columns can be added. In general, the default behavoir of the gates is to try to "amortize" constants, in a sense that over the same row, we try to place gates that use same constants. This is a reasonable approach because most of the circuits are "cycles" in practice, so we can "fill" the row.
- "Specialized" columns - where one can designate a separate set of columns to the particular gate/evaluator, so the relation enforced by evaluator must hold on every row in these columns. This may be beneficial in some circuits where a particular gate is used very often. One can specify few different modes of utilization of these columns in the case of multiple sets being spent for the same relations, namely to share constants or not between sets.

In addition, the trace allows you to add a lookup argument, which can also either use specialized columns to house the entries of the lookup tables, or just use general purpose columns. Tables are encoded as only one set of polynomials for now, so the total length of the trace must be larger than the total number of entries in the tables. 

Note that every "gate" (as a Rust type) is unique, and so a gate can only be placed into either specialized or general purpose columns, but not into both. If one needs such functionality then it's possible to make a newtype wrapper.

Higher level logical functions (like boolean decompositions, range checks, zero checks, etc) are used to make a circuit internally inscribe themselves in different manners depending if some gates are allowed or not allowed in the particular instance of the CS. Instances of the CS with different sets of gates are considered a different type from the Rust perspective, and we rely on some inlining/constant prop/compiler work to reduce branching into static jumps.

### Notes on subparts of construction

- Only the 2^64 - 2^32 + 1 field is implemented. The non-vectorized math implementation is based on the implementation developed for Plonky2, but is reformulated for const traits
- Auto-vectorization is performed mainly for additions, where benefits are clear
- Poseidon MDS and round constants are equal to Plonky2 to have some compatibility for users
- Poseidon2 round constants reuses the Poseidon constants
- Arithmetization constraints only affect one row. The placement strategy is to amortize constants as much as possible by tiling row-wise or column-wise
- Copy-permutation argument is taken from Plonk (the grand product based one). May be changed to log-derivative (the additive one) later on
- Lookup argument is log-derivative (the additive one)
- Lookup tables in a circuit must all be the same width for now
- No columns can be separated from the oracles and fed into another proof yet
- At the moment, the movement to the extension field is only done on FRI aggregation (so during previous stages challenges are of `|F|` and so we have to repeat arguments), but this will be changed so that we move to the extension field as fast as possible after committing to the witness to avoid a quite "large" chance of getting zeroes in denominator. The effect on computational expense in proving is quite negligible
- Zero-knowledge is not yet implemented, but planned (gates will itself determine how to put a satisfying, but random witness in their yet unused rows)
- FFT is not optimized
- Hashes are somewhat optimized
- Implemented gates are opinionated, as well as arithmetizations

### Note on lookup argument

We use a lookup argument enforced via the relations `\sum_i selector(x_i) / (witness(x_i) + beta) == \sum_i multiplicity(x_i) / (table(x_i) + beta)` where a lookup over specialized columns `selector(x_i)` is just an identity. We also do not encode the tables as the polynomial of smaller degree to eliminate extra degree bound checks, and instead pad them with zeroes. Note that table entries never contain an element of `(0,0,...,0)` as we use separate ID columns for table types in case of multiple tables (even in the case of only one table being used), and an ID like this starts with 1.

One nice feature of a lookup argument like this is that, due to its additive nature, if we do lookups over multiple `witness` polynomials into the same table, instead of repeating the argument for every (tuple of) polynomial(s) (which would require a separate multiplicity column, as well as few a intermediate polynomials later on), we can "add up" multiplicities and transform the argument into something like `\sum_i selector_0(x_i) / (witness_0(x_i) + beta) + \sum_i selector_1(x_i) / (witness_1(x_i) + beta) == \sum_i total_multiplicity(x_i) / (table(x_i) + beta)`, so that the total cost of a lookup is just 1 multiplicities column, and 2 (witness-related) + 1 (table-related) intermediate polynomials to encode the lhs and rhs relations on the roots of unity.

The correctness of this argument is clear.
For soundness, we use the original argument as in the ["Cached quotients for fast lookups" paper](https://eprint.iacr.org/2022/1763), Lemma 2.4.
We need to show that it suffices to commit to the `total_multiplicity` rather than to the multiplicities of `witness_0` and `witness_1` separately.

Suppose the equation `\sum_i selector_0(x_i) / (witness_0(x_i) + X) + \sum_i selector_1(x_i) / (witness_1(x_i) + X) == \sum_i total_multiplicity(x_i) / (table(x_i) + X)` holds. 
We need to show that `witness_0` and `witness_1` are contained in the table `t`.
Let `f = (witness_0 | witness_1)`, a concatenation of the values.
The equation above implies `\sum_i selector_i / (f_i + X) == \sum_i total_multiplicity_i / (t_i + X)` (note that the interval length of `i` on the LHS is double than the above).
By Lemma 2.4 we get `f \subset t`: "subset" in the sense that every coordinate of the vector `f` is a coordinate of `t`.
In particular, `witness_0, witness_1 \subset f \subset t`.

Note that the argument holds for several `witness_i` as well. The rest of the soundness argument, for a chosen `\beta`, follows directly as in the work above.

### Planned extensions
- [ ] Allow lookup tables of different "width" (Unlikely now, we need to update type system a little)
- [x] Split the CS into a "configurable" part (where one can allow gates and static tools), and an "inscribable" part (where one can put variables, gates, etc). So one first configures, then "freezes" and then inscribes, and can not make a mistake along the way
- [ ] Allow an alternative selector mode (individual insteal of tree) for rare circuits that need it. Because we have a huge number of setup polynomials from copy-permutation anyways, flat selectors are not that expensive if they allow to avoid pushing quotient degree 2x
- [ ] Make u16/u32 use "static" caches for decompositions instead of "dynamic" ones
- [ ] Make "dyn" verifier, so all it's descendants are "Self". Note: most likely unnecessary
- [x] Move to the field extension "earlier", because it only affects the copy-permutation product and lookup argument parts, and this tradeoff is acceptable in comparison to the `2^-40` chance to get `0` in denominators
- [x] Switch to generic logging
- [x] Switch to Poseidon2 by default
    - Note on Monolith: even though it's blazing fast, it has a drawback where it's very hard to just unroll it into single "row" as it mixes lookups and algebraic relations. It may not be the best suited for circuit instances of large width
- [ ] Actually optimize FFT
- [ ] Check what's the most optimal strategy to evaluate gates over general purpose columns
- [x] Merge new DAG resolver (10-100x faster)
- [ ] Tune consistency check for auxilary lookup polynomials to utilize higher-degree constraint if it's "free" (if we would already do higher degree extension anyway for copy-permutation, or gates)

### For curions in benchmarks only

There are benchmarks for 8kB of SHA256 using what we think is somewhat optimal configuration of gates + tables for SHA256 circuit. Note that even though the prover is kind-of fast, we didn't properly optimize the FFT and still use Poseidon (not Poseidon2) for configurations where we expect the proof to be used for recursion. Two scripts `sha256_bench_recursive.sh` and `sha256_bench_non_recursive.sh` allow you to run the corresponding tests (whether proof is expected to be used in recursion or not), and you should look for a line `Proving is done, taken ...` to see the proving time, because the verifier that runs after it is quite verbose. These benchmarks use an LDE factor of 8, even though all our constraints are of degree 4 or less - however, it's a parameter that is used in some other public benchmarks. We also do not use PoW in those proofs because PoW for 20 bits is negligible (30ms), and we do not support PoW over algebraic hashes yet (however those are only ~2x slower, so also negligible). Security level is roughly `100` bits, but the FRI soundness can be boosted by increaseing the number of queries, and an increase in number of queries doesn't increase prover time (not to be confused with changing the FRI rate). Trace length is `2^16` and it uses 60 general purpose columns and 8 lookup arguments of width 4.

Note: benchmarks just try to compile to native arch and only AArch64 (read Apple M1) arch is normally tested end-to-end for now. x86-64 arithmetic implementations were tested for validity, but not end-to-end in full proofs. Note that max performance x86-64 requires extra compiler feature flags in addition to `cpu = native` (AVX512 set is not used by Rust compiler even on native CPUs)

## License

The Boojum prover is distributed under the terms of either

- Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Official Links

- [Website](https://zksync.io/)
- [GitHub](https://github.com/matter-labs)
- [Twitter](https://twitter.com/zksync)
- [Twitter for Devs](https://twitter.com/zkSyncDevs)
- [Discord](https://join.zksync.dev/)

## Disclaimer

zkSync Era has been through lots of testing and audits. Although it is live, it is still in alpha state and will go
through more audits and bug bounties programs. We would love to hear our community's thoughts and suggestions about it!
It is important to state that forking it now can potentially lead to missing important security updates, critical
features, and performance improvements.

### Third party notices
This software includes components from third parties. For a full list of these components and their licenses, see the [THIRD PARTY NOTICES file](ThirdPartyNotices.txt).

