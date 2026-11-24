# Formalizing P vs NP in Lean 4 with mathlib

`PNP.lean` is a mathlib-based formalization. The Lake project in `pnp-mathlib/`
pins a mathlib revision compatible with the installed Lean 4.36 toolchain.

To keep the build small, the file does **not** import all of mathlib. It imports
only `Mathlib.Algebra.Polynomial.Eval.Defs` and uses mathlib for:

- `Set`: `Language := Set Word`, plus `PClass` and `NPClass` as sets of languages.
- `Polynomial ℕ`: `TimeBound`, the polynomial running-time bounds.
- mathlib's polynomial evaluation lemmas and simplifier.

## What is in it

- `TM`: a deterministic single-tape Turing machine (finite states `Fin n`,
  transition function, start/accept/reject states).
- `init`, `step`, `run`, `acceptsIn`, `outputIn`: operational semantics;
  the machine stops changing its configuration once it reaches a halting state.
- `InP L`: a Turing machine **halts on every input** within a polynomial time
  bound and decides `L`.
- `InNP L`: a polynomial-time verifier **halts on every input/certificate pair**
  and accepts some polynomially bounded certificate exactly when `x ∈ L`.
- `theorem inP_subset_inNP`: the provable inclusion `P ⊆ NP`.
- `PClass`, `NPClass : Set Language`, with
  `PEqualsNP : Prop := PClass = NPClass` and the equivalent inclusion statement
  `PEqualsNP_iff_inclusion`.
- `Reducible`, `NPHard`, `NPComplete`, and a conditional version of Cook's
  theorem (`NPComplete_in_P_implies_PEqualsNP`) assuming the standard closure
  of P under polynomial-time reductions.

## Section 7: the 3b route (P ≠ NP via P/poly)

This section starts the disproof route:

- `Circuit`: a Boolean circuit with indexed input variables.
- `Circuit.eval`, `Circuit.size`, derived `ite` and `orMany`.
- `CircuitFamily`, `PolySize`, and `InPPoly`: P/poly as polynomial-size Boolean
  circuit families.
- `TMCompilesToPolyCircuits`: the standard simulation lemma stating that every
  polynomially clocked TM has an equivalent polynomial-size circuit family.
  This is isolated as an explicit hypothesis because proving it requires the
  full polynomial unrolling construction.
- `P_subset_PPoly`: from the simulation lemma, `P ⊆ P/poly`.
- `NPNotInPPoly`: the needed lower bound, i.e. some NP language has no
  polynomial-size circuits.
- `NP_not_in_PPoly_implies_not_PEqualsNP`: formal conclusion of the route:
  if an NP language is outside P/poly, then `P ≠ NP`.

The lower bound itself is open; the Lean file formalizes the implication.

## Section 8: bounded simulation and circuit unrolling

This section starts the construction of `TMCompilesToPolyCircuits`:

- `BConfig`: a bounded configuration with state, head position, and tape vector.
- `binit`, `bhalt`, `bstep`, `bnext`, `brun`, `bacceptsIn`: the bounded machine
  semantics; `bnext` freezes on halting states.
- `SimBits`: circuits representing a bounded configuration bit-by-bit.
- `initBits`, `stepBits`, `unrollBits`, `acceptCircuit`: the actual polynomial
  unrolling construction.
- `StepBitsCorrect`: the local correctness obligation for one transition
  circuit.
- `unrollBits_correct`: proved theorem — if every transition circuit is
  correct, the whole unrolled circuit correctly represents the bounded run.
- `BRunsLikeTM`: the obligation that the bounded run agrees with the original
  TM on clocked runs.
- `UnrollPolySize`: the obligation that the unrolled accept circuit has
  polynomial size.
- `bounded_unroll_implies_TMCompiles`: proved theorem assembling those three
  obligations into the TM-to-circuit compilation lemma.

So the original single hypothesis has been decomposed into three smaller and
more localized proof obligations.

The question itself is *stated*, not proved or refuted — as expected for an
open problem.

## Check

```sh
export PATH="$HOME/.elan/bin:$PATH"
cd pnp-mathlib
lake env lean PNP.lean
```

To check the top-level copy from the same project:

```sh
lake env lean ../PNP.lean
```

On a fresh checkout you first need to fetch/build the pinned mathlib dependency:

```sh
lake update
lake build Mathlib.Algebra.Polynomial.Eval.Defs
```

There should be no errors or warnings.
