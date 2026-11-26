# Formalizing P vs NP in Lean 4 with mathlib

`PNP.lean` is a mathlib-based formalization. The Lake project in `pnp-mathlib/`
pins a mathlib revision compatible with the installed Lean 4.36 toolchain.

To keep the build small, the file does **not** import all of mathlib. It imports
`Mathlib.Algebra.Polynomial.Eval.Defs` and `Mathlib.Data.List.GetD` and uses
mathlib for:

- `Set`: `Language := Set Word`, plus `PClass` and `NPClass` as sets of languages.
- `Polynomial ℕ`: `TimeBound`, the polynomial running-time bounds.
- mathlib's polynomial evaluation lemmas and simplifier.
- list `getD` lemmas for indexed words.

## What is in it

- `TM`: a deterministic single-tape Turing machine (finite states `Fin n`,
  transition function, start/accept/reject states).
- `init`, `step`, `run`, `acceptsIn`, `outputIn`: operational semantics;
  the machine stops changing its configuration once it reaches a halting state.
- `boutputIn`: the bounded transducer output, read from fixed absolute tape
  indices so that every output bit has a direct circuit representation.
- `DTM`, `DConfig`, `Dinit`, `Dstep`, `Drun`, `Dboutput`, and `DboutputUpTo`: a
  composable transducer model with a read-only input word, an append-only output
  word, and a two-way infinite work tape.  `DAction` carries optional head
  movements (`none` means stay put) and the optional work-tape write, so ordinary
  subroutine constructions can keep auxiliary data.  Its `handoff` instruction resets the input to the current
  output, clears the output, and blanks the work tape, which is exactly what
  sequential composition needs.  The original decider model and all
  circuit-compilation lemmas remain unchanged.
- `DPolyTimeComputable`: polynomial-time computability in the composable model,
  with separate time and length polynomials.
- `Dcompose`, `liftFirst`, and `liftSecond`: the sequential-composition machine
  and the two phase-simulation invariants.  A first-phase halting step performs
  the handoff; subsequent steps mirror the second machine.
- `theorem DPolyTimeComputableClosedUnderComposition`: proved sequential closure
  in the composable model.  The first machine's first halt is located with
  `Nat.find`; freezing lemmas show its output is unchanged up to the full time
  bound, and the handoff gives the second machine a clean input.
- `DIdTM` and `dPolyTimeComputable_id`: the first concrete subroutine in the
  composable model, copying the read-only input to the output in linear time.
  Its proofs exercise the boundary-aware input reader and the stay-put movement
  option.
- `DAppendTM` and `dPolyTimeComputable_append`: a second concrete subroutine,
  copying the input and then emitting a fixed suffix.  Its fixed-suffix phase
  uses `Option`-valued head movements to stay put while reading the suffix from
  the machine's finite control.
- `DPrependTM` and `dPolyTimeComputable_prepend`: a fixed-prefix emitter followed
  by an input-copy phase.
- `DConstTM` and `dPolyTimeComputable_const`: a fixed-word emitter that ignores
  its input.
- `DUnaryLengthTM` and `dPolyTimeComputable_unary_length`: a length-dependent
  subroutine computing `replicate x.length true ++ [false]`.  It copies the
  input, uses the handoff instruction to make that copy the new input, and then
  emits one `true` per bit.
- `dPolyTimeComputable_var_encoding_length`: composition of the prefix and
  unary-length subroutines, producing the encoding of a variable whose index is
  the input length.
- `Formula.dPolyTimeComputable_var_encoding`, `not_encoding`, `and_encoding`,
  and `or_encoding`: concrete transducers for the formula constructors.  Because
  the encoding is prefix-based, every constructor is a fixed-tag prepend; for
  binary connectives the pair format is `f.encode ++ g.encode`.
- `Formula.unaryIndexEncode` and `dPolyTimeComputable_unaryIndexEncode`: turn a
  unary index code `1^i 0` directly into `(var i).encode`.  This works because
  `Formula.encodeNat i` is exactly that unary code, so only the variable tag is
  prepended; it supplies the encoded literals needed by Tseitin constraints.
- Constant formula encodings and the `.andConst`, `.orConst`, and `.notFormula`
  combinators for `DPolyTimeComputable`, which assemble fixed clause shapes
  around computed literal encodings.
- `DNotBitsTM` and `dPolyTimeComputable_bitwise_not`: a linear-time transducer
  that complements every input bit.
- `DDoubleTM` and `dPolyTimeComputable_double`: a linear-time transducer for
  `x ↦ x ++ x`.  It copies the input, rewinds using the two-way input head, and
  copies it again while appending.
- `DLengthPrefixTM` and `dPolyTimeComputable_length_prefix`: a linear-time
  transducer for `x ↦ encodeNat |x| ++ x`, where the prefix is unary.  It emits
  the length while scanning, rewinds, and then copies the original input.
- `DPadTM` and `dPolyTimeComputable_pad`: a linear-time transducer for
  `x ↦ x ++ replicate |x| false`, giving a canonical fixed-length padding whose
  output length depends only on `|x|`.
- `DMapTM` and `dPolyTimeComputable_map`: a generic linear-time transducer for
  applying any fixed Boolean function pointwise, `x ↦ x.map g`.  The earlier
  bitwise-complement transducer is a special case.
- Closure corollaries for `DPolyTimeComputable`: `.map`, `.double`, `.pad`,
  `.append`, `.prepend`, and `.copyMap`.  They turn the concrete subroutines
  into reusable combinators for assembling larger formula transformations.
- `DCopyMapTM` and `dPolyTimeComputable_copy_map`: a copy-and-map transducer for
  `x ↦ x ++ x.map g`, generalizing both self-concatenation and fixed padding.
- `DInsertSelfTM` and `dPolyTimeComputable_insert_self`: a transducer for
  `x ↦ x ++ y ++ x`, with an arbitrary fixed word `y` inserted between two
  copies of the input.  Its closure corollary is
  `DPolyTimeComputable.insertSelf`.
- `unarySwap`, `DUnarySwapTM`, and `dPolyTimeComputable_unary_swap`: a linear-time
  transducer that moves an initial run of `true` bits behind the first `false`
  and the remaining suffix; on an all-`true` word it returns the input unchanged.
  This gives `DPolyTimeComputable.unarySwapPrefix` for rearranging a unary prefix
  produced by an earlier subroutine.  The machine uses an explicit `start` state
  so that the boundary reader cannot mistake the left boundary for the end of
  the input.
- `unarySub`, `DUnarySubTM`, and `dPolyTimeComputable_unary_sub`: a linear-time
  transducer for subtracting the second unary counter from the first.  The
  machine counts the leading `true` run on its work tape, consumes the second
  run after the separator, emits the difference, and finally pads the output to
  length `|x| + 1`.  It uses work-tape cell `0` as a boundary sentinel so that a
  zero-origin mark block can be rewound unambiguously.  This gives
  `DPolyTimeComputable.unarySubPrefix` for subtracting a unary prefix produced
  by an earlier subroutine.
- `dPolyTimeComputable_and_self_var_length`,
  `dPolyTimeComputable_or_self_var_length`, and
  `dPolyTimeComputable_not_var_length`: bounded formula-building examples obtained
  by composing the constructor transducers with the variable-index and doubling
  subroutines.
- `insertVarTagTotal`, `DInsertVarTagTM`, and
  `dPolyTimeComputable_insertVarTagTotal`: insert the variable tag `[false, false]`
  after the first `false` bit.  On `encodeNat i ++ encodeNat j` this produces
  `encodeNat i ++ [false, false] ++ encodeNat j`, the raw pair format needed by
  two-variable literal clauses.
- `insertNotVarTagTotal`, `DInsertNotVarTagTM`, and
  `dPolyTimeComputable_insertNotVarTagTotal`: insert the negated-variable tag
  `[false, true, false, false]` after the first `false` bit.  On
  `encodeNat i ++ encodeNat j` this produces the separator for a negated second
  literal.
- `pairVarVarEncode`, `pairVarNotVarEncode`, `pairNotVarVarEncode`, and
  `pairNotVarNotVarEncode`: fixed-prefix wrappers around the two insertion
  transducers.  Each maps a pair of unary codes to the encoding of one of the
  literal-disjunction shapes occurring in Tseitin constraints, and each has a
  proved `DPolyTimeComputable` theorem.
- `Circuit.encode`, `Circuit.decodeCircuit`, and `Circuit.encode_injective`: a
  prefix code for circuits with a fuel-bounded parser.  The parser is proved to
  invert `encode` on every circuit and suffix, which makes the circuit word a
  canonical intermediate representation for the Cook–Levin assembly.
- `NodeDesc` and `nodeConstraintEncode`: a compact word description of one
  Tseitin constraint.  `nodeDescOfCircuit` supplies the descriptor of a circuit
  node, and `nodeConstraintFormula_nodeDescOfCircuit` proves that the assembled
  formula encoding is exactly `tseitinConstraint`.  This isolates the
  constraint-assembly step from the machine that will enumerate circuit nodes.
- `NodeDescSeq`, `parseNodeDescSeq`, and `nodeConstraintSeqEncode`: a terminated
  sequence of node descriptors that assembles to the encoding of
  `andMany (tseitinConstraints c)`.  `tseitinDescEncode` and `tseitinAssemble`
  add the output-variable index and reconstruct the full `tseitinFormula`.
- `npReductionCoreTseitin` and `npReductionAssemblerTseitin`: a richer pure
  decomposition where the core already carries the Tseitin descriptors and the
  assembler rebuilds the fixed-length SAT instance from them.
  `NPReductionDTMSubroutineObligation_of_tseitin` reduces the DTM obligation to
  polynomial-time computability of these two functions.
- `npReductionCoreDAG` and `npReductionAssemblerDAG`: the sharing-aware variant,
  where the core emits only a unary length plus the DAG descriptors.  Unlike
  `Circuit.encode`, the descriptor sequence is polynomial in `c.size`, as shown
  by `tseitinDescEncode_length_le`.  `npReductionCoreDAG_length_le_poly` gives
  the corresponding polynomial bound for the whole core with respect to
  `npReductionDAGPoly`.  `NodeDescSeq.encode_injective` and
  `nodeDescSeqOfCircuit_nodup` provide parser uniqueness and distinctness of the
  enumerated nodes.  `NPReductionDTMSubroutineObligation_of_dag` reduces the DTM
  obligation to these two functions.
- `npReductionFixedFromCircuit`, `npReductionCore`, and `npReductionAssembler`:
  a pure decomposition of `npReductionFixed`.  The core emits a unary output
  length followed by the encoded verifier circuit; the assembler parses that
  representation and rebuilds the fixed-length SAT instance.
  `npReductionAssembler_core` proves the round trip, and
  `NPReductionDTMSubroutineObligation_of_canonical` reduces the remaining DTM
  obligation to polynomial-time computability of these two functions.
- `DTMPolyTimeBridge`: an explicit proposition connecting the composable model
  to the concrete TM model used by `Reducible`.  It is not assumed.
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
  of P under polynomial-time reductions (see section 9 for the P/poly analogue,
  which is proved).

## Section 7: the 3b route (P ≠ NP via P/poly)

This section starts the disproof route:

- `Circuit`: a Boolean circuit with indexed input variables.
- `Circuit.eval`, `Circuit.nodes`, and a sharing-aware `Circuit.size` that counts
  distinct subcircuits; `Circuit.treeSize` is retained only for comparison.
- `CircuitFamily`, `PolySize`, and `InPPoly`: P/poly as polynomial-size Boolean
  circuit families.
- `TMCompilesToPolyCircuits`: the standard simulation lemma stating that every
  polynomially clocked TM has an equivalent polynomial-size circuit family.
  It is now proved as `tmCompilesToPolyCircuits`.
- `P_subset_PPoly`: the earlier conditional form; `P_subset_PPoly_unconditional`
  derives `P ⊆ P/poly` from the proved compilation theorem.
- `NPNotInPPoly`: the needed lower bound, i.e. some NP language has no
  polynomial-size circuits.
- `NP_not_in_PPoly_implies_not_PEqualsNP`: the conditional implication;
  `NPNotInPPoly_implies_not_PEqualsNP` is the final form with the compilation
  theorem discharged.

The concrete NP lower bound is still open; the Lean file formalizes the implication.

## Section 8: bounded simulation and circuit unrolling

This section starts the construction of `TMCompilesToPolyCircuits`:

- `BConfig`: a bounded configuration with state, head position, and tape vector.
- `binit`, `bhalt`, `bstep`, `bnext`, `brun`, `bacceptsIn`: the bounded machine
  semantics; `bnext` freezes on halting states.
- `SimBits`: circuits representing a bounded configuration bit-by-bit, with
  `SimBits.nodes`/`SimBits.size` counting distinct subcircuits.
- `initBits`, `stepBits`, `unrollBits`, `acceptCircuit`: the actual polynomial
  unrolling construction.
- `StepBitsCorrect`: the local correctness obligation for one transition
  circuit.
- `stepBitsCorrect`: proved theorem — `stepBits` correctly implements one
  bounded transition, including the halting freeze.
- `unrollBits_correct`: proved theorem — correctness of every transition
  circuit implies correctness of the whole unrolled run.
- `cellAt`, `cellAt_step_right`, `cellAt_step_left`: absolute tape-cell indexing
  and one-step shift lemmas for the original TM.
- `Simulates`: the invariant relating an original configuration after `s` steps
  to a bounded configuration whose window has radius `t`.
- `simulates_init`, `simulates_step`, `simulates_more`, `simulates_run_init`:
  proved induction connecting the original and bounded runs for `s ≤ t`.
- `brunsLikeTM`: proved theorem — `BRunsLikeTM`; the bounded run agrees with the
  original TM on every clocked window.
- `step_rel_bound`: proved theorem — one transition introduces only
  polynomially many new distinct circuit nodes (`stepRelBound`).
- `initBits_size_bound`, `stepBits_size_bound`, `unrollBits_size_bound`: proved
  size induction for the unrolled configuration bits.
- `initPoly`, `stepPoly`, `unrollPoly`: mathlib polynomials witnessing the
  size bounds, with `stepPoly` bounding `stepRelBound`.
- `UnrollPolySize`: the size obligation, now discharged by `unrollPolySize`.
- `bounded_unroll_implies_TMCompiles`: proved theorem — the unrolling
  construction gives TM-to-circuit compilation.
- `tmCompilesToPolyCircuits`: the resulting unconditional compilation theorem.

So the original single hypothesis has been decomposed into localized proof
obligations: transition correctness, bounded-run agreement, and polynomial size
are all discharged.  The only open hypothesis in the 3b route is the concrete
NP lower bound `NPNotInPPoly`.

## Section 9: reductions and P/poly closure

The reduction definitions are placed after the bounded-output definition because
`PolyTimeComputable` uses `boutputIn`.

- `Circuit.substVars` replaces input variables by arbitrary circuits.
- `Circuit.eval_substVars` proves that substituting circuits is equivalent to
  evaluating the original circuit on the list of substituted bit values.
- `Circuit.substTop`, `Circuit.nodes_substVars_subset`, and
  `Circuit.size_substVars_le`: a sharing-aware size bound showing that
  substitution multiplies size by a polynomial bound on the inserted circuits.
- `reductionBits`: compiles each bit of a polynomial-time transducer output into
  a circuit, using the already proved `unrollBits_correct`.
- `reductionBits_eval`, `reductionBits_size_le`: correctness and polynomial-size
  bounds for those output-bit circuits.
- `pPolyClosedUnderReductions`: proved theorem — `P/poly` is closed under
  polynomial-time many-one reductions.  It composes the circuit family for the
  target language with the compiled transducer bit circuits.

## Section 10: concrete SAT target

To make the lower bound concrete:

- `Formula`: propositional formulas over numbered variables.
- `Formula.eval` and `Formula.encode`: Boolean semantics and a prefix encoding
  as words.
- `Formula.trueFormula`, `Formula.falseFormula`, `Formula.toCircuit`,
  `toCircuit_eval`, `toCircuit_maxVar_le`, `toCircuit_sat_iff`,
  `toCircuit_treeSize`, `toCircuit_size_le_formulaSize`, `toCircuit_vars`, and
  `Formula.tseitin_encode_length_le_poly`: the reverse bridge from formulas back
  to circuits, preserving evaluation, satisfiability, variable bounds,
  structural size, and polynomial Tseitin output length.
- `Circuit.size_le_treeSize`: the sharing-aware circuit size never exceeds the
  structural tree size.
- `Formula.ofCircuit` and `Formula.ofCircuit_eval`: a direct circuit-to-formula translation preserving
  evaluation.  It is a tree expansion, not the polynomial-size Tseitin
  translation.
- `Circuit.maxVar` and `Circuit.eval_eq_of_agree_on_vars`: circuit evaluation
  only depends on input bits up to the largest variable used.
- `Formula.ofCircuit_maxVar_le`, `circuit_formula_mem_SAT_of_eval_true`,
  `formula_mem_SAT_ofCircuit_eval_true`, and `circuit_formula_SAT_iff`:
  evaluation-preserving circuit-to-formula translation gives an exact
  satisfiability equivalence with SAT.  This translation is a tree expansion;
  see section 12 for the polynomial-size Tseitin translation.
- `SAT`: the language of encoded satisfiable formulas.
- `Formula.mem_SAT_iff_sat`, `Formula.sat_iff_tseitin_toCircuit`, and
  `Formula.mem_SAT_iff_tseitin_toCircuit`: ordinary SAT witnesses are equivalent
  to satisfiability of the Tseitin translation of the formula's structural
  circuit.
- `Formula.mem_SAT_of_eval_true`, `sat_var_zero`, and `sat_tautology`: basic
  SAT membership checks.
- `unsat_contradiction`: an explicit unsatisfiable formula is not in SAT, using
  injectivity of the encoding.
- `Formula.maxVar`: the largest variable index occurring in a formula.
- `Formula.eval_eq_of_agree_on_vars`: evaluation only depends on assignments up
  to `maxVar`.
- `Formula.assign` and `Formula.sat_iff_bounded`: satisfiability of a formula is
  equivalent to satisfiability by an assignment over just its occurring
  variables.
- `Formula.assignments` and `Formula.mem_assignments`: a computable enumeration
  of all assignments on `Fin n`, with `Formula.assignments_length` counting
  them.
- `Formula.sat_iff_bounded_assignments`, `Formula.satSearch`, and
  `Formula.satSearch_eq_true`: a finite Boolean search procedure for
  satisfiability of a fixed formula.
- `Formula.assignOfWord` and its `ofFn`/length lemmas: read a bounded assignment
  from a Boolean certificate word.
- `Formula.maxVar_lt_encode_length`, `Formula.bounded_assignment_mem_SAT`, and
  `Formula.bounded_assignment_length_le`: bounded certificates fit inside a
  polynomial length bound.
- `encodeNat_injective` and `encodeNat_append_cancel`: injectivity and unique
  splitting of the unary-encoded variable indices used by `Formula.encode`.
- `Formula.encode_append_cancel_aux` and `Formula.encode_injective`: formula
  encodings are injective and uniquely split, proved by strong induction on
  total encoded length.
- `Formula.parseNat`, `Formula.parseFuel`, `Formula.parse`,
  `Formula.parseNat_encodeNat`, `Formula.parseFuel_encode`, and
  `Formula.parse_encode`: a computable prefix parser for formula encodings,
  with correctness on `f.encode ++ w`.
- `Formula.parseNat_spec`, `Formula.parseFuel_spec`, `Formula.parse_spec`, and
  `Formula.parse_eq_iff`: the converse parser theorem, so a successful parse
  exactly identifies `f.encode ++ w`.
- `find?_eq_some_of_mem_of_unique` and `find?_pred_of_eq_some`: generic list
  search lemmas used to reason about a finite decoder.
- `Formula.decode`, `Formula.decode_encode`, `Formula.decode_spec`,
  `Formula.decode_eq_iff`, and `Formula.decode_eq_none_iff`: a classical decoder
  for formula encodings.
- `Formula.enum` and `Formula.mem_enum_of_encode_length_le`: a computable finite
  enumeration of formulas up to a given encoding length.
- `Formula.decodeComp`, `Formula.decodeComp_encode`, `Formula.decodeComp_spec`,
  and `Formula.decodeComp_eq_decode`: a computable decoder obtained by searching
  that enumeration and agreeing with the classical decoder.
- `SAT_formula_unique`: the formula witnessing a SAT word is unique.
- `SAT_iff_decode_sat`: SAT membership restated using the classical decoder.
- `SAT_iff_bounded_witness`: SAT membership is equivalent to a bounded
  assignment for the witnessing formula.
- `SAT_bounded_certificate`: every SAT instance has a satisfying certificate
  whose length is at most the input length.
- `SATVerify`, `SATVerify_eq_true_iff`, `SATVerify_sound`, and
  `SATVerify_complete`: a concrete Boolean certificate checker for SAT, with
  soundness and existence of polynomially bounded accepting certificates.  It
  is still not compiled into the concrete TM model.
- `SATVerifyParsed`, `SATVerifyParsed_sound`,
  `SATVerifyParsed_eq_SATVerify`, and `SATVerifyParsed_complete`: a checked
  verifier that rejects malformed instance words by requiring a complete
  formula parse before running the SAT certificate check.
- `SATVerifierTMExists`: the remaining concrete verifier obligation, requiring
  a TM that computes `SATVerify` on input `x ++ cert`.
- `SATVerifierTMExists_implies_SATVerifierExists`: the TM obligation implies
  the abstract `SATVerifierExists` (`SAT ∈ NP`).
- `SATVerifierExists`: the Cook–Levin obligation (`SAT ∈ NP`) in the concrete
  TM model, isolated as an explicit hypothesis.
- `SATNotInPPoly`: the concrete lower bound `SAT ∉ P/poly`.
- `SATNotInPPoly_implies_not_PEqualsNP`: from the verifier hypothesis and
  `SATNotInPPoly`, derive `P ≠ NP`.
- `PPolyClosedUnderReductions`: the closure statement; proved by
  `pPolyClosedUnderReductions` in section 9.
- `SATNPComplete`: Cook–Levin packaged as `NPComplete SAT`.
- `NPNotInPPoly_iff_SATNotInPPoly`: assuming SAT NP-completeness, the abstract
  and concrete lower bounds are equivalent (closure is now discharged).
- `SATNPComplete_and_not_PPoly_implies_not_PEqualsNP`: the final concrete route.

## Section 12: polynomial-size Tseitin translation

The direct `Formula.ofCircuit` bridge is exact but tree-like.  Section 12 adds a
sharing-aware Tseitin translation:

- A computable duplicate-free enumeration `Circuit.nodesList`, proved equivalent
  to the finite set `Circuit.nodes`, gives every distinct circuit node a stable
  fresh variable `auxVar c n = auxOffset c + auxIndex c n`.
- `tseitinConstraint` locally forces the fresh variable of each node to agree
  with the node's Boolean value; `tseitinFormula` conjoins all constraints and
  the output literal.
- `tseitinAssignment` extends an input assignment by evaluating the node
  associated with each fresh variable.  `tseitinConstraint_eval_true` shows
  every local constraint is then satisfied.
- `tseitinFormula_mem_SAT_of_eval_true` and
  `eval_true_of_tseitinFormula_mem_SAT` prove the exact equivalence
  `circuit_tseitin_SAT_iff`: a circuit is satisfiable iff its Tseitin formula
  is in SAT.
- `formulaSize`, `formulaSize_andMany_le_of_bound`, and
  `encode_length_le_formulaSize` bound formula encodings.  With
  `tseitinConstraint_formulaSize_le`, `tseitinFormula_maxVar_le`, and
  `tseitin_encode_length_le`, the Tseitin encoding is polynomial in
  `c.size` and `c.maxVar`, unlike the tree expansion.
- `tseitinPoly` packages that blow-up as a `Polynomial ℕ` bound, proved by
  `tseitin_encode_length_le_poly`.
- `tseitinCertificate` turns a circuit-satisfying input into the corresponding
  bounded SAT assignment.  `tseitinCertificate_verifies` proves that this
  assignment is accepted by the formula checker, and
  `tseitinCertificate_length_le_poly` bounds its length by the same polynomial.

This supplies the semantic and size ingredients for Cook–Levin, but it does not
by itself discharge `SATVerifierTMExists`, `SATNPComplete`, or `SATNotInPPoly`.
Those remain explicit obligations; no lower bound or open result is assumed.

## Section 13: semantic Cook–Levin reduction

The Tseitin translation is now connected to an arbitrary NP verifier at the
circuit level:

- `timeBound_eval_monotone`, `run_add_eq`, `run_eq_of_halted_within`, and
  `acceptsIn_eq_of_halted_within`: monotonicity and stabilization lemmas for
  polynomial time bounds and halting runs.
- `Circuit.maxVar_orMany_le`, `Circuit.maxVar_ite_le`, `Circuit.const_maxVar_le`,
  `Circuit.vars`, `Circuit.mem_vars_le_maxVar`, and
  `Circuit.eval_eq_of_agree_on_vars_finset`: variable-bound and finite-variable
  machinery.  The `vars` formulation handles the zero-certificate case where
  `maxVar` alone is too coarse.
- `word_getD_take_eq_of_lt`: truncation preserves low-index input bits.
- `npInitBits` hardcodes `x` and leaves the certificate `y` as free input bits;
  `npInitBits_correct` proves it agrees with the bounded initial configuration
  whenever `y.length ≤ q.eval x.length`.
- `unrollBitsFrom` starts from an arbitrary bounded bit vector;
  `unrollBitsFrom_correct` proves correctness of the unrolled simulation.
- `npVerifierCircuit` is the resulting verifier circuit.  Its evaluation agrees
  with `acceptsIn V (x ++ y)` for all bounded certificates
  (`npVerifierCircuit_eval_eq_acceptsIn`).
- `SimBits.BoundedVars`, `SimBits.VarsBounded`, `stepBits_boundedVars`, and
  `stepBits_varsBounded` show the unrolling introduces no variables outside the
  certificate range; `npVerifierCircuit_vars_subset` packages this for the
  verifier circuit.
- `npReduction V p q x` is the Tseitin encoding of `npVerifierCircuit V p q x`.
  `npReduction_mem_SAT_iff` proves the exact satisfiability equivalence:
  `npReduction V p q x ∈ SAT` iff some certificate `y` of length at most
  `q.eval x.length` makes the verifier accept.  Truncation to the first
  `q.eval x.length` bits is justified by `Circuit.vars_subset` and
  `Circuit.eval_eq_of_agree_on_vars_finset`.
- `npInitBits_size_bound`, `unrollBitsFrom_size_bound`, and
  `npVerifierCircuit_size_bound` bound the circuit size of the unrolled verifier.
  `npTimePoly p q = p.comp (X + q)` is itself a polynomial, so
  `npCircuitPoly` and `npVerifierCircuit_size_le_poly` give a polynomial size
  bound in `|x|`.
- `maxVar_le_of_vars_subset` and `npReductionOutputPoly` give a polynomial bound
  on the Tseitin output length; `npReduction_length_le_poly` proves
  `|npReduction V p q x| ≤ (npReductionOutputPoly V p q).eval x.length`.
  Polynomial monotonicity is the already proved `timeBound_eval_monotone`.
- `npReductionFixedPoly`, `npReductionFixed`, and `npReductionFixed_length`
  turn the bounded-length reduction into a fixed-length one.  The Tseitin
  formula is conjoined with a fresh variable whose index absorbs the remaining
  slack, so the output length depends only on `|x|`.  This matches the fixed
  output length of `PolyTimeComputable` transducers.
- `Formula.and_var_sat_iff_of_fresh` and
  `npReductionFixed_mem_SAT_iff_accepts` prove that the padding preserves SAT
  membership and the NP acceptance equivalence.
- `NPSemanticReductionIsPolyTime` isolates the reduction-machine step: showing
  the explicit fixed-length word function `npReductionFixed V p q` is computed
  by a polynomial-time TM.  The length bound above makes the obligation
  coherent.  This is separate from `SATVerifierTMExists`, which supplies
  `SAT ∈ NP`.
- `PolyTimeComputableClosedUnderComposition` and
  `NPReductionSubroutineObligation` decompose that machine step in the concrete
  TM model.  In the composable `DTM` model, closure is a proved theorem, and
  `NPReductionDTMSubroutineObligation` asks only for the core encoder and
  assembler.  `DTMPolyTimeBridge` connects the two models, and
  `NPSemanticReductionIsPolyTime_of_DTM` shows that the bridge plus the DTM
  subroutines discharge the concrete reduction obligation.
- `semantic_cook_levin` proves `NPHard SAT` conditional only on that explicit
  machine-realization obligation; it does not assume Cook–Levin.
- `NP_subset_PPoly_of_reduction_and_SAT_in_PPoly` and
  `NPNotInPPoly_implies_SATNotInPPoly_of_reduction` show that the reduction alone
  transfers P/poly membership from SAT to all of NP, and contrapositively moves
  a lower bound from NP to SAT.  These do not need the SAT verifier obligation.

This closes the semantic gap in the 3b route.  The remaining obligations are:

1. `DTMPolyTimeBridge` and `NPReductionDTMSubroutineObligation`: translate the
   proved composable-model reduction into a concrete polynomial-time TM for
   `npReductionFixed`.
2. `SATVerifierTMExists`: a concrete polynomial-time TM for the SAT certificate
   checker on `x ++ cert`, including reliable parsing of the instance prefix.
3. `SATNotInPPoly`: the concrete circuit lower bound for SAT.

All three are explicit propositions, not axioms.  `not_PEqualsNP_of_obligations`
packages them into the final implication.

The file also records the P/poly consequence of an NP-complete language being
in P: `NPComplete_in_P_implies_NP_subset_PPoly` and its specialization
`SAT_in_P_implies_NP_subset_PPoly`.  These use the already proved circuit-level
closure `pPolyClosedUnderReductions`, so no separate machine-composition theorem
is needed for this direction.  In particular,
`SAT_in_P_implies_not_SATNotInPPoly` shows that SAT in P contradicts the
concrete lower-bound hypothesis.

Mathlib's `Computability/TuringMachine` files do contain a constructive chain
from `Computable`/`Partrec` functions to TM2 and then TM1/TM0 machines, but the
pinned library has no theorem promoting that simulation to polynomial time and
even states composition of polynomial-time TM2 computers as `proof_wanted`.
For that reason the concrete `TM`/`PolyTimeComputable` model here remains the
right place to discharge the Cook–Levin machine obligations explicitly.

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
