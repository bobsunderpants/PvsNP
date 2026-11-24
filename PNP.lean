/-
  A formalization of the P versus NP problem in Lean 4 using mathlib.

  Mathlib is used for:
    * `Set` as the type of languages,
    * `Polynomial ℕ` as polynomial running-time bounds,
    * mathlib's polynomial evaluation lemmas and simplifier.

  Contents:
    * a concrete deterministic Turing machine model over the binary alphabet,
    * polynomial bounds on running times,
    * the complexity classes P and NP,
    * the theorem P ⊆ NP (the easy direction),
    * the statement of the open problem P = NP,
    * polynomial-time many-one reductions and NP-completeness.
-/

module

import Mathlib.Algebra.Polynomial.Eval.Defs

namespace PNP

open Polynomial

/-- A word over the binary alphabet. -/
abbrev Word := List Bool

/-- A language is a set of words. -/
abbrev Language := Set Word

-- -----------------------------------------------------------------------------
-- 1. Turing machines
-- -----------------------------------------------------------------------------

/-- A deterministic Turing machine with a single two-way infinite tape.

    States are the finite type `Fin M.numStates`.  The transition function sends
    the current state and the symbol under the head to a new state, a symbol to
    write, and a direction (`true` = right, `false` = left). -/
structure TM where
  numStates : Nat
  step : Fin numStates → Bool → Fin numStates × Bool × Bool
  start : Fin numStates
  accept : Fin numStates
  reject : Fin numStates

/-- A configuration: the finite visible part of the tape is stored as
    `left` (reversed, nearest cell first), the scanned cell `head`, and
    `right` (nearest cell first).  Cells outside `left`/`head`/`right` are blank
    (`false`). -/
structure Config (M : TM) where
  state : Fin M.numStates
  left : List Bool
  head : Bool
  right : List Bool

/-- Initial configuration on input `x`: head over the first symbol of `x`. -/
def init (M : TM) (x : Word) : Config M :=
  match x with
  | [] => ⟨M.start, [], false, []⟩
  | b :: bs => ⟨M.start, [], b, bs⟩

/-- A configuration is halting iff the machine is in an accepting or rejecting state. -/
def halted (M : TM) (c : Config M) : Bool :=
  c.state == M.accept || c.state == M.reject

/-- One transition of the machine. -/
def step (M : TM) (c : Config M) : Config M :=
  let (q', a, dir) := M.step c.state c.head
  if dir then
    match c.right with
    | [] => ⟨q', a :: c.left, false, []⟩
    | b :: bs => ⟨q', a :: c.left, b, bs⟩
  else
    match c.left with
    | [] => ⟨q', [], false, a :: c.right⟩
    | b :: bs => ⟨q', bs, b, a :: c.right⟩

/-- Run the machine for at most `t` transitions.  Once a halting state is
    reached, the configuration no longer changes. -/
def run (M : TM) : Nat → Config M → Config M
  | 0, c => c
  | t + 1, c => if halted M c then c else run M t (step M c)

/-- Does `M` accept `x` within `t` steps? -/
def acceptsIn (M : TM) (x : Word) (t : Nat) : Bool :=
  (run M t (init M x)).state == M.accept

/-- The contents of the tape of a configuration. -/
def Config.tape {M : TM} (c : Config M) : Word :=
  c.left.reverse ++ c.head :: c.right

/-- The word left on the tape after `t` steps (used for transducers). -/
def outputIn (M : TM) (x : Word) (t : Nat) : Word :=
  (run M t (init M x)).tape

-- -----------------------------------------------------------------------------
-- 2. Polynomial bounds
-- -----------------------------------------------------------------------------

/-- A time bound is a polynomial over `ℕ`; the number of available steps on an
    input of length `n` is `p.eval n`.  This uses mathlib's polynomial type. -/
abbrev TimeBound := Polynomial ℕ

/-- If `f` and `g` are bounded by mathlib polynomials `p` and `q`, then
    `f + g` is bounded by the mathlib polynomial `p + q`. -/
lemma poly_add_bound {f g : Nat → Nat} {p q : TimeBound}
    (hf : ∀ n, f n ≤ p.eval n) (hg : ∀ n, g n ≤ q.eval n) :
    ∀ n, f n + g n ≤ (p + q).eval n := by
  intro n
  simpa using Nat.add_le_add (hf n) (hg n)

-- -----------------------------------------------------------------------------
-- 3. The classes P and NP
-- -----------------------------------------------------------------------------

/-- `L ∈ P`: some deterministic Turing machine halts on every input within a
    polynomially bounded number of steps and decides `L`. -/
def InP (L : Language) : Prop :=
  ∃ (M : TM) (p : TimeBound),
    (∀ x : Word, halted M (run M (p.eval x.length) (init M x)) = true) ∧
    ∀ x : Word, acceptsIn M x (p.eval x.length) = true ↔ x ∈ L

/-- `L ∈ NP`: there is a polynomially bounded certificate `y` and a
    deterministic polynomial-time verifier `V` which halts on every input
    `x ++ y` such that `x ∈ L` iff some certificate makes `V` accept. -/
def InNP (L : Language) : Prop :=
  ∃ (V : TM) (p q : TimeBound),
    (∀ x y : Word,
      halted V (run V (p.eval (x ++ y).length) (init V (x ++ y))) = true) ∧
    ∀ x : Word, x ∈ L ↔
      ∃ y : Word, y.length ≤ q.eval x.length ∧
        acceptsIn V (x ++ y) (p.eval (x ++ y).length) = true

/-- The easy inclusion: a polynomial-time decider is a verifier that ignores
    the (empty) certificate. -/
theorem inP_subset_inNP : ∀ L : Language, InP L → InNP L := by
  intro L h
  rcases h with ⟨M, p, hhalt, hM⟩
  refine ⟨M, p, 0, ?_, ?_⟩
  · intro x y
    exact hhalt (x ++ y)
  · intro x
    constructor
    · intro hx
      refine ⟨[], by simp, ?_⟩
      simpa using (hM x).2 hx
    · rintro ⟨y, hy, hyacc⟩
      cases y with
      | nil =>
          exact (hM x).1 (by simpa using hyacc)
      | cons b bs =>
          simp at hy

-- -----------------------------------------------------------------------------
-- 4. The question
-- -----------------------------------------------------------------------------

/-- The complexity classes P and NP, as mathlib sets of languages. -/
def PClass : Set Language := {L | InP L}

def NPClass : Set Language := {L | InNP L}

/-- The P versus NP problem: the two sets of languages are equal. -/
def PEqualsNP : Prop := PClass = NPClass

/-- Since P ⊆ NP is provable, `P = NP` is equivalent to the converse inclusion. -/
theorem PEqualsNP_iff_inclusion :
    PEqualsNP ↔ ∀ L : Language, InNP L → InP L := by
  constructor
  · intro h L hL
    have : L ∈ PClass := by
      rw [h]
      exact hL
    exact this
  · intro h
    apply Set.ext
    intro L
    constructor
    · intro hP
      exact inP_subset_inNP L hP
    · intro hNP
      exact h L hNP

-- -----------------------------------------------------------------------------
-- 5. Reductions and NP-completeness
-- -----------------------------------------------------------------------------

/-- A word function is polynomial-time computable if some Turing machine
    writes it on the tape within a polynomially bounded number of steps. -/
def PolyTimeComputable (f : Word → Word) : Prop :=
  ∃ (M : TM) (p : TimeBound),
    (∀ x : Word, halted M (run M (p.eval x.length) (init M x)) = true) ∧
    ∀ x : Word, outputIn M x (p.eval x.length) = f x

/-- Many-one reduction: `L₁ ≤ₚ L₂` if a polynomial-time computable `f` maps
    positive instances of `L₁` to positive instances of `L₂` and negative ones
    to negative ones. -/
def Reducible (L₁ L₂ : Language) : Prop :=
  ∃ f : Word → Word, PolyTimeComputable f ∧ ∀ x : Word, (f x ∈ L₂ ↔ x ∈ L₁)

/-- NP-hardness and NP-completeness. -/
def NPHard (L : Language) : Prop := ∀ L' : Language, InNP L' → Reducible L' L

def NPComplete (L : Language) : Prop := InNP L ∧ NPHard L

/-- P is closed under polynomial-time many-one reductions.  This is stated as
    a separate hypothesis because proving it requires a (standard but lengthy)
    machine-composition construction. -/
def ClosedPUnderReductions : Prop :=
  ∀ L₁ L₂ : Language, InP L₂ → Reducible L₁ L₂ → InP L₁

/-- Cook's reduction principle: if one NP-complete language is in P, then
    P = NP (assuming the standard closure of P under reductions). -/
theorem NPComplete_in_P_implies_PEqualsNP
    (hclosed : ClosedPUnderReductions) {L : Language}
    (hc : NPComplete L) (hL : InP L) : PEqualsNP := by
  rw [PEqualsNP_iff_inclusion]
  intro L' hL'
  exact hclosed L' L hL (hc.2 L' hL')

-- -----------------------------------------------------------------------------
-- 6. Two trivial examples (sanity checks for the machine model)
-- -----------------------------------------------------------------------------

/-- A machine that immediately rejects. -/
def rejectTM : TM where
  numStates := 3
  step := fun _ _ => (2, false, true)
  start := 0
  accept := 1
  reject := 2

/-- A machine that immediately accepts. -/
def acceptTM : TM where
  numStates := 3
  step := fun _ _ => (1, false, true)
  start := 0
  accept := 1
  reject := 2

lemma rejectTM_halts (x : Word) :
    halted rejectTM (run rejectTM 1 (init rejectTM x)) = true := by
  cases x with
  | nil => simp [run, init, rejectTM, halted, step]
  | cons b bs => cases bs <;> simp [run, init, rejectTM, halted, step]

lemma acceptTM_halts (x : Word) :
    halted acceptTM (run acceptTM 1 (init acceptTM x)) = true := by
  cases x with
  | nil => simp [run, init, acceptTM, halted, step]
  | cons b bs => cases bs <;> simp [run, init, acceptTM, halted, step]

example : InP (∅ : Language) := by
  refine ⟨rejectTM, 1, ?_, ?_⟩
  · intro x
    simpa using rejectTM_halts x
  intro x
  constructor
  · intro hacc
    cases x with
    | nil => simp [acceptsIn, run, init, rejectTM, halted, step] at hacc
    | cons b bs => cases bs <;> simp [acceptsIn, run, init, rejectTM, halted, step] at hacc
  · intro hx
    exact False.elim hx

example : InP (Set.univ : Language) := by
  refine ⟨acceptTM, 1, ?_, ?_⟩
  · intro x
    simpa using acceptTM_halts x
  intro x
  constructor
  · intro _; trivial
  · intro _
    cases x with
    | nil => simp [acceptsIn, run, init, acceptTM, halted, step]
    | cons b bs => cases bs <;> simp [acceptsIn, run, init, acceptTM, halted, step]

-- -----------------------------------------------------------------------------
-- 7. Boolean circuits and P/poly
-- -----------------------------------------------------------------------------

/-- A Boolean circuit with indexed input variables. -/
inductive Circuit where
  | const (b : Bool) : Circuit
  | var (i : Nat) : Circuit
  | not (c : Circuit) : Circuit
  | and (c₁ c₂ : Circuit) : Circuit
  | or (c₁ c₂ : Circuit) : Circuit
  deriving Repr

namespace Circuit

/-- Evaluate a circuit on a word; missing input bits are read as `false`. -/
def eval : Circuit → Word → Bool
  | const b, _ => b
  | var i, x => x.getD i false
  | not c, x => Bool.not (c.eval x)
  | and c₁ c₂, x => Bool.and (c₁.eval x) (c₂.eval x)
  | or c₁ c₂, x => Bool.or (c₁.eval x) (c₂.eval x)

/-- Number of gates in a circuit. -/
def size : Circuit → Nat
  | const _ => 1
  | var _ => 1
  | not c => 1 + c.size
  | and c₁ c₂ => 1 + c₁.size + c₂.size
  | or c₁ c₂ => 1 + c₁.size + c₂.size

/-- If-then-else as a derived circuit. -/
def ite (c t e : Circuit) : Circuit :=
  or (and c t) (and (not c) e)

/-- OR of a list of circuits. -/
def orMany : List Circuit → Circuit
  | [] => const false
  | c :: cs => or c (orMany cs)

@[simp] lemma eval_const (b : Bool) (x : Word) : (const b).eval x = b := rfl
@[simp] lemma eval_var (i : Nat) (x : Word) : (var i).eval x = x.getD i false := rfl
@[simp] lemma eval_not (c : Circuit) (x : Word) : (not c).eval x = Bool.not (c.eval x) := rfl
@[simp] lemma eval_and (c₁ c₂ : Circuit) (x : Word) :
    (and c₁ c₂).eval x = Bool.and (c₁.eval x) (c₂.eval x) := rfl
@[simp] lemma eval_or (c₁ c₂ : Circuit) (x : Word) :
    (or c₁ c₂).eval x = Bool.or (c₁.eval x) (c₂.eval x) := rfl

@[simp] lemma eval_ite (c t e : Circuit) (x : Word) :
    (ite c t e).eval x = if c.eval x then t.eval x else e.eval x := by
  cases hc : c.eval x <;> simp [ite, hc]

@[simp] lemma eval_orMany_nil (x : Word) : (orMany []).eval x = false := rfl
@[simp] lemma eval_orMany_cons (c : Circuit) (cs : List Circuit) (x : Word) :
    (orMany (c :: cs)).eval x = Bool.or (c.eval x) ((orMany cs).eval x) := rfl

@[simp] lemma size_const (b : Bool) : (const b).size = 1 := rfl
@[simp] lemma size_var (i : Nat) : (var i).size = 1 := rfl
@[simp] lemma size_not (c : Circuit) : (not c).size = 1 + c.size := rfl
@[simp] lemma size_and (c₁ c₂ : Circuit) : (and c₁ c₂).size = 1 + c₁.size + c₂.size := rfl
@[simp] lemma size_or (c₁ c₂ : Circuit) : (or c₁ c₂).size = 1 + c₁.size + c₂.size := rfl

end Circuit

/-- A family of Boolean circuits, one circuit for each input length. -/
abbrev CircuitFamily := Nat → Circuit

/-- A circuit family has polynomial size if its `n`-th circuit has at most
    `p.eval n` gates for some mathlib polynomial `p`. -/
def PolySize (F : CircuitFamily) : Prop :=
  ∃ p : TimeBound, ∀ n : Nat, (F n).size ≤ p.eval n

/-- `L ∈ P/poly`: a polynomial-size circuit family decides `L`. -/
def InPPoly (L : Language) : Prop :=
  ∃ F : CircuitFamily,
    PolySize F ∧ ∀ x : Word, (F x.length).eval x = true ↔ x ∈ L

/-- The remaining simulation lemma for the 3b route: every polynomially
    clocked TM has an equivalent polynomial-size circuit family.  This is the
    standard unrolling of a polynomial number of transition steps. -/
def TMCompilesToPolyCircuits : Prop :=
  ∀ (M : TM) (p : TimeBound),
    (∀ x : Word, halted M (run M (p.eval x.length) (init M x)) = true) →
    ∃ F : CircuitFamily,
      PolySize F ∧ ∀ x : Word, (F x.length).eval x = acceptsIn M x (p.eval x.length)

/-- From the simulation lemma, P ⊆ P/poly. -/
theorem P_subset_PPoly (hcompile : TMCompilesToPolyCircuits) :
    ∀ L : Language, InP L → InPPoly L := by
  intro L hL
  rcases hL with ⟨M, p, hhalt, hM⟩
  rcases hcompile M p hhalt with ⟨F, hFsize, hFcorrect⟩
  refine ⟨F, hFsize, ?_⟩
  intro x
  rw [hFcorrect x]
  exact hM x

/-- The lower bound needed for the disproof route: some NP language has no
    polynomial-size circuit family. -/
def NPNotInPPoly : Prop :=
  ∃ L : Language, InNP L ∧ ¬ InPPoly L

/-- If an NP language is outside P/poly, then P ≠ NP. -/
theorem NP_not_in_PPoly_implies_not_PEqualsNP
    (hcompile : TMCompilesToPolyCircuits) :
    NPNotInPPoly → ¬ PEqualsNP := by
  rintro ⟨L, hLNP, hLnot⟩ hEq
  have hIncl : ∀ L' : Language, InNP L' → InP L' :=
    (PEqualsNP_iff_inclusion.mp hEq)
  exact hLnot (P_subset_PPoly hcompile L (hIncl L hLNP))

-- -----------------------------------------------------------------------------
-- 8. Bounded simulation and circuit unrolling
-- -----------------------------------------------------------------------------

/-- A bounded configuration used for circuit compilation.  Tape cell `i`
    represents tape displacement `i - t` from the initial head position. -/
structure BConfig (M : TM) (t : Nat) where
  state : Fin M.numStates
  pos : Fin (2 * t + 1)
  tape : Fin (2 * t + 1) → Bool

/-- Initial bounded configuration on input `x`. -/
def binit (M : TM) (t : Nat) (x : Word) : BConfig M t where
  state := M.start
  pos := ⟨t, by omega⟩
  tape i :=
    if t ≤ i.val ∧ i.val < t + x.length then
      x.getD (i.val - t) false
    else
      false

/-- A bounded configuration is halting iff its state is accept or reject. -/
def bhalt (M : TM) (c : BConfig M t) : Bool :=
  c.state == M.accept || c.state == M.reject

/-- One bounded transition.  Head movement saturates at the boundary of the
    window; runs of length at most `t` never need to move outside it. -/
def bstep (M : TM) (t : Nat) (c : BConfig M t) : BConfig M t :=
  let a := c.tape c.pos
  let tr := M.step c.state a
  let nextPos : Nat :=
    if tr.2.2 then
      if c.pos.val < 2 * t then c.pos.val + 1 else c.pos.val
    else
      if 0 < c.pos.val then c.pos.val - 1 else c.pos.val
  { state := tr.1
    pos := ⟨nextPos, by
      dsimp [nextPos]
      split <;> split <;> omega⟩
    tape := fun i => if i.val == c.pos.val then tr.2.1 else c.tape i }

/-- One bounded transition, freezing on halting states. -/
def bnext (M : TM) (t : Nat) (c : BConfig M t) : BConfig M t :=
  if bhalt M c then c else bstep M t c

/-- Run the bounded machine for `s` steps. -/
def brun (M : TM) (t : Nat) : Nat → BConfig M t → BConfig M t
  | 0, c => c
  | s + 1, c => bnext M t (brun M t s c)

/-- Acceptance in the bounded model. -/
def bacceptsIn (M : TM) (t s : Nat) (x : Word) : Bool :=
  (brun M t s (binit M t x)).state == M.accept

/-- Boolean vectors of circuits representing a bounded configuration. -/
structure SimBits (S N : Nat) where
  state : Fin S → Circuit
  head : Fin N → Circuit
  tape : Fin N → Circuit

namespace SimBits

/-- Total circuit size of a bounded-configuration bit vector. -/
def totalSize (b : SimBits S N) : Nat :=
  ((List.ofFn b.state).map Circuit.size).sum +
    ((List.ofFn b.head).map Circuit.size).sum +
      ((List.ofFn b.tape).map Circuit.size).sum

end SimBits

/-- Circuit bits for the initial bounded configuration on inputs of length `n`. -/
def initBits (M : TM) (t n : Nat) : SimBits M.numStates (2 * t + 1) where
  state q := Circuit.const (M.start == q)
  head i := Circuit.const (i.val == t)
  tape i :=
    if t ≤ i.val ∧ i.val < t + n then
      Circuit.var (i.val - t)
    else
      Circuit.const false

/-- Circuit bits for one bounded transition, freezing after halting. -/
def stepBits (M : TM) (t : Nat) (b : SimBits M.numStates (2 * t + 1)) :
    SimBits M.numStates (2 * t + 1) :=
  let haltedBits := Circuit.or (b.state M.accept) (b.state M.reject)
  let scan :=
    Circuit.orMany (List.ofFn fun i : Fin (2 * t + 1) =>
      Circuit.and (b.head i) (b.tape i))
  let dirRight :=
    Circuit.orMany (List.ofFn fun q : Fin M.numStates =>
      Circuit.and (b.state q)
        (Circuit.ite scan
          (Circuit.const (M.step q true).2.2)
          (Circuit.const (M.step q false).2.2)))
  let writeBit :=
    Circuit.orMany (List.ofFn fun q : Fin M.numStates =>
      Circuit.and (b.state q)
        (Circuit.ite scan
          (Circuit.const (M.step q true).2.1)
          (Circuit.const (M.step q false).2.1)))
  let nextState : Fin M.numStates → Circuit := fun q' =>
    Circuit.orMany (List.ofFn fun q : Fin M.numStates =>
      Circuit.and (b.state q)
        (Circuit.ite scan
          (Circuit.const ((M.step q true).1 == q'))
          (Circuit.const ((M.step q false).1 == q'))))
  let nextHead : Fin (2 * t + 1) → Circuit := fun i =>
    Circuit.orMany (List.ofFn fun j : Fin (2 * t + 1) =>
      Circuit.and (b.head j)
        (Circuit.ite dirRight
          (Circuit.const (j.val + 1 == i.val))
          (Circuit.const (i.val + 1 == j.val))))
  let nextTape : Fin (2 * t + 1) → Circuit := fun i =>
    Circuit.or (Circuit.and (b.head i) writeBit)
      (Circuit.and (Circuit.not (b.head i)) (b.tape i))
  { state := fun q' => Circuit.ite haltedBits (b.state q') (nextState q')
    head := fun i => Circuit.ite haltedBits (b.head i) (nextHead i)
    tape := fun i => Circuit.ite haltedBits (b.tape i) (nextTape i) }

/-- Unroll `s` transition circuits starting from the initial configuration. -/
def unrollBits (M : TM) (t n : Nat) : Nat → SimBits M.numStates (2 * t + 1)
  | 0 => initBits M t n
  | s + 1 => stepBits M t (unrollBits M t n s)

/-- The accept-state circuit of a bounded bit vector. -/
def acceptCircuit (M : TM) (t : Nat) (b : SimBits M.numStates (2 * t + 1)) : Circuit :=
  b.state M.accept

/-- Correctness obligation for one transition circuit.  This is a local lemma:
    it only relates `stepBits` to `bnext` for one configuration. -/
def StepBitsCorrect (M : TM) (t : Nat) : Prop :=
  ∀ (x : Word) (c : BConfig M t) (b : SimBits M.numStates (2 * t + 1)),
    (∀ q : Fin M.numStates, (b.state q).eval x = (c.state == q)) →
    (∀ i : Fin (2 * t + 1), (b.head i).eval x = (c.pos == i)) →
    (∀ i : Fin (2 * t + 1), (b.tape i).eval x = c.tape i) →
    let c' := bnext M t c
    let b' := stepBits M t b
    (∀ q : Fin M.numStates, (b'.state q).eval x = (c'.state == q)) ∧
      (∀ i : Fin (2 * t + 1), (b'.head i).eval x = (c'.pos == i)) ∧
        (∀ i : Fin (2 * t + 1), (b'.tape i).eval x = c'.tape i)

/-- If each transition circuit is correct, the unrolled circuit correctly
    represents the bounded run. -/
theorem unrollBits_correct (M : TM) (t : Nat) (hstep : StepBitsCorrect M t)
    (x : Word) (s : Nat) :
    let b := unrollBits M t x.length s
    let c := brun M t s (binit M t x)
    (∀ q : Fin M.numStates, (b.state q).eval x = (c.state == q)) ∧
      (∀ i : Fin (2 * t + 1), (b.head i).eval x = (c.pos == i)) ∧
        (∀ i : Fin (2 * t + 1), (b.tape i).eval x = c.tape i) := by
  induction s with
  | zero =>
      dsimp [unrollBits, brun]
      constructor
      · intro q
        simp [initBits, binit]
      · constructor
        · intro i
          simp [initBits, binit, Fin.ext_iff, eq_comm]
        · intro i
          by_cases h : t ≤ i.val ∧ i.val < t + x.length <;>
            simp [initBits, binit, h]
  | succ s ih =>
      dsimp at ih
      dsimp [unrollBits, brun]
      exact hstep x (brun M t s (binit M t x)) (unrollBits M t x.length s)
        ih.1 ih.2.1 ih.2.2

/-- The bounded simulation agrees with the original TM for clocked runs. -/
def BRunsLikeTM : Prop :=
  ∀ (M : TM) (p : TimeBound),
    (∀ x : Word, halted M (run M (p.eval x.length) (init M x)) = true) →
      ∀ x : Word,
        bacceptsIn M (p.eval x.length) (p.eval x.length) x =
          acceptsIn M x (p.eval x.length)

/-- The size obligation for the unrolled accept circuit. -/
def UnrollPolySize : Prop :=
  ∀ (M : TM) (p : TimeBound),
    ∃ P : TimeBound, ∀ n : Nat,
      (acceptCircuit M (p.eval n) (unrollBits M (p.eval n) n (p.eval n))).size ≤ P.eval n

/-- Assembling the bounded obligations gives the original compilation lemma. -/
theorem bounded_unroll_implies_TMCompiles
    (hstep : ∀ M t, StepBitsCorrect M t)
    (hsize : UnrollPolySize)
    (hbrun : BRunsLikeTM) : TMCompilesToPolyCircuits := by
  intro M p hhalt
  let F : CircuitFamily := fun n =>
    acceptCircuit M (p.eval n) (unrollBits M (p.eval n) n (p.eval n))
  refine ⟨F, hsize M p, ?_⟩
  intro x
  dsimp [F, acceptCircuit]
  have hc := unrollBits_correct M (p.eval x.length) (hstep M (p.eval x.length)) x (p.eval x.length)
  dsimp at hc
  rw [hc.1 M.accept]
  exact hbrun M p hhalt x

end PNP
