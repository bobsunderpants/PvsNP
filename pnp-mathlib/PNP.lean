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
import Mathlib.Data.List.GetD
import Mathlib.Order.Nat

namespace PNP

open Polynomial

/-- A word over the binary alphabet. -/
abbrev Word := List Bool

/-- A language is a set of words. -/
abbrev Language := Set Word

/-- `find?` returns a satisfying element when the satisfying element is unique. -/
lemma find?_eq_some_of_mem_of_unique {α : Type} (p : α → Bool)
    (huniq : ∀ a b, p a = true → p b = true → a = b)
    {l : List α} {a : α} (ha : a ∈ l) (hpa : p a = true) :
    l.find? p = some a := by
  induction l with
  | nil => simp at ha
  | cons y ys ih =>
      by_cases hy : p y = true
      · have hya : y = a := huniq y a hy hpa
        subst y
        simp [List.find?, hpa]
      · have hne : a ≠ y := by
          intro h
          subst a
          exact hy hpa
        simp at ha
        rcases ha with h | h
        · subst a
          contradiction
        · simp [List.find?, hy, ih h]

/-- The result of `find?` satisfies the predicate. -/
lemma find?_pred_of_eq_some {α : Type} (p : α → Bool)
    {l : List α} {a : α} (h : l.find? p = some a) : p a = true := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
      by_cases hy : p y = true
      · simp [List.find?, hy] at h
        subst a
        exact hy
      · simp [List.find?, hy] at h
        exact ih h

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

/-- One transition increases the visible tape length by at most one. -/
lemma step_tape_length_le (M : TM) (c : Config M) :
    (step M c).tape.length ≤ c.tape.length + 1 := by
  rcases htr : M.step c.state c.head with ⟨q', w, dir⟩
  cases dir
  · cases hL : c.left with
    | nil =>
        simp [step, Config.tape, htr, hL]
    | cons b bs =>
        simp [step, Config.tape, htr, hL, List.length_reverse]
  · cases hR : c.right with
    | nil =>
        simp [step, Config.tape, htr, hR]
    | cons b bs =>
        simp [step, Config.tape, htr, hR, List.length_reverse]

/-- After `t` transitions the visible tape length grows by at most `t`. -/
lemma run_tape_length_le (M : TM) (t : Nat) (c : Config M) :
    (run M t c).tape.length ≤ c.tape.length + t := by
  induction t generalizing c with
  | zero => simp [run]
  | succ t ih =>
      by_cases hh : halted M c
      · simp [run, hh]
      · simp [run, hh]
        have hs := step_tape_length_le M c
        have hi := ih (step M c)
        omega

lemma init_tape_length_le (M : TM) (x : Word) :
    (init M x).tape.length ≤ x.length + 1 := by
  cases x <;> simp [init, Config.tape]

/-- The output tape after `t` steps has length at most `|x| + 1 + t`. -/
lemma output_length_le (M : TM) (x : Word) (t : Nat) :
    (outputIn M x t).length ≤ x.length + 1 + t := by
  have h := run_tape_length_le M t (init M x)
  have hi := init_tape_length_le M x
  dsimp [outputIn]
  omega

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

/-- Polynomials over `ℕ` evaluate monotonically.  This is needed when a
    certificate is shorter than its maximum allowed length. -/
lemma timeBound_eval_monotone (p : TimeBound) {a b : Nat} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial n c =>
      simpa [Polynomial.eval_monomial] using
        Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)

-- -----------------------------------------------------------------------------
-- 2b. A composable transducer model
-- -----------------------------------------------------------------------------

/-- One transition of a composable transducer: the next state, an optional
    output bit, the input-head movement, an optional work-tape write, and the
    work-head movement.  A movement is `some true` for right, `some false` for
    left, and `none` for staying put. -/
structure DAction (σ : Type) where
  next : σ
  output : Option Bool
  inputMove : Option Bool
  workWrite : Option Bool
  workMove : Option Bool

/-- A composable transducer: a read-only input word, a write-only output word,
    and a two-way infinite work tape.  Both heads start on distinguished left
    boundaries.  The `handoff` instruction resets the input to the current
    output, clears the output, and blanks the work tape, which is exactly what
    sequential composition needs. -/
structure DTM (σ : Type) [Fintype σ] [DecidableEq σ] where
  step : σ → Option Bool → Bool → DAction σ
  handoff : σ → Bool := fun _ => false
  start : σ
  accept : σ
  reject : σ

/-- A configuration of a transducer. -/
structure DConfig (σ : Type) where
  state : σ
  input : Word
  head : Nat
  output : Word
  work : Nat → Bool
  workHead : Nat

/-- Initial configuration: both heads on their boundaries, input immediately to
    the right of the input boundary, work tape blank. -/
def Dinit {σ : Type} [Fintype σ] [DecidableEq σ] (M : DTM σ) (x : Word) : DConfig σ :=
  ⟨M.start, x, 0, [], fun _ => false, 0⟩

/-- A transducer halts in its accepting or rejecting state. -/
def Dhalted {σ : Type} [Fintype σ] [DecidableEq σ] (M : DTM σ) (c : DConfig σ) : Bool :=
  decide (c.state = M.accept) || decide (c.state = M.reject)

/-- The symbol currently scanned by the input head.  The left boundary and any
    position past the end of the input are both represented by `none`. -/
def Dread {σ : Type} (c : DConfig σ) : Option Bool :=
  if c.head = 0 then none else c.input[c.head - 1]?

/-- Move a head one cell, reflecting at the distinguished boundary. -/
def Dmove (dir : Bool) (h : Nat) : Nat :=
  if dir then h + 1 else if h = 0 then 0 else h - 1

/-- Write an optional bit to the work tape. -/
def DwriteWork (f : Nat → Bool) (h : Nat) (w : Option Bool) : Nat → Bool :=
  fun i => match w with
    | none => f i
    | some b => if i = h then b else f i

@[simp] lemma DwriteWork_none (f : Nat → Bool) (h : Nat) : DwriteWork f h none = f := by
  funext i
  simp [DwriteWork]

/-- One transition.  The output word is append-only and the work tape is
    persistent unless a handoff occurs. -/
def Dstep {σ : Type} [Fintype σ] [DecidableEq σ] (M : DTM σ) (c : DConfig σ) : DConfig σ :=
  let sym := Dread c
  let tr := M.step c.state sym (c.work c.workHead)
  let hand := M.handoff c.state
  let input' := if hand then c.output else c.input
  let head' := if hand then 0 else match tr.inputMove with
    | none => c.head
    | some dir => Dmove dir c.head
  let output' := if hand then [] else match tr.output with
    | none => c.output
    | some b => c.output ++ [b]
  let work' := if hand then (fun _ => false) else DwriteWork c.work c.workHead tr.workWrite
  let workHead' := if hand then 0 else match tr.workMove with
    | none => c.workHead
    | some dir => Dmove dir c.workHead
  ⟨tr.next, input', head', output', work', workHead'⟩

/-- Run a transducer for at most `t` steps, freezing on halt. -/
def Drun {σ : Type} [Fintype σ] [DecidableEq σ] (M : DTM σ) : Nat → DConfig σ → DConfig σ
  | 0, c => c
  | t + 1, c => if Dhalted M c then c else Drun M t (Dstep M c)

/-- The bounded output word. -/
abbrev Dboutput {σ : Type} [Fintype σ] [DecidableEq σ]
    (M : DTM σ) (t : Nat) (x : Word) : Word :=
  (Drun M t (Dinit M x)).output

/-- The first `m` output bits, padded with `false` when shorter. -/
def DboutputUpTo {σ : Type} [Fintype σ] [DecidableEq σ]
    (M : DTM σ) (t m : Nat) (x : Word) : Word :=
  List.ofFn (fun i : Fin m => (Drun M t (Dinit M x)).output.getD i.val false)

@[simp] lemma DboutputUpTo_length {σ : Type} [Fintype σ] [DecidableEq σ]
    (M : DTM σ) (t m : Nat) (x : Word) : (DboutputUpTo M t m x).length = m := by
  simp [DboutputUpTo]

/-- One transition with halting configurations frozen. -/
def DnextConfig {σ : Type} [Fintype σ] [DecidableEq σ]
    (M : DTM σ) (c : DConfig σ) : DConfig σ :=
  if Dhalted M c then c else Dstep M c

lemma Drun_halted {σ : Type} [Fintype σ] [DecidableEq σ]
    (M : DTM σ) (c : DConfig σ) (k : Nat) (h : Dhalted M c = true) :
    Drun M k c = c := by
  cases k <;> simp [Drun, h]

lemma Drun_succ_eq_run_nextConfig {σ : Type} [Fintype σ] [DecidableEq σ]
    (M : DTM σ) (c : DConfig σ) (k : Nat) :
    Drun M (k + 1) c = Drun M k (DnextConfig M c) := by
  by_cases h : Dhalted M c = true
  · simp [Drun, h, DnextConfig, Drun_halted M c k h]
  · simp [Drun, h, DnextConfig]

lemma Drun_add_eq {σ : Type} [Fintype σ] [DecidableEq σ]
    (M : DTM σ) (c : DConfig σ) (a b : Nat) :
    Drun M (a + b) c = Drun M b (Drun M a c) := by
  induction a generalizing c with
  | zero => simp [Drun]
  | succ a ih =>
      rw [Nat.succ_add, Drun_succ_eq_run_nextConfig]
      rw [Drun_succ_eq_run_nextConfig M c a]
      exact ih (DnextConfig M c)

lemma Drun_eq_of_halted_within {σ : Type} [Fintype σ] [DecidableEq σ]
    (M : DTM σ) (c : DConfig σ) {s t : Nat} (hs : s ≤ t)
    (hh : Dhalted M (Drun M s c) = true) : Drun M t c = Drun M s c := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
  rw [hk, Drun_add_eq, Drun_halted M (Drun M s c) k hh]

/-- Polynomial-time computability in the composable model.  `p` bounds the
    running time and `r` bounds the output length. -/
def DPolyTimeComputable (f : Word → Word) : Prop :=
  ∃ (σ : Type) (_instσ : Fintype σ) (_decσ : DecidableEq σ)
    (M : DTM σ) (p r : TimeBound),
    (∀ x : Word, Dhalted M (Drun M (p.eval x.length) (Dinit M x)) = true) ∧
    ∀ x : Word,
      Dboutput M (p.eval x.length) x = f x ∧ (f x).length = r.eval x.length

/-- States of a sequential composition: first subroutine, then second. -/
inductive DCompState (σ τ : Type) where
  | first : σ → DCompState σ τ
  | second : τ → DCompState σ τ
  deriving DecidableEq

namespace DCompState

def toSum {σ τ : Type} : DCompState σ τ → σ ⊕ τ
  | first q => Sum.inl q
  | second q => Sum.inr q

def ofSum {σ τ : Type} : σ ⊕ τ → DCompState σ τ
  | Sum.inl q => first q
  | Sum.inr q => second q

lemma ofSum_toSum {σ τ : Type} (s : DCompState σ τ) : ofSum (toSum s) = s := by
  cases s <;> rfl

lemma toSum_ofSum {σ τ : Type} (s : σ ⊕ τ) : toSum (ofSum s) = s := by
  cases s <;> rfl

def finEquiv {σ τ : Type} : DCompState σ τ ≃ σ ⊕ τ where
  toFun := toSum
  invFun := ofSum
  left_inv := ofSum_toSum
  right_inv := toSum_ofSum

instance fintype {σ τ : Type} [Fintype σ] [Fintype τ] : Fintype (DCompState σ τ) :=
  Fintype.ofEquiv (σ ⊕ τ) finEquiv.symm

end DCompState

/-- Sequential composition.  The first phase mirrors `M`; when `M` halts, the
    composed machine hands its output to `N` and the second phase mirrors `N`. -/
def Dcompose {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
    (M : DTM σ) (N : DTM τ) : DTM (DCompState σ τ) where
  step
    | DCompState.first q, sym, wsym =>
        if decide (q = M.accept) || decide (q = M.reject) then
          { next := DCompState.second N.start, output := none, inputMove := none
            workWrite := none, workMove := none }
        else
          let tr := M.step q sym wsym
          { next := DCompState.first tr.next, output := tr.output
            inputMove := tr.inputMove, workWrite := tr.workWrite, workMove := tr.workMove }
    | DCompState.second q, sym, wsym =>
        if decide (q = N.accept) || decide (q = N.reject) then
          { next := DCompState.second q, output := none, inputMove := none
            workWrite := none, workMove := none }
        else
          let tr := N.step q sym wsym
          { next := DCompState.second tr.next, output := tr.output
            inputMove := tr.inputMove, workWrite := tr.workWrite, workMove := tr.workMove }
  handoff
    | DCompState.first q => M.handoff q || (decide (q = M.accept) || decide (q = M.reject))
    | DCompState.second q => N.handoff q
  start := DCompState.first M.start
  accept := DCompState.second N.accept
  reject := DCompState.second N.reject

def liftFirst {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
    (_M : DTM σ) (_N : DTM τ) (c : DConfig σ) : DConfig (DCompState σ τ) :=
  ⟨DCompState.first c.state, c.input, c.head, c.output, c.work, c.workHead⟩

def liftSecond {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
    (_M : DTM σ) (_N : DTM τ) (c : DConfig τ) : DConfig (DCompState σ τ) :=
  ⟨DCompState.second c.state, c.input, c.head, c.output, c.work, c.workHead⟩

lemma Dhalted_compose_liftFirst {σ τ : Type} [Fintype σ] [DecidableEq σ]
    [Fintype τ] [DecidableEq τ] (M : DTM σ) (N : DTM τ) (c : DConfig σ) :
    Dhalted (Dcompose M N) (liftFirst M N c) = false := by
  rcases c with ⟨q, inp, hd, out, wk, wh⟩
  simp [Dhalted, liftFirst, Dcompose]

lemma Dhalted_compose_liftSecond {σ τ : Type} [Fintype σ] [DecidableEq σ]
    [Fintype τ] [DecidableEq τ] (M : DTM σ) (N : DTM τ) (c : DConfig τ) :
    Dhalted (Dcompose M N) (liftSecond M N c) = Dhalted N c := by
  rcases c with ⟨q, inp, hd, out, wk, wh⟩
  simp [Dhalted, liftSecond, Dcompose]

lemma Dstep_compose_first_of_not_halted {σ τ : Type} [Fintype σ] [DecidableEq σ]
    [Fintype τ] [DecidableEq τ] (M : DTM σ) (N : DTM τ) (c : DConfig σ)
    (hnot : Dhalted M c = false) :
    Dstep (Dcompose M N) (liftFirst M N c) = liftFirst M N (Dstep M c) := by
  rcases c with ⟨q, inp, hd, out, wk, wh⟩
  dsimp [liftFirst, Dstep, Dread, Dhalted] at hnot ⊢
  have hqp : ¬ (q = M.accept ∨ q = M.reject) := by simpa using hnot
  simp [Dcompose, hqp]

lemma Dstep_compose_first_halted {σ τ : Type} [Fintype σ] [DecidableEq σ]
    [Fintype τ] [DecidableEq τ] (M : DTM σ) (N : DTM τ) (c : DConfig σ)
    (hhalt : Dhalted M c = true) :
    Dstep (Dcompose M N) (liftFirst M N c) = liftSecond M N (Dinit N c.output) := by
  rcases c with ⟨q, inp, hd, out, wk, wh⟩
  dsimp [liftFirst, liftSecond, Dinit, Dstep, Dread, Dhalted] at hhalt ⊢
  have hqp : q = M.accept ∨ q = M.reject := by simpa using hhalt
  simp [Dcompose, hqp]

lemma Dstep_compose_second_of_not_halted {σ τ : Type} [Fintype σ] [DecidableEq σ]
    [Fintype τ] [DecidableEq τ] (M : DTM σ) (N : DTM τ) (c : DConfig τ)
    (hnot : Dhalted N c = false) :
    Dstep (Dcompose M N) (liftSecond M N c) = liftSecond M N (Dstep N c) := by
  rcases c with ⟨q, inp, hd, out, wk, wh⟩
  dsimp [liftSecond, Dstep, Dread, Dhalted] at hnot ⊢
  have hqp : ¬ (q = N.accept ∨ q = N.reject) := by simpa using hnot
  simp [Dcompose, hqp]

lemma DnextConfig_compose_second {σ τ : Type} [Fintype σ] [DecidableEq σ]
    [Fintype τ] [DecidableEq τ] (M : DTM σ) (N : DTM τ) (c : DConfig τ) :
    DnextConfig (Dcompose M N) (liftSecond M N c) =
      liftSecond M N (DnextConfig N c) := by
  by_cases h : Dhalted N c = true
  · have hc : Dhalted (Dcompose M N) (liftSecond M N c) = true := by
      rw [Dhalted_compose_liftSecond]
      exact h
    simp [DnextConfig, h, hc]
  · have hf : Dhalted N c = false := by cases h' : Dhalted N c <;> simp_all
    have hc : Dhalted (Dcompose M N) (liftSecond M N c) = false := by
      rw [Dhalted_compose_liftSecond]
      exact hf
    simp [DnextConfig, hf, hc, Dstep_compose_second_of_not_halted M N c hf]

lemma DnextConfig_compose_first_of_not_halted {σ τ : Type} [Fintype σ] [DecidableEq σ]
    [Fintype τ] [DecidableEq τ] (M : DTM σ) (N : DTM τ) (c : DConfig σ)
    (hnot : Dhalted M c = false) :
    DnextConfig (Dcompose M N) (liftFirst M N c) = liftFirst M N (DnextConfig M c) := by
  have hcnot : Dhalted (Dcompose M N) (liftFirst M N c) = false :=
    Dhalted_compose_liftFirst M N c
  simp [DnextConfig, hnot, hcnot, Dstep_compose_first_of_not_halted M N c hnot]

lemma Drun_compose_second {σ τ : Type} [Fintype σ] [DecidableEq σ]
    [Fintype τ] [DecidableEq τ] (M : DTM σ) (N : DTM τ)
    (k : Nat) (c : DConfig τ) :
    Drun (Dcompose M N) k (liftSecond M N c) = liftSecond M N (Drun N k c) := by
  induction k generalizing c with
  | zero => simp [Drun, liftSecond]
  | succ k ih =>
      rw [Drun_succ_eq_run_nextConfig]
      rw [Drun_succ_eq_run_nextConfig]
      rw [DnextConfig_compose_second M N c]
      exact ih (DnextConfig N c)

lemma Drun_compose_first {σ τ : Type} [Fintype σ] [DecidableEq σ]
    [Fintype τ] [DecidableEq τ] (M : DTM σ) (N : DTM τ)
    (t : Nat) (c : DConfig σ)
    (hnone : ∀ s : Nat, s < t → Dhalted M (Drun M s c) = false) :
    Drun (Dcompose M N) t (liftFirst M N c) = liftFirst M N (Drun M t c) := by
  induction t generalizing c with
  | zero => simp [Drun, liftFirst]
  | succ t ih =>
      rw [Drun_succ_eq_run_nextConfig]
      rw [Drun_succ_eq_run_nextConfig]
      have hnot_c : Dhalted M c = false := by
        simpa [Drun] using hnone 0 (Nat.succ_pos t)
      rw [DnextConfig_compose_first_of_not_halted M N c hnot_c]
      apply ih (DnextConfig M c)
      intro s hs
      have hs' : s + 1 < t + 1 := Nat.succ_lt_succ hs
      have h := hnone (s + 1) hs'
      simpa [Drun_succ_eq_run_nextConfig] using h

/-- Sequential closure is now a theorem: the handoff instruction transfers a
    variable-length output word to a clean input for the second machine. -/
theorem DPolyTimeComputableClosedUnderComposition :
    ∀ f g : Word → Word, DPolyTimeComputable f → DPolyTimeComputable g →
      DPolyTimeComputable (fun x => g (f x)) := by
  intro f g hf hg
  rcases hf with ⟨σ, _instσ, _decσ, M, p, r, hMhalt, hMout⟩
  rcases hg with ⟨τ, _instτ, _decτ, N, q, s, hNhalt, hNout⟩
  let K := Dcompose M N
  let P : TimeBound := p + C 1 + q.comp r
  let R : TimeBound := s.comp r
  have hcomp_run : ∀ x : Word,
      Drun K (P.eval x.length) (Dinit K x) =
        liftSecond M N (Drun N (q.eval (f x).length) (Dinit N (f x))) := by
    intro x
    let pm := p.eval x.length
    let c0 := Dinit K x
    let cM0 := Dinit M x
    let hex : ∃ t : Nat, t ≤ pm ∧ Dhalted M (Drun M t cM0) = true :=
      ⟨pm, le_rfl, by simpa [pm] using hMhalt x⟩
    let t0 := Nat.find hex
    have ht0halt : Dhalted M (Drun M t0 cM0) = true := (Nat.find_spec hex).2
    have ht0le : t0 ≤ pm := Nat.find_min' hex (by simpa [pm] using hMhalt x)
    have hnone : ∀ s' : Nat, s' < t0 → Dhalted M (Drun M s' cM0) = false := by
      intro s' hs
      have hle : s' ≤ pm := by omega
      by_contra hh
      exact (Nat.find_min hex hs) ⟨hle, by simpa using hh⟩
    have hfirst : Drun K t0 (liftFirst M N cM0) = liftFirst M N (Drun M t0 cM0) := by
      simpa [K] using Drun_compose_first M N t0 cM0 hnone
    have hfreeze : Drun M pm cM0 = Drun M t0 cM0 :=
      Drun_eq_of_halted_within M cM0 ht0le ht0halt
    have hout_t0 : (Drun M t0 cM0).output = f x := by
      rw [← hfreeze]
      exact (hMout x).1
    have hswitch : Drun K (t0 + 1) c0 = liftSecond M N (Dinit N (f x)) := by
      dsimp [c0]
      change Drun K (t0 + 1) (liftFirst M N cM0) = _
      rw [Drun_add_eq]
      rw [hfirst]
      change Drun (Dcompose M N) 1 (liftFirst M N (Drun M t0 cM0)) = _
      rw [show Drun (Dcompose M N) 1 (liftFirst M N (Drun M t0 cM0)) =
          DnextConfig (Dcompose M N) (liftFirst M N (Drun M t0 cM0)) by
        simp [Drun, DnextConfig, Dhalted_compose_liftFirst]]
      rw [DnextConfig, Dhalted_compose_liftFirst]
      simp [Dstep_compose_first_halted M N (Drun M t0 cM0) ht0halt, hout_t0]
    let pn := q.eval (f x).length
    have hNhaltx : Dhalted N (Drun N pn (Dinit N (f x))) = true := by
      simpa [pn] using hNhalt (f x)
    have htotal_time : Drun K ((t0 + 1) + pn) c0 =
        liftSecond M N (Drun N pn (Dinit N (f x))) := by
      rw [Drun_add_eq]
      rw [hswitch]
      simpa [K] using Drun_compose_second M N pn (Dinit N (f x))
    have hhalt_total : Dhalted K (Drun K ((t0 + 1) + pn) c0) = true := by
      rw [htotal_time]
      rw [Dhalted_compose_liftSecond]
      simpa [K] using hNhaltx
    have hpn : pn = (q.comp r).eval x.length := by
      have hlen := (hMout x).2
      simp [pn, hlen, Polynomial.eval_comp]
    have hP : P.eval x.length = pm + 1 + (q.comp r).eval x.length := by
      simp [P, pm]
    have hle_total : (t0 + 1) + pn ≤ P.eval x.length := by omega
    exact (Drun_eq_of_halted_within K c0 hle_total hhalt_total).trans htotal_time
  refine ⟨DCompState σ τ, inferInstance, inferInstance, K, P, R, ?_, ?_⟩
  · intro x
    rw [hcomp_run x]
    rw [Dhalted_compose_liftSecond]
    simpa [K] using hNhalt (f x)
  · intro x
    constructor
    · change (Drun K (P.eval x.length) (Dinit K x)).output = g (f x)
      rw [hcomp_run x]
      simpa [liftSecond] using (hNout (f x)).1
    · have hlenf : (f x).length = r.eval x.length := (hMout x).2
      rw [(hNout (f x)).2, hlenf]
      simp [R, Polynomial.eval_comp]

-- -----------------------------------------------------------------------------
-- 2c. A first concrete transducer subroutine
-- -----------------------------------------------------------------------------

/-- States of the identity transducer, identified with `Fin 4`. -/
abbrev DIdState := Fin 4

namespace DIdState

def start : DIdState := ⟨0, by decide⟩
def scan : DIdState := ⟨1, by decide⟩
def done : DIdState := ⟨2, by decide⟩
def reject : DIdState := ⟨3, by decide⟩

end DIdState

/-- A transducer that copies its read-only input to its output.  It uses one
    startup step to leave the input boundary, then emits one bit per input cell. -/
def DIdTM : DTM DIdState where
  step := fun q sym _ =>
    if q = DIdState.start then
      { next := DIdState.scan, output := none, inputMove := some true
        workWrite := none, workMove := none }
    else if q = DIdState.scan then
      match sym with
      | some b =>
          { next := DIdState.scan, output := some b, inputMove := some true
            workWrite := none, workMove := none }
      | none =>
          { next := DIdState.done, output := none, inputMove := none
            workWrite := none, workMove := none }
    else
      { next := q, output := none, inputMove := none
        workWrite := none, workMove := none }
  start := DIdState.start
  accept := DIdState.done
  reject := DIdState.reject

lemma Drun_DIdTM_start (x : Word) :
    Drun DIdTM 1 (Dinit DIdTM x) =
      { state := DIdState.scan, input := x, head := 1, output := [],
        work := fun _ : Nat => false, workHead := 0 } := by
  simp [Drun, Dhalted, Dinit, Dstep, Dread, DIdTM, Dmove,
    DIdState.start, DIdState.scan, DIdState.done, DIdState.reject]

/-- Once the scan state is reached with `prefix` already emitted, the machine
    emits the remaining suffix and halts.  The work tape is left untouched. -/
lemma Drun_DIdTM_scan_suffix (pre suffix : Word) (wk : Nat → Bool) (wh : Nat) :
    Drun DIdTM (suffix.length + 1)
      { state := DIdState.scan, input := pre ++ suffix, head := pre.length + 1,
        output := pre, work := wk, workHead := wh } =
      { state := DIdState.done, input := pre ++ suffix,
        head := (pre ++ suffix).length + 1, output := pre ++ suffix,
        work := wk, workHead := wh } := by
  induction suffix generalizing pre with
  | nil =>
      let c : DConfig DIdState :=
        { state := DIdState.scan, input := pre ++ [], head := pre.length + 1,
          output := pre, work := wk, workHead := wh }
      change Drun DIdTM 1 c = _
      simp [c, Drun, Dhalted, Dstep, Dread, DIdTM,
        DIdState.scan, DIdState.done, DIdState.start, DIdState.reject]
  | cons b bs ih =>
      rw [show (b :: bs).length + 1 = 1 + (bs.length + 1) by
        simp [Nat.add_comm, Nat.add_left_comm]]
      rw [Drun_add_eq]
      let c : DConfig DIdState :=
        { state := DIdState.scan, input := pre ++ b :: bs, head := pre.length + 1,
          output := pre, work := wk, workHead := wh }
      let c' : DConfig DIdState :=
        { state := DIdState.scan, input := pre ++ b :: bs, head := pre.length + 2,
          output := pre ++ [b], work := wk, workHead := wh }
      have hstep : Drun DIdTM 1 c = c' := by
        simp [c, c', Drun, Dhalted, Dstep, Dread, DIdTM, Dmove,
          DIdState.scan, DIdState.done, DIdState.start, DIdState.reject]
      change Drun DIdTM (bs.length + 1) (Drun DIdTM 1 c) = _
      rw [hstep]
      simpa [c', List.append_assoc, Nat.add_comm, Nat.add_left_comm] using ih (pre := pre ++ [b])

lemma dPolyTimeComputable_id : DPolyTimeComputable id := by
  refine ⟨DIdState, inferInstance, inferInstance, DIdTM, X + C 2, X, ?_, ?_⟩
  · intro x
    have hstart := Drun_DIdTM_start x
    have hfinal : Drun DIdTM (x.length + 1)
        { state := DIdState.scan, input := x, head := 1, output := [],
          work := fun _ : Nat => false, workHead := 0 } =
        { state := DIdState.done, input := x, head := x.length + 1,
          output := x, work := fun _ : Nat => false, workHead := 0 } := by
      simpa using (Drun_DIdTM_scan_suffix [] x (fun _ : Nat => false) 0)
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    change Dhalted DIdTM (Drun DIdTM (x.length + 2) (Dinit DIdTM x)) = true
    rw [show x.length + 2 = 1 + (x.length + 1) by omega, Drun_add_eq, hstart, hfinal]
    simp [Dhalted, DIdTM]
  · intro x
    have hstart := Drun_DIdTM_start x
    have hfinal : Drun DIdTM (x.length + 1)
        { state := DIdState.scan, input := x, head := 1, output := [],
          work := fun _ : Nat => false, workHead := 0 } =
        { state := DIdState.done, input := x, head := x.length + 1,
          output := x, work := fun _ : Nat => false, workHead := 0 } := by
      simpa using (Drun_DIdTM_scan_suffix [] x (fun _ : Nat => false) 0)
    constructor
    · change Dboutput DIdTM ((X + C 2 : TimeBound).eval x.length) x = id x
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      dsimp [Dboutput]
      rw [show x.length + 2 = 1 + (x.length + 1) by omega, Drun_add_eq, hstart, hfinal]
    · simp

-- -----------------------------------------------------------------------------
-- 2d. Appending a fixed suffix
-- -----------------------------------------------------------------------------

/-- States of the append transducer.  States `0` and `1` copy the input; states
    `2 ... y.length + 1` emit the bits of the fixed suffix `y`; the last state
    is halting. -/
abbrev DAppendState (y : Word) := Fin (y.length + 3)

namespace DAppendState

def start (y : Word) : DAppendState y := ⟨0, by omega⟩
def scan (y : Word) : DAppendState y := ⟨1, by omega⟩
def emitStart (y : Word) : DAppendState y := ⟨2, by omega⟩
def done (y : Word) : DAppendState y := ⟨y.length + 2, by omega⟩

end DAppendState

/-- Copy the input, then append the fixed word `y`. -/
def DAppendTM (y : Word) : DTM (DAppendState y) where
  step := fun q sym _ =>
    if q = DAppendState.start y then
      { next := DAppendState.scan y, output := none, inputMove := some true
        workWrite := none, workMove := none }
    else if q = DAppendState.scan y then
      match sym with
      | some b =>
          { next := DAppendState.scan y, output := some b, inputMove := some true
            workWrite := none, workMove := none }
      | none =>
          { next := DAppendState.emitStart y, output := none, inputMove := none
            workWrite := none, workMove := none }
    else if hq : q.val < y.length + 2 then
      { next := ⟨q.val + 1, by
          exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt ‹q.val < y.length + 2›)
            (Nat.lt_succ_self (y.length + 2))⟩,
        output := some (y.getD (q.val - 2) false),
        inputMove := none, workWrite := none, workMove := none }
    else
      { next := q, output := none, inputMove := none
        workWrite := none, workMove := none }
  start := DAppendState.start y
  accept := DAppendState.done y
  reject := DAppendState.done y

lemma Drun_DAppendTM_start (y x : Word) :
    Drun (DAppendTM y) 1 (Dinit (DAppendTM y) x) =
      { state := DAppendState.scan y, input := x, head := 1, output := [],
        work := fun _ : Nat => false, workHead := 0 } := by
  simp [Drun, Dhalted, Dinit, Dstep, Dread, DAppendTM, Dmove,
    DAppendState.start, DAppendState.scan, DAppendState.emitStart,
    DAppendState.done]

/-- The scan phase emits `pre ++ suffix` and enters the fixed-suffix phase. -/
lemma Drun_DAppendTM_scan_suffix (y pre suffix : Word) (wk : Nat → Bool) (wh : Nat) :
    Drun (DAppendTM y) (suffix.length + 1)
      { state := DAppendState.scan y, input := pre ++ suffix, head := pre.length + 1,
        output := pre, work := wk, workHead := wh } =
      { state := DAppendState.emitStart y, input := pre ++ suffix,
        head := (pre ++ suffix).length + 1, output := pre ++ suffix,
        work := wk, workHead := wh } := by
  induction suffix generalizing pre with
  | nil =>
      let c : DConfig (DAppendState y) :=
        { state := DAppendState.scan y, input := pre ++ [], head := pre.length + 1,
          output := pre, work := wk, workHead := wh }
      change Drun (DAppendTM y) 1 c = _
      simp [c, Drun, Dhalted, Dstep, Dread, DAppendTM,
        DAppendState.start, DAppendState.scan, DAppendState.emitStart,
        DAppendState.done]
  | cons b bs ih =>
      rw [show (b :: bs).length + 1 = 1 + (bs.length + 1) by
        simp [Nat.add_comm, Nat.add_left_comm]]
      rw [Drun_add_eq]
      let c : DConfig (DAppendState y) :=
        { state := DAppendState.scan y, input := pre ++ b :: bs, head := pre.length + 1,
          output := pre, work := wk, workHead := wh }
      let c' : DConfig (DAppendState y) :=
        { state := DAppendState.scan y, input := pre ++ b :: bs, head := pre.length + 2,
          output := pre ++ [b], work := wk, workHead := wh }
      have hstep : Drun (DAppendTM y) 1 c = c' := by
        simp [c, c', Drun, Dhalted, Dstep, Dread, DAppendTM, Dmove,
          DAppendState.start, DAppendState.scan, DAppendState.emitStart,
          DAppendState.done]
      change Drun (DAppendTM y) (bs.length + 1) (Drun (DAppendTM y) 1 c) = _
      rw [hstep]
      simpa [c', List.append_assoc, Nat.add_comm, Nat.add_left_comm] using ih (pre := pre ++ [b])

/-- The fixed-suffix phase emits `suffix` without touching the input or work tape. -/
lemma Drun_DAppendTM_emit_suffix (y : Word) :
    ∀ (preY suffix : Word) (hy : y = preY ++ suffix),
    ∀ (inp out : Word) (h : Nat) (wk : Nat → Bool) (wh : Nat),
      Drun (DAppendTM y) suffix.length
        { state := ⟨preY.length + 2, by
            have hlen : y.length = preY.length + suffix.length := by
              rw [hy]
              simp
            omega⟩, input := inp, head := h,
          output := out, work := wk, workHead := wh } =
        { state := ⟨(preY ++ suffix).length + 2, by
            have hlen : y.length = preY.length + suffix.length := by
              rw [hy]
              simp
            have happ : (preY ++ suffix).length = preY.length + suffix.length := by simp
            omega⟩, input := inp, head := h,
          output := out ++ suffix, work := wk, workHead := wh } := by
  intro preY suffix hy
  induction suffix generalizing preY with
  | nil =>
      intro inp out h wk wh
      subst y
      simp [Drun]
  | cons b bs ih =>
      intro inp out h wk wh
      change Drun (DAppendTM y) (bs.length + 1)
        { state := ⟨preY.length + 2, by
            have hlen : y.length = preY.length + (b :: bs).length := by
              rw [hy]
              simp
            omega⟩, input := inp, head := h,
          output := out, work := wk, workHead := wh } = _
      rw [Drun_succ_eq_run_nextConfig]
      have hy' : y = (preY ++ [b]) ++ bs := by simpa [List.append_assoc] using hy
      have hlt : preY.length + 2 < y.length + 2 := by
        rw [hy]
        simp
      have hne : preY.length ≠ y.length := by omega
      have hlt' : (preY ++ [b]).length + 2 < y.length + 3 := by
        rw [hy']
        simp
      have hget : y[preY.length]?.getD false = b := by
        rw [hy]
        simp
      have hnext : DnextConfig (DAppendTM y)
          { state := ⟨preY.length + 2, by
              have hlen : y.length = preY.length + (b :: bs).length := by
                rw [hy]
                simp
              omega⟩, input := inp, head := h,
            output := out, work := wk, workHead := wh } =
          { state := ⟨(preY ++ [b]).length + 2, hlt'⟩, input := inp, head := h,
            output := out ++ [b], work := wk, workHead := wh } := by
        simp [DnextConfig, Dhalted, Dstep, DAppendTM, hlt, hne, hget,
          DAppendState.start, DAppendState.scan, DAppendState.done]
      rw [hnext]
      simpa [List.append_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (preY := preY ++ [b]) hy' inp (out ++ [b]) h wk wh

theorem dPolyTimeComputable_append (y : Word) : DPolyTimeComputable (fun x => x ++ y) := by
  refine ⟨DAppendState y, inferInstance, inferInstance, DAppendTM y,
    X + C (y.length + 2), X + C y.length, ?_, ?_⟩
  · intro x
    have hstart := Drun_DAppendTM_start y x
    have hscan : Drun (DAppendTM y) (x.length + 1)
        { state := DAppendState.scan y, input := x, head := 1, output := [],
          work := fun _ : Nat => false, workHead := 0 } =
        { state := DAppendState.emitStart y, input := x, head := x.length + 1,
          output := x, work := fun _ : Nat => false, workHead := 0 } := by
      simpa using (Drun_DAppendTM_scan_suffix y [] x (fun _ : Nat => false) 0)
    have hemit : Drun (DAppendTM y) y.length
        { state := DAppendState.emitStart y, input := x, head := x.length + 1,
          output := x, work := fun _ : Nat => false, workHead := 0 } =
        { state := DAppendState.done y, input := x, head := x.length + 1,
          output := x ++ y, work := fun _ : Nat => false, workHead := 0 } := by
      simpa [DAppendState.emitStart, DAppendState.done] using
        (Drun_DAppendTM_emit_suffix y [] y rfl x x (x.length + 1)
          (fun _ : Nat => false) 0)
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    change Dhalted (DAppendTM y)
      (Drun (DAppendTM y) (x.length + (y.length + 2))
        (Dinit (DAppendTM y) x)) = true
    rw [show x.length + (y.length + 2) = 1 + ((x.length + 1) + y.length) by omega]
    rw [Drun_add_eq, hstart]
    rw [Drun_add_eq, hscan, hemit]
    simp [Dhalted, DAppendTM, DAppendState.done]
  · intro x
    have hstart := Drun_DAppendTM_start y x
    have hscan : Drun (DAppendTM y) (x.length + 1)
        { state := DAppendState.scan y, input := x, head := 1, output := [],
          work := fun _ : Nat => false, workHead := 0 } =
        { state := DAppendState.emitStart y, input := x, head := x.length + 1,
          output := x, work := fun _ : Nat => false, workHead := 0 } := by
      simpa using (Drun_DAppendTM_scan_suffix y [] x (fun _ : Nat => false) 0)
    have hemit : Drun (DAppendTM y) y.length
        { state := DAppendState.emitStart y, input := x, head := x.length + 1,
          output := x, work := fun _ : Nat => false, workHead := 0 } =
        { state := DAppendState.done y, input := x, head := x.length + 1,
          output := x ++ y, work := fun _ : Nat => false, workHead := 0 } := by
      simpa [DAppendState.emitStart, DAppendState.done] using
        (Drun_DAppendTM_emit_suffix y [] y rfl x x (x.length + 1)
          (fun _ : Nat => false) 0)
    constructor
    · change Dboutput (DAppendTM y) ((X + C (y.length + 2) : TimeBound).eval x.length) x = x ++ y
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      dsimp [Dboutput]
      rw [show x.length + (y.length + 2) = 1 + ((x.length + 1) + y.length) by omega]
      rw [Drun_add_eq, hstart]
      rw [Drun_add_eq, hscan, hemit]
    · simp

-- -----------------------------------------------------------------------------
-- 2e. Prefixing a fixed word
-- -----------------------------------------------------------------------------

/-- States of the prefix transducer.  States below `y.length` emit the fixed
    prefix, then one startup step enters the input-copy loop. -/
abbrev DPrependState (y : Word) := Fin (y.length + 3)

namespace DPrependState

def emitStart (y : Word) : DPrependState y := ⟨0, by omega⟩
def copyStart (y : Word) : DPrependState y := ⟨y.length, by omega⟩
def copy (y : Word) : DPrependState y := ⟨y.length + 1, by omega⟩
def done (y : Word) : DPrependState y := ⟨y.length + 2, by omega⟩

end DPrependState

/-- Emit the fixed word `y`, then copy the input after it. -/
def DPrependTM (y : Word) : DTM (DPrependState y) where
  step := fun q sym _ =>
    if hq : q.val < y.length then
      { next := ⟨q.val + 1, by
          exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hq)
            (by omega : y.length < y.length + 3)⟩,
        output := some (y[q.val]?.getD false), inputMove := none,
        workWrite := none, workMove := none }
    else if q = DPrependState.copyStart y then
      { next := DPrependState.copy y, output := none, inputMove := some true
        workWrite := none, workMove := none }
    else if q = DPrependState.copy y then
      match sym with
      | some b =>
          { next := DPrependState.copy y, output := some b, inputMove := some true
            workWrite := none, workMove := none }
      | none =>
          { next := DPrependState.done y, output := none, inputMove := none
            workWrite := none, workMove := none }
    else
      { next := q, output := none, inputMove := none
        workWrite := none, workMove := none }
  start := DPrependState.emitStart y
  accept := DPrependState.done y
  reject := DPrependState.done y

/-- The fixed-prefix phase emits `suffix` and enters the copy-start state. -/
lemma Drun_DPrependTM_emit_prefix (y : Word) :
    ∀ (pre suffix : Word) (hy : y = pre ++ suffix),
    ∀ (inp out : Word) (h : Nat) (wk : Nat → Bool) (wh : Nat),
      Drun (DPrependTM y) suffix.length
        { state := ⟨pre.length, by
            have hlen : y.length = pre.length + suffix.length := by
              rw [hy]
              simp
            omega⟩, input := inp, head := h,
          output := out, work := wk, workHead := wh } =
        { state := ⟨(pre ++ suffix).length, by
            have hlen : y.length = pre.length + suffix.length := by
              rw [hy]
              simp
            have happ : (pre ++ suffix).length = pre.length + suffix.length := by simp
            omega⟩, input := inp, head := h,
          output := out ++ suffix, work := wk, workHead := wh } := by
  intro pre suffix hy
  induction suffix generalizing pre with
  | nil =>
      intro inp out h wk wh
      subst y
      simp [Drun]
  | cons b bs ih =>
      intro inp out h wk wh
      change Drun (DPrependTM y) (bs.length + 1)
        { state := ⟨pre.length, by
            have hlen : y.length = pre.length + (b :: bs).length := by
              rw [hy]
              simp
            omega⟩, input := inp, head := h,
          output := out, work := wk, workHead := wh } = _
      rw [Drun_succ_eq_run_nextConfig]
      have hy' : y = (pre ++ [b]) ++ bs := by simpa [List.append_assoc] using hy
      have hlt : pre.length < y.length := by
        rw [hy]
        simp
      have hlt' : (pre ++ [b]).length < y.length + 3 := by
        rw [hy']
        simp
        omega
      have hne : pre.length ≠ y.length + 2 := by omega
      have hgetD : y[pre.length]?.getD false = b := by
        rw [hy]
        simp
      have hget : y[pre.length] = b := by
        rw [← List.getD_eq_getElem y false hlt]
        exact hgetD
      have hnext : DnextConfig (DPrependTM y)
          { state := ⟨pre.length, by
              have hlen : y.length = pre.length + (b :: bs).length := by
                rw [hy]
                simp
              omega⟩, input := inp, head := h,
            output := out, work := wk, workHead := wh } =
          { state := ⟨(pre ++ [b]).length, hlt'⟩, input := inp, head := h,
            output := out ++ [b], work := wk, workHead := wh } := by
        simp [DnextConfig, Dhalted, Dstep, DPrependTM, hlt, hne, hget,
          DPrependState.emitStart, DPrependState.copyStart,
          DPrependState.copy, DPrependState.done]
      rw [hnext]
      simpa [List.append_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (pre := pre ++ [b]) hy' inp (out ++ [b]) h wk wh

lemma Drun_DPrependTM_copy_start (y x : Word) (wk : Nat → Bool) (wh : Nat) :
    Drun (DPrependTM y) 1
      { state := DPrependState.copyStart y, input := x, head := 0, output := y,
        work := wk, workHead := wh } =
      { state := DPrependState.copy y, input := x, head := 1, output := y,
        work := wk, workHead := wh } := by
  simp [Drun, Dhalted, Dstep, Dread, DPrependTM, Dmove,
    DPrependState.emitStart, DPrependState.copyStart,
    DPrependState.copy, DPrependState.done]

/-- The copy phase emits `pre ++ suffix` after the prefix. -/
lemma Drun_DPrependTM_copy_suffix (y pre suffix : Word)
    (out : Word) (wk : Nat → Bool) (wh : Nat) :
    Drun (DPrependTM y) (suffix.length + 1)
      { state := DPrependState.copy y, input := pre ++ suffix,
        head := pre.length + 1, output := out, work := wk, workHead := wh } =
      { state := DPrependState.done y, input := pre ++ suffix,
        head := (pre ++ suffix).length + 1, output := out ++ suffix,
        work := wk, workHead := wh } := by
  induction suffix generalizing pre out with
  | nil =>
      let c : DConfig (DPrependState y) :=
        { state := DPrependState.copy y, input := pre ++ [], head := pre.length + 1,
          output := out, work := wk, workHead := wh }
      change Drun (DPrependTM y) 1 c = _
      simp [c, Drun, Dhalted, Dstep, Dread, DPrependTM,
        DPrependState.emitStart, DPrependState.copyStart,
        DPrependState.copy, DPrependState.done]
  | cons b bs ih =>
      rw [show (b :: bs).length + 1 = 1 + (bs.length + 1) by
        simp [Nat.add_comm, Nat.add_left_comm]]
      rw [Drun_add_eq]
      let c : DConfig (DPrependState y) :=
        { state := DPrependState.copy y, input := pre ++ b :: bs,
          head := pre.length + 1, output := out, work := wk, workHead := wh }
      let c' : DConfig (DPrependState y) :=
        { state := DPrependState.copy y, input := pre ++ b :: bs,
          head := pre.length + 2, output := out ++ [b], work := wk, workHead := wh }
      have hstep : Drun (DPrependTM y) 1 c = c' := by
        simp [c, c', Drun, Dhalted, Dstep, Dread, DPrependTM, Dmove,
          DPrependState.emitStart, DPrependState.copyStart,
          DPrependState.copy, DPrependState.done]
      change Drun (DPrependTM y) (bs.length + 1) (Drun (DPrependTM y) 1 c) = _
      rw [hstep]
      simpa [c', List.append_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (pre := pre ++ [b]) (out := out ++ [b])

theorem dPolyTimeComputable_prepend (y : Word) :
    DPolyTimeComputable (fun x => y ++ x) := by
  refine ⟨DPrependState y, inferInstance, inferInstance, DPrependTM y,
    X + C (y.length + 2), X + C y.length, ?_, ?_⟩
  · intro x
    have hprefix : Drun (DPrependTM y) y.length
        { state := DPrependState.emitStart y, input := x, head := 0, output := [],
          work := fun _ : Nat => false, workHead := 0 } =
        { state := DPrependState.copyStart y, input := x, head := 0, output := y,
          work := fun _ : Nat => false, workHead := 0 } := by
      simpa [DPrependState.emitStart, DPrependState.copyStart] using
        (Drun_DPrependTM_emit_prefix y [] y rfl x [] 0 (fun _ : Nat => false) 0)
    have hcopyStart := Drun_DPrependTM_copy_start y x (fun _ : Nat => false) 0
    have hcopy : Drun (DPrependTM y) (x.length + 1)
        { state := DPrependState.copy y, input := x, head := 1, output := y,
          work := fun _ : Nat => false, workHead := 0 } =
        { state := DPrependState.done y, input := x, head := x.length + 1,
          output := y ++ x, work := fun _ : Nat => false, workHead := 0 } := by
      simpa using (Drun_DPrependTM_copy_suffix y [] x y (fun _ : Nat => false) 0)
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    change Dhalted (DPrependTM y)
      (Drun (DPrependTM y) (x.length + (y.length + 2))
        (Dinit (DPrependTM y) x)) = true
    dsimp [Dinit]
    change Dhalted (DPrependTM y)
      (Drun (DPrependTM y) (x.length + (y.length + 2))
        { state := DPrependState.emitStart y, input := x, head := 0, output := [],
          work := fun _ : Nat => false, workHead := 0 }) = true
    rw [show x.length + (y.length + 2) = y.length + (1 + (x.length + 1)) by omega]
    rw [Drun_add_eq, hprefix]
    rw [Drun_add_eq, hcopyStart]
    rw [hcopy]
    simp [Dhalted, DPrependTM, DPrependState.done]
  · intro x
    have hprefix : Drun (DPrependTM y) y.length
        { state := DPrependState.emitStart y, input := x, head := 0, output := [],
          work := fun _ : Nat => false, workHead := 0 } =
        { state := DPrependState.copyStart y, input := x, head := 0, output := y,
          work := fun _ : Nat => false, workHead := 0 } := by
      simpa [DPrependState.emitStart, DPrependState.copyStart] using
        (Drun_DPrependTM_emit_prefix y [] y rfl x [] 0 (fun _ : Nat => false) 0)
    have hcopyStart := Drun_DPrependTM_copy_start y x (fun _ : Nat => false) 0
    have hcopy : Drun (DPrependTM y) (x.length + 1)
        { state := DPrependState.copy y, input := x, head := 1, output := y,
          work := fun _ : Nat => false, workHead := 0 } =
        { state := DPrependState.done y, input := x, head := x.length + 1,
          output := y ++ x, work := fun _ : Nat => false, workHead := 0 } := by
      simpa using (Drun_DPrependTM_copy_suffix y [] x y (fun _ : Nat => false) 0)
    constructor
    · change Dboutput (DPrependTM y) ((X + C (y.length + 2) : TimeBound).eval x.length) x =
        y ++ x
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      dsimp [Dboutput, Dinit]
      change (Drun (DPrependTM y) (x.length + (y.length + 2))
        { state := DPrependState.emitStart y, input := x, head := 0, output := [],
          work := fun _ : Nat => false, workHead := 0 }).output = y ++ x
      rw [show x.length + (y.length + 2) = y.length + (1 + (x.length + 1)) by omega]
      rw [Drun_add_eq, hprefix]
      rw [Drun_add_eq, hcopyStart]
      rw [hcopy]
    · simp [Nat.add_comm]

-- -----------------------------------------------------------------------------
-- 2f. Emitting a fixed word
-- -----------------------------------------------------------------------------

/-- States of the constant transducer.  State `i < y.length` emits `y[i]`; the
    last state is halting. -/
abbrev DConstState (y : Word) := Fin (y.length + 1)

namespace DConstState

def start (y : Word) : DConstState y := ⟨0, by omega⟩
def done (y : Word) : DConstState y := ⟨y.length, by omega⟩

end DConstState

/-- Ignore the input and emit the fixed word `y`. -/
def DConstTM (y : Word) : DTM (DConstState y) where
  step := fun q _ _ =>
    if hq : q.val < y.length then
      { next := ⟨q.val + 1, by
          exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hq)
            (Nat.lt_succ_self y.length)⟩,
        output := some (y[q.val]?.getD false), inputMove := none,
        workWrite := none, workMove := none }
    else
      { next := q, output := none, inputMove := none
        workWrite := none, workMove := none }
  start := DConstState.start y
  accept := DConstState.done y
  reject := DConstState.done y

/-- The fixed-word phase emits `suffix` without touching the input or work tape. -/
lemma Drun_DConstTM_emit_prefix (y : Word) :
    ∀ (pre suffix : Word) (hy : y = pre ++ suffix),
    ∀ (inp out : Word) (h : Nat) (wk : Nat → Bool) (wh : Nat),
      Drun (DConstTM y) suffix.length
        { state := ⟨pre.length + 0, by
            have hlen : y.length = pre.length + suffix.length := by
              rw [hy]
              simp
            omega⟩, input := inp, head := h,
          output := out, work := wk, workHead := wh } =
        { state := ⟨(pre ++ suffix).length + 0, by
            have hlen : y.length = pre.length + suffix.length := by
              rw [hy]
              simp
            have happ : (pre ++ suffix).length = pre.length + suffix.length := by simp
            omega⟩, input := inp, head := h,
          output := out ++ suffix, work := wk, workHead := wh } := by
  intro pre suffix hy
  induction suffix generalizing pre with
  | nil =>
      intro inp out h wk wh
      subst y
      simp [Drun]
  | cons b bs ih =>
      intro inp out h wk wh
      change Drun (DConstTM y) (bs.length + 1)
        { state := ⟨pre.length + 0, by
            have hlen : y.length = pre.length + (b :: bs).length := by
              rw [hy]
              simp
            omega⟩, input := inp, head := h,
          output := out, work := wk, workHead := wh } = _
      rw [Drun_succ_eq_run_nextConfig]
      have hy' : y = (pre ++ [b]) ++ bs := by simpa [List.append_assoc] using hy
      have hlt : pre.length < y.length := by
        rw [hy]
        simp
      have hne : pre.length ≠ y.length := by omega
      have hlt' : (pre ++ [b]).length < y.length + 1 := by
        rw [hy']
        simp
      have hgetD : y[pre.length]?.getD false = b := by
        rw [hy]
        simp
      have hget : y[pre.length] = b := by
        rw [← List.getD_eq_getElem y false hlt]
        exact hgetD
      have hnext : DnextConfig (DConstTM y)
          { state := ⟨pre.length + 0, by
              have hlen : y.length = pre.length + (b :: bs).length := by
                rw [hy]
                simp
              omega⟩, input := inp, head := h,
            output := out, work := wk, workHead := wh } =
          { state := ⟨(pre ++ [b]).length + 0, hlt'⟩, input := inp, head := h,
            output := out ++ [b], work := wk, workHead := wh } := by
        simp [DnextConfig, Dhalted, Dstep, DConstTM, hlt, hne, hget,
          DConstState.start, DConstState.done]
      rw [hnext]
      simpa [List.append_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (pre := pre ++ [b]) hy' inp (out ++ [b]) h wk wh

theorem dPolyTimeComputable_const (y : Word) : DPolyTimeComputable (fun _ => y) := by
  refine ⟨DConstState y, inferInstance, inferInstance, DConstTM y,
    C y.length, C y.length, ?_, ?_⟩
  · intro x
    have hem : Drun (DConstTM y) y.length
        { state := DConstState.start y, input := x, head := 0, output := [],
          work := fun _ : Nat => false, workHead := 0 } =
        { state := DConstState.done y, input := x, head := 0, output := y,
          work := fun _ : Nat => false, workHead := 0 } := by
      simpa [DConstState.start, DConstState.done] using
        (Drun_DConstTM_emit_prefix y [] y rfl x [] 0 (fun _ : Nat => false) 0)
    simp only [Polynomial.eval_C]
    change Dhalted (DConstTM y)
      (Drun (DConstTM y) y.length (Dinit (DConstTM y) x)) = true
    dsimp [Dinit]
    change Dhalted (DConstTM y)
      (Drun (DConstTM y) y.length
        { state := DConstState.start y, input := x, head := 0, output := [],
          work := fun _ : Nat => false, workHead := 0 }) = true
    rw [hem]
    simp [Dhalted, DConstTM, DConstState.done]
  · intro x
    have hem : Drun (DConstTM y) y.length
        { state := DConstState.start y, input := x, head := 0, output := [],
          work := fun _ : Nat => false, workHead := 0 } =
        { state := DConstState.done y, input := x, head := 0, output := y,
          work := fun _ : Nat => false, workHead := 0 } := by
      simpa [DConstState.start, DConstState.done] using
        (Drun_DConstTM_emit_prefix y [] y rfl x [] 0 (fun _ : Nat => false) 0)
    constructor
    · change Dboutput (DConstTM y) ((C y.length : TimeBound).eval x.length) x = y
      simp only [Polynomial.eval_C]
      dsimp [Dboutput, Dinit]
      change (Drun (DConstTM y) y.length
        { state := DConstState.start y, input := x, head := 0, output := [],
          work := fun _ : Nat => false, workHead := 0 }).output = y
      rw [hem]
    · simp

-- -----------------------------------------------------------------------------
-- 2g. A length-dependent unary encoding
-- -----------------------------------------------------------------------------

/-- States of the unary-length transducer. -/
abbrev DUnaryLengthState := Fin 6

namespace DUnaryLengthState

def start : DUnaryLengthState := ⟨0, by decide⟩
def copy : DUnaryLengthState := ⟨1, by decide⟩
def handoff : DUnaryLengthState := ⟨2, by decide⟩
def countStart : DUnaryLengthState := ⟨3, by decide⟩
def count : DUnaryLengthState := ⟨4, by decide⟩
def done : DUnaryLengthState := ⟨5, by decide⟩

end DUnaryLengthState

/-- Compute `encodeNat x.length = replicate x.length true ++ [false]`.  The
    first pass copies the input to the output; the handoff turns that output
    into the new input; the second pass emits one `true` per input bit. -/
def DUnaryLengthTM : DTM DUnaryLengthState where
  step := fun q sym _ =>
    if q = DUnaryLengthState.start then
      { next := DUnaryLengthState.copy, output := none, inputMove := some true
        workWrite := none, workMove := none }
    else if q = DUnaryLengthState.copy then
      match sym with
      | some b =>
          { next := DUnaryLengthState.copy, output := some b, inputMove := some true
            workWrite := none, workMove := none }
      | none =>
          { next := DUnaryLengthState.handoff, output := none, inputMove := none
            workWrite := none, workMove := none }
    else if q = DUnaryLengthState.handoff then
      { next := DUnaryLengthState.countStart, output := none, inputMove := none
        workWrite := none, workMove := none }
    else if q = DUnaryLengthState.countStart then
      { next := DUnaryLengthState.count, output := none, inputMove := some true
        workWrite := none, workMove := none }
    else if q = DUnaryLengthState.count then
      match sym with
      | some _ =>
          { next := DUnaryLengthState.count, output := some true, inputMove := some true
            workWrite := none, workMove := none }
      | none =>
          { next := DUnaryLengthState.done, output := some false, inputMove := none
            workWrite := none, workMove := none }
    else
      { next := q, output := none, inputMove := none
        workWrite := none, workMove := none }
  handoff := fun q => q = DUnaryLengthState.handoff
  start := DUnaryLengthState.start
  accept := DUnaryLengthState.done
  reject := DUnaryLengthState.done

lemma Drun_DUnaryLengthTM_start (x : Word) :
    Drun DUnaryLengthTM 1 (Dinit DUnaryLengthTM x) =
      { state := DUnaryLengthState.copy, input := x, head := 1, output := [],
        work := fun _ : Nat => false, workHead := 0 } := by
  simp [Drun, Dhalted, Dinit, Dstep, Dread, DUnaryLengthTM, Dmove,
    DUnaryLengthState.start, DUnaryLengthState.copy, DUnaryLengthState.handoff,
    DUnaryLengthState.count, DUnaryLengthState.done]

/-- The copy phase emits `pre ++ suffix` and enters the handoff state. -/
lemma Drun_DUnaryLengthTM_copy_suffix (pre suffix : Word)
    (wk : Nat → Bool) (wh : Nat) :
    Drun DUnaryLengthTM (suffix.length + 1)
      { state := DUnaryLengthState.copy, input := pre ++ suffix,
        head := pre.length + 1, output := pre, work := wk, workHead := wh } =
      { state := DUnaryLengthState.handoff, input := pre ++ suffix,
        head := (pre ++ suffix).length + 1, output := pre ++ suffix,
        work := wk, workHead := wh } := by
  induction suffix generalizing pre with
  | nil =>
      let c : DConfig DUnaryLengthState :=
        { state := DUnaryLengthState.copy, input := pre ++ [], head := pre.length + 1,
          output := pre, work := wk, workHead := wh }
      change Drun DUnaryLengthTM 1 c = _
      simp [c, Drun, Dhalted, Dstep, Dread, DUnaryLengthTM,
        DUnaryLengthState.start, DUnaryLengthState.copy,
        DUnaryLengthState.handoff, DUnaryLengthState.countStart,
    DUnaryLengthState.count,
        DUnaryLengthState.done]
  | cons b bs ih =>
      rw [show (b :: bs).length + 1 = 1 + (bs.length + 1) by
        simp [Nat.add_comm, Nat.add_left_comm]]
      rw [Drun_add_eq]
      let c : DConfig DUnaryLengthState :=
        { state := DUnaryLengthState.copy, input := pre ++ b :: bs,
          head := pre.length + 1, output := pre, work := wk, workHead := wh }
      let c' : DConfig DUnaryLengthState :=
        { state := DUnaryLengthState.copy, input := pre ++ b :: bs,
          head := pre.length + 2, output := pre ++ [b], work := wk, workHead := wh }
      have hstep : Drun DUnaryLengthTM 1 c = c' := by
        simp [c, c', Drun, Dhalted, Dstep, Dread, DUnaryLengthTM, Dmove,
          DUnaryLengthState.start, DUnaryLengthState.copy,
          DUnaryLengthState.handoff, DUnaryLengthState.countStart,
    DUnaryLengthState.count,
          DUnaryLengthState.done]
      change Drun DUnaryLengthTM (bs.length + 1) (Drun DUnaryLengthTM 1 c) = _
      rw [hstep]
      simpa [c', List.append_assoc, Nat.add_comm, Nat.add_left_comm] using ih (pre := pre ++ [b])

/-- A handoff resets the heads, replaces the input by the output, clears the
    output, and blanks the work tape. -/
lemma Drun_DUnaryLengthTM_handoff (x : Word) (_h : Nat)
    (wk : Nat → Bool) (wh : Nat) :
    Drun DUnaryLengthTM 1
      { state := DUnaryLengthState.handoff, input := x, head := _h, output := x,
        work := wk, workHead := wh } =
      { state := DUnaryLengthState.countStart, input := x, head := 0, output := [],
        work := fun _ : Nat => false, workHead := 0 } := by
  rw [Drun_succ_eq_run_nextConfig]
  simp [Drun, DnextConfig, Dhalted, Dstep, Dread, DUnaryLengthTM,
    DUnaryLengthState.start, DUnaryLengthState.copy,
    DUnaryLengthState.handoff, DUnaryLengthState.countStart,
    DUnaryLengthState.count,
    DUnaryLengthState.done]

/-- Leave the left boundary before counting the input bits. -/
lemma Drun_DUnaryLengthTM_count_start (x : Word) :
    Drun DUnaryLengthTM 1
      { state := DUnaryLengthState.countStart, input := x, head := 0,
        output := [], work := fun _ : Nat => false, workHead := 0 } =
      { state := DUnaryLengthState.count, input := x, head := 1,
        output := [], work := fun _ : Nat => false, workHead := 0 } := by
  simp [Drun, Dhalted, Dstep, Dread, DUnaryLengthTM, Dmove,
    DUnaryLengthState.start, DUnaryLengthState.copy,
    DUnaryLengthState.handoff, DUnaryLengthState.countStart,
    DUnaryLengthState.count,
    DUnaryLengthState.done]

/-- The count phase emits one `true` per input bit and then a final `false`. -/
lemma Drun_DUnaryLengthTM_count_suffix (pre suffix out : Word)
    (wk : Nat → Bool) (wh : Nat) :
    Drun DUnaryLengthTM (suffix.length + 1)
      { state := DUnaryLengthState.count, input := pre ++ suffix,
        head := pre.length + 1, output := out, work := wk, workHead := wh } =
      { state := DUnaryLengthState.done, input := pre ++ suffix,
        head := (pre ++ suffix).length + 1,
        output := out ++ List.replicate suffix.length true ++ [false],
        work := wk, workHead := wh } := by
  induction suffix generalizing pre out with
  | nil =>
      let c : DConfig DUnaryLengthState :=
        { state := DUnaryLengthState.count, input := pre ++ [], head := pre.length + 1,
          output := out, work := wk, workHead := wh }
      change Drun DUnaryLengthTM 1 c = _
      simp [c, Drun, Dhalted, Dstep, Dread, DUnaryLengthTM,
        DUnaryLengthState.start, DUnaryLengthState.copy,
        DUnaryLengthState.handoff, DUnaryLengthState.countStart,
    DUnaryLengthState.count,
        DUnaryLengthState.done]
  | cons b bs ih =>
      rw [show (b :: bs).length + 1 = 1 + (bs.length + 1) by
        simp [Nat.add_comm, Nat.add_left_comm]]
      rw [Drun_add_eq]
      let c : DConfig DUnaryLengthState :=
        { state := DUnaryLengthState.count, input := pre ++ b :: bs,
          head := pre.length + 1, output := out, work := wk, workHead := wh }
      let c' : DConfig DUnaryLengthState :=
        { state := DUnaryLengthState.count, input := pre ++ b :: bs,
          head := pre.length + 2, output := out ++ [true],
          work := wk, workHead := wh }
      have hstep : Drun DUnaryLengthTM 1 c = c' := by
        simp [c, c', Drun, Dhalted, Dstep, Dread, DUnaryLengthTM, Dmove,
          DUnaryLengthState.start, DUnaryLengthState.copy,
          DUnaryLengthState.handoff, DUnaryLengthState.countStart,
    DUnaryLengthState.count,
          DUnaryLengthState.done]
      change Drun DUnaryLengthTM (bs.length + 1) (Drun DUnaryLengthTM 1 c) = _
      rw [hstep]
      simpa [c', List.replicate_succ, List.append_assoc, Nat.add_comm,
        Nat.add_left_comm] using ih (pre := pre ++ [b]) (out := out ++ [true])

theorem dPolyTimeComputable_unary_length :
    DPolyTimeComputable (fun x => List.replicate x.length true ++ [false]) := by
  refine ⟨DUnaryLengthState, inferInstance, inferInstance, DUnaryLengthTM,
    C 2 * X + C 5, X + C 1, ?_, ?_⟩
  · intro x
    have hstart := Drun_DUnaryLengthTM_start x
    have hcopy : Drun DUnaryLengthTM (x.length + 1)
        { state := DUnaryLengthState.copy, input := x, head := 1, output := [],
          work := fun _ : Nat => false, workHead := 0 } =
        { state := DUnaryLengthState.handoff, input := x, head := x.length + 1,
          output := x, work := fun _ : Nat => false, workHead := 0 } := by
      simpa using (Drun_DUnaryLengthTM_copy_suffix [] x (fun _ : Nat => false) 0)
    have hhand : Drun DUnaryLengthTM 1
        { state := DUnaryLengthState.handoff, input := x, head := x.length + 1,
          output := x, work := fun _ : Nat => false, workHead := 0 } =
        { state := DUnaryLengthState.countStart, input := x, head := 0, output := [],
          work := fun _ : Nat => false, workHead := 0 } := by
      simpa using (Drun_DUnaryLengthTM_handoff x (x.length + 1)
        (fun _ : Nat => false) 0)
    have hcountStart : Drun DUnaryLengthTM 1
        { state := DUnaryLengthState.countStart, input := x, head := 0,
          output := [], work := fun _ : Nat => false, workHead := 0 } =
        { state := DUnaryLengthState.count, input := x, head := 1,
          output := [], work := fun _ : Nat => false, workHead := 0 } := by
      simpa using (Drun_DUnaryLengthTM_count_start x)
    have hcount : Drun DUnaryLengthTM (x.length + 1)
        { state := DUnaryLengthState.count, input := x, head := 1, output := [],
          work := fun _ : Nat => false, workHead := 0 } =
        { state := DUnaryLengthState.done, input := x, head := x.length + 1,
          output := List.replicate x.length true ++ [false],
          work := fun _ : Nat => false, workHead := 0 } := by
      simpa using
        (Drun_DUnaryLengthTM_count_suffix [] x [] (fun _ : Nat => false) 0)
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_X]
    change Dhalted DUnaryLengthTM
      (Drun DUnaryLengthTM (2 * x.length + 5) (Dinit DUnaryLengthTM x)) = true
    rw [show 2 * x.length + 5 = 1 + ((x.length + 1) + (1 + (1 + (x.length + 1)))) by omega]
    rw [Drun_add_eq, hstart]
    rw [Drun_add_eq, hcopy]
    rw [Drun_add_eq, hhand]
    rw [Drun_add_eq, hcountStart]
    rw [hcount]
    simp [Dhalted, DUnaryLengthTM, DUnaryLengthState.done]
  · intro x
    have hstart := Drun_DUnaryLengthTM_start x
    have hcopy : Drun DUnaryLengthTM (x.length + 1)
        { state := DUnaryLengthState.copy, input := x, head := 1, output := [],
          work := fun _ : Nat => false, workHead := 0 } =
        { state := DUnaryLengthState.handoff, input := x, head := x.length + 1,
          output := x, work := fun _ : Nat => false, workHead := 0 } := by
      simpa using (Drun_DUnaryLengthTM_copy_suffix [] x (fun _ : Nat => false) 0)
    have hhand : Drun DUnaryLengthTM 1
        { state := DUnaryLengthState.handoff, input := x, head := x.length + 1,
          output := x, work := fun _ : Nat => false, workHead := 0 } =
        { state := DUnaryLengthState.countStart, input := x, head := 0, output := [],
          work := fun _ : Nat => false, workHead := 0 } := by
      simpa using (Drun_DUnaryLengthTM_handoff x (x.length + 1)
        (fun _ : Nat => false) 0)
    have hcountStart : Drun DUnaryLengthTM 1
        { state := DUnaryLengthState.countStart, input := x, head := 0,
          output := [], work := fun _ : Nat => false, workHead := 0 } =
        { state := DUnaryLengthState.count, input := x, head := 1,
          output := [], work := fun _ : Nat => false, workHead := 0 } := by
      simpa using (Drun_DUnaryLengthTM_count_start x)
    have hcount : Drun DUnaryLengthTM (x.length + 1)
        { state := DUnaryLengthState.count, input := x, head := 1, output := [],
          work := fun _ : Nat => false, workHead := 0 } =
        { state := DUnaryLengthState.done, input := x, head := x.length + 1,
          output := List.replicate x.length true ++ [false],
          work := fun _ : Nat => false, workHead := 0 } := by
      simpa using
        (Drun_DUnaryLengthTM_count_suffix [] x [] (fun _ : Nat => false) 0)
    constructor
    · change Dboutput DUnaryLengthTM ((C 2 * X + C 5 : TimeBound).eval x.length) x =
        List.replicate x.length true ++ [false]
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_X]
      change (Drun DUnaryLengthTM (2 * x.length + 5)
        (Dinit DUnaryLengthTM x)).output =
        List.replicate x.length true ++ [false]
      rw [show 2 * x.length + 5 = 1 + ((x.length + 1) + (1 + (1 + (x.length + 1)))) by omega]
      rw [Drun_add_eq, hstart]
      rw [Drun_add_eq, hcopy]
      rw [Drun_add_eq, hhand]
      rw [Drun_add_eq, hcountStart]
      rw [hcount]
    · simp

/-- Composing the unary-length transducer with a fixed prefix gives the
    encoding of the variable whose index is the input length:
    `[false, false] ++ replicate |x| true ++ [false]`. -/
theorem dPolyTimeComputable_var_encoding_length :
    DPolyTimeComputable
      (fun x => ([false, false] : Word) ++ (List.replicate x.length true ++ [false])) := by
  have hcomp := DPolyTimeComputableClosedUnderComposition
    (fun x => List.replicate x.length true ++ [false])
    (fun z => ([false, false] : Word) ++ z)
    dPolyTimeComputable_unary_length
    (dPolyTimeComputable_prepend [false, false])
  simpa [Function.comp_def, List.append_assoc] using hcomp

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
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

namespace Circuit

/-- Evaluate a circuit on a word; missing input bits are read as `false`. -/
def eval : Circuit → Word → Bool
  | const b, _ => b
  | var i, x => x.getD i false
  | not c, x => Bool.not (c.eval x)
  | and c₁ c₂, x => Bool.and (c₁.eval x) (c₂.eval x)
  | or c₁ c₂, x => Bool.or (c₁.eval x) (c₂.eval x)

/-- The tree size, retained for comparison with the sharing-aware size below. -/
def treeSize : Circuit → Nat
  | const _ => 1
  | var _ => 1
  | not c => 1 + c.treeSize
  | and c₁ c₂ => 1 + c₁.treeSize + c₂.treeSize
  | or c₁ c₂ => 1 + c₁.treeSize + c₂.treeSize

/-- The set of distinct subcircuits, including gates and leaves.  This is what
    makes the size measure sharing-aware: a subcircuit used in several places is
    counted once. -/
def nodes : Circuit → Finset Circuit
  | const b => {const b}
  | var i => {var i}
  | not c => insert (not c) c.nodes
  | and c₁ c₂ => insert (and c₁ c₂) (c₁.nodes ∪ c₂.nodes)
  | or c₁ c₂ => insert (or c₁ c₂) (c₁.nodes ∪ c₂.nodes)

/-- Number of distinct gates/leaves in a circuit. -/
def size (c : Circuit) : Nat := c.nodes.card

/-- Number of nodes of `c` that are not already in the finite set `S`.  This is
    the key measure for a step that reuses an earlier layer of circuits. -/
def rel (S : Finset Circuit) (c : Circuit) : Nat := (c.nodes \ S).card

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

lemma eval_orMany_eq_true_iff (cs : List Circuit) (x : Word) :
    (orMany cs).eval x = true ↔ ∃ c ∈ cs, c.eval x = true := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
      cases hc : c.eval x <;> simp [orMany, hc, ih]

lemma eval_orMany_eq_false_iff (cs : List Circuit) (x : Word) :
    (orMany cs).eval x = false ↔ ∀ c ∈ cs, c.eval x = false := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
      cases hc : c.eval x <;> simp [orMany, hc, ih]

/-- The largest input variable index used by a circuit. -/
def maxVar : Circuit → Nat
  | const _ => 0
  | var i => i
  | not c => c.maxVar
  | and c₁ c₂ => max c₁.maxVar c₂.maxVar
  | or c₁ c₂ => max c₁.maxVar c₂.maxVar

/-- The finite set of input variable indices used by a circuit. -/
def vars : Circuit → Finset Nat
  | const _ => ∅
  | var i => {i}
  | not c => c.vars
  | and c₁ c₂ => c₁.vars ∪ c₂.vars
  | or c₁ c₂ => c₁.vars ∪ c₂.vars

lemma mem_vars_le_maxVar {c : Circuit} {i : Nat} (hi : i ∈ c.vars) : i ≤ c.maxVar := by
  induction c with
  | const b => simp [vars] at hi
  | var j =>
      simp [vars] at hi
      subst i
      rfl
  | not c ih => simpa [vars, maxVar] using ih hi
  | and c₁ c₂ ih1 ih2 =>
      simp only [vars, Finset.mem_union] at hi
      rcases hi with hi | hi
      · exact Nat.le_trans (ih1 hi) (Nat.le_max_left _ _)
      · exact Nat.le_trans (ih2 hi) (Nat.le_max_right _ _)
  | or c₁ c₂ ih1 ih2 =>
      simp only [vars, Finset.mem_union] at hi
      rcases hi with hi | hi
      · exact Nat.le_trans (ih1 hi) (Nat.le_max_left _ _)
      · exact Nat.le_trans (ih2 hi) (Nat.le_max_right _ _)

lemma eval_eq_of_agree_on_vars_finset (c : Circuit) {x y : Word}
    (h : ∀ i ∈ c.vars, x.getD i false = y.getD i false) :
    c.eval x = c.eval y := by
  induction c with
  | const b => simp [Circuit.eval]
  | var i =>
      simp [vars, Circuit.eval] at h ⊢
      exact h
  | not c ih =>
      dsimp [Circuit.eval]
      rw [ih (by intro i hi; exact h i (by simp [vars, hi]))]
  | and c₁ c₂ ih1 ih2 =>
      dsimp [Circuit.eval]
      rw [ih1 (by intro i hi; exact h i (by simp [vars, hi]))]
      rw [ih2 (by intro i hi; exact h i (by simp [vars, hi]))]
  | or c₁ c₂ ih1 ih2 =>
      dsimp [Circuit.eval]
      rw [ih1 (by intro i hi; exact h i (by simp [vars, hi]))]
      rw [ih2 (by intro i hi; exact h i (by simp [vars, hi]))]

lemma vars_orMany_subset {cs : List Circuit} {m : Nat}
    (h : ∀ c ∈ cs, c.vars ⊆ Finset.range m) : (orMany cs).vars ⊆ Finset.range m := by
  induction cs with
  | nil => simp [orMany, vars]
  | cons c cs ih =>
      intro i hi
      simp only [orMany, vars, Finset.mem_union] at hi
      rcases hi with hi | hi
      · exact h c (by simp) hi
      · exact ih (by intro d hd; exact h d (by simp [hd])) hi

lemma vars_ite_subset {c t e : Circuit} {m : Nat}
    (hc : c.vars ⊆ Finset.range m) (ht : t.vars ⊆ Finset.range m)
    (he : e.vars ⊆ Finset.range m) : (ite c t e).vars ⊆ Finset.range m := by
  intro i hi
  dsimp [ite] at hi
  simp only [Circuit.vars, Finset.mem_union] at hi
  rcases hi with (hi | hi) | (hi | hi)
  · exact hc hi
  · exact ht hi
  · exact hc hi
  · exact he hi

lemma vars_or_subset {c₁ c₂ : Circuit} {m : Nat}
    (h1 : c₁.vars ⊆ Finset.range m) (h2 : c₂.vars ⊆ Finset.range m) :
    (or c₁ c₂).vars ⊆ Finset.range m := by
  intro i hi
  simp only [vars, Finset.mem_union] at hi
  rcases hi with hi | hi
  · exact h1 hi
  · exact h2 hi

lemma vars_and_subset {c₁ c₂ : Circuit} {m : Nat}
    (h1 : c₁.vars ⊆ Finset.range m) (h2 : c₂.vars ⊆ Finset.range m) :
    (and c₁ c₂).vars ⊆ Finset.range m := by
  intro i hi
  simp only [vars, Finset.mem_union] at hi
  rcases hi with hi | hi
  · exact h1 hi
  · exact h2 hi

lemma vars_not_subset {c : Circuit} {m : Nat} (h : c.vars ⊆ Finset.range m) :
    (not c).vars ⊆ Finset.range m := by
  simpa [vars] using h

lemma eval_eq_of_agree_on_vars (c : Circuit) {x y : Word}
    (h : ∀ i, i ≤ c.maxVar → x.getD i false = y.getD i false) :
    c.eval x = c.eval y := by
  induction c generalizing x y with
  | const b => simp [Circuit.eval]
  | var i => simpa [Circuit.eval, maxVar] using h i le_rfl
  | not c ih =>
      dsimp [Circuit.eval]
      rw [ih (by intro i hi; exact h i hi)]
  | and c₁ c₂ ih1 ih2 =>
      dsimp [Circuit.eval]
      rw [ih1 (by intro i hi; exact h i (Nat.le_trans hi (Nat.le_max_left _ _)))]
      rw [ih2 (by intro i hi; exact h i (Nat.le_trans hi (Nat.le_max_right _ _)))]
  | or c₁ c₂ ih1 ih2 =>
      dsimp [Circuit.eval]
      rw [ih1 (by intro i hi; exact h i (Nat.le_trans hi (Nat.le_max_left _ _)))]
      rw [ih2 (by intro i hi; exact h i (Nat.le_trans hi (Nat.le_max_right _ _)))]

lemma maxVar_orMany_le (cs : List Circuit) (B : Nat)
    (h : ∀ c ∈ cs, c.maxVar ≤ B) : (orMany cs).maxVar ≤ B := by
  induction cs with
  | nil => simp [orMany, maxVar]
  | cons c cs ih =>
      dsimp [orMany, maxVar]
      exact max_le (h c (by simp)) (ih (by
        intro d hd
        exact h d (by simp [hd])))

lemma maxVar_ite_le {c t e : Circuit} {B : Nat}
    (hc : c.maxVar ≤ B) (ht : t.maxVar ≤ B) (he : e.maxVar ≤ B) :
    (ite c t e).maxVar ≤ B := by
  dsimp [ite, maxVar]
  exact max_le (max_le hc ht) (max_le hc he)

lemma const_maxVar_le (B : Nat) (b : Bool) : (Circuit.const b).maxVar ≤ B := by
  simp [Circuit.maxVar]

/-- Truncating a word beyond `n` does not change bits below `n`. -/
lemma word_getD_take_eq_of_lt_aux : ∀ (l : Word) (n i : Nat),
    i < n → (l.take n).getD i false = l.getD i false := by
  intro l n
  induction l generalizing n with
  | nil => intro i hi; simp
  | cons b l ih =>
      intro i hi
      cases i with
      | zero =>
          cases n with
          | zero => omega
          | succ n => simp
      | succ i =>
          cases n with
          | zero => omega
          | succ n => simpa using ih n i (by omega)

lemma word_getD_take_eq_of_lt (l : Word) {n i : Nat} (hi : i < n) :
    (l.take n).getD i false = l.getD i false :=
  word_getD_take_eq_of_lt_aux l n i hi

/-- Replace every variable `i` by the circuit `g i`.  In applications `g i` is
    `const false` outside the fixed input length, so the result may be evaluated
    on a word of that length. -/
def substVars (g : Nat → Circuit) : Circuit → Circuit
  | const b => const b
  | var i => g i
  | not c => not (substVars g c)
  | and c₁ c₂ => and (substVars g c₁) (substVars g c₂)
  | or c₁ c₂ => or (substVars g c₁) (substVars g c₂)

/-- Evaluation of a substitution against the word obtained from the first `m`
    variables. -/
lemma eval_substVars (g : Nat → Circuit) (m : Nat)
    (hg : ∀ i, m ≤ i → g i = const false) (c : Circuit) (x : Word) :
    (substVars g c).eval x =
      c.eval (List.ofFn (fun i : Fin m => (g i.val).eval x)) := by
  induction c with
  | const b => simp [substVars]
  | var i =>
      by_cases hi : i < m
      · simp [substVars, hi]
      · have him : m ≤ i := by omega
        have hgi : g i = const false := hg i him
        have hget : (List.ofFn (fun j : Fin m => (g j.val).eval x)).getD i false = false := by
          rw [List.getD_eq_default (List.ofFn (fun j : Fin m => (g j.val).eval x)) false
            (by simpa using him)]
        simpa [substVars, hgi] using hget.symm
  | not c ih => simp [substVars, ih]
  | and c₁ c₂ ih1 ih2 => simp [substVars, ih1, ih2]
  | or c₁ c₂ ih1 ih2 => simp [substVars, ih1, ih2]

@[simp] lemma size_const (b : Bool) : (const b).size = 1 := by
  simp [size, nodes]
@[simp] lemma size_var (i : Nat) : (var i).size = 1 := by
  simp [size, nodes]

lemma rel_insert_le (S : Finset Circuit) (a : Circuit) (s : Finset Circuit) :
    ((insert a s) \ S).card ≤ 1 + (s \ S).card := by
  have hsub : (insert a s) \ S ⊆ insert a (s \ S) := by
    intro x hx
    simp at hx ⊢
    rcases hx with ⟨hxmem, hxnot⟩
    rcases hxmem with rfl | hxmem
    · simp
    · exact Or.inr ⟨hxmem, hxnot⟩
  have hcard := Finset.card_le_card hsub
  have hins := Finset.card_insert_le a (s \ S)
  omega

lemma rel_not (S : Finset Circuit) (c : Circuit) :
    rel S (not c) ≤ 1 + rel S c := by
  dsimp [rel, nodes]
  exact rel_insert_le S (not c) c.nodes

lemma rel_binary (S : Finset Circuit) (a c₁ c₂ : Circuit) :
    ((insert a (c₁.nodes ∪ c₂.nodes)) \ S).card ≤
      1 + (c₁.nodes \ S).card + (c₂.nodes \ S).card := by
  have h1 := rel_insert_le S a (c₁.nodes ∪ c₂.nodes)
  have hsub : ((c₁.nodes ∪ c₂.nodes) \ S) ⊆
      (c₁.nodes \ S) ∪ (c₂.nodes \ S) := by
    intro x hx
    simp at hx ⊢
    exact Or.elim hx.1 (fun h => Or.inl ⟨h, hx.2⟩) (fun h => Or.inr ⟨h, hx.2⟩)
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le (c₁.nodes \ S) (c₂.nodes \ S)
  omega

lemma rel_and (S : Finset Circuit) (c₁ c₂ : Circuit) :
    rel S (and c₁ c₂) ≤ 1 + rel S c₁ + rel S c₂ := by
  dsimp [rel, nodes]
  exact rel_binary S (and c₁ c₂) c₁ c₂

lemma rel_or (S : Finset Circuit) (c₁ c₂ : Circuit) :
    rel S (or c₁ c₂) ≤ 1 + rel S c₁ + rel S c₂ := by
  dsimp [rel, nodes]
  exact rel_binary S (or c₁ c₂) c₁ c₂

lemma size_not (c : Circuit) : (not c).size ≤ 1 + c.size := by
  dsimp [size]
  simpa [rel] using rel_not ∅ c

lemma size_and (c₁ c₂ : Circuit) : (and c₁ c₂).size ≤ 1 + c₁.size + c₂.size := by
  dsimp [size]
  simpa [rel] using rel_and ∅ c₁ c₂

lemma size_or (c₁ c₂ : Circuit) : (or c₁ c₂).size ≤ 1 + c₁.size + c₂.size := by
  dsimp [size]
  simpa [rel] using rel_or ∅ c₁ c₂

lemma rel_orMany (S : Finset Circuit) (cs : List Circuit) :
    rel S (orMany cs) ≤ cs.length + 1 + (cs.map (rel S)).sum := by
  induction cs with
  | nil =>
      dsimp [orMany, rel, nodes]
      have hsub : ({const false} : Finset Circuit) \ S ⊆ ({const false} : Finset Circuit) := by
        intro x hx
        simp at hx ⊢
        exact hx.1
      have hcard := Finset.card_le_card hsub
      simp at hcard ⊢
      exact hcard
  | cons c cs ih =>
      dsimp [orMany]
      simp only [List.map_cons, List.sum_cons]
      have h := rel_or S c (orMany cs)
      omega

lemma rel_ite (S : Finset Circuit) (c t e : Circuit) :
    rel S (ite c t e) ≤ 5 + 2 * rel S c + rel S t + rel S e := by
  dsimp [ite]
  have h1 := rel_or S (and c t) (and (not c) e)
  have h2 := rel_and S c t
  have h3 := rel_and S (not c) e
  have h4 := rel_not S c
  omega

lemma rel_const_le_one (S : Finset Circuit) (v : Bool) :
    rel S (const v) ≤ 1 := by
  dsimp [rel, nodes]
  have hsub : ({const v} : Finset Circuit) \ S ⊆ ({const v} : Finset Circuit) := by
    intro x hx
    simp at hx ⊢
    exact hx.1
  have hcard := Finset.card_le_card hsub
  simp at hcard ⊢
  exact hcard

lemma rel_var_le_one (S : Finset Circuit) (i : Nat) :
    rel S (var i) ≤ 1 := by
  dsimp [rel, nodes]
  have hsub : ({var i} : Finset Circuit) \ S ⊆ ({var i} : Finset Circuit) := by
    intro x hx
    simp at hx ⊢
    exact hx.1
  have hcard := Finset.card_le_card hsub
  simp at hcard ⊢
  exact hcard

lemma rel_orMany_le (S : Finset Circuit) (cs : List Circuit) (k : Nat)
    (h : ∀ c ∈ cs, rel S c ≤ k) :
    rel S (orMany cs) ≤ cs.length + 1 + cs.length * k := by
  induction cs with
  | nil =>
      dsimp [orMany]
      have hc := rel_const_le_one S false
      omega
  | cons c cs ih =>
      dsimp [orMany]
      have hc : rel S c ≤ k := h c (by simp)
      have hcs : ∀ d ∈ cs, rel S d ≤ k := by
        intro d hd
        exact h d (by simp [hd])
      have hih := ih hcs
      have hor := rel_or S c (orMany cs)
      have hmul : (cs.length + 1) * k = cs.length * k + k := by
        simp [Nat.succ_mul]
      omega

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

/-- The output word of a bounded transducer is the `t + 1` cells beginning at
    the initial head position.  Using fixed absolute indices is what makes the
    output bits directly representable by circuits. -/
def boutputIn (M : TM) (t : Nat) (x : Word) : Word :=
  let b := brun M t t (binit M t x)
  List.ofFn (fun i : Fin (t + 1) => b.tape ⟨t + i.val, by
    have hi : i.val < t + 1 := i.isLt
    omega⟩)

@[simp] lemma boutputIn_length (M : TM) (t : Nat) (x : Word) :
    (boutputIn M t x).length = t + 1 := by
  simp [boutputIn]

lemma boutputIn_getD (M : TM) (t : Nat) (x : Word) (i : Nat)
    (hi : i < t + 1) :
    (boutputIn M t x).getD i false =
      (brun M t t (binit M t x)).tape ⟨t + i, by omega⟩ := by
  rw [List.getD_eq_getElem (boutputIn M t x) false (by simpa using hi)]
  dsimp [boutputIn]
  simpa using (List.getElem_ofFn
    (f := fun j : Fin (t + 1) =>
      (brun M t t (binit M t x)).tape ⟨t + j.val, by
        have hj : j.val < t + 1 := j.isLt
        omega⟩)
    (by simpa using hi))

-- -----------------------------------------------------------------------------
-- 9. Reductions and NP-completeness
-- -----------------------------------------------------------------------------

/-- A word function is polynomial-time computable if some Turing machine
    writes it on the tape within a polynomially bounded number of steps. -/
def PolyTimeComputable (f : Word → Word) : Prop :=
  ∃ (M : TM) (p : TimeBound),
    (∀ x : Word, halted M (run M (p.eval x.length) (init M x)) = true) ∧
    ∀ x : Word, boutputIn M (p.eval x.length) x = f x

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

/-- The state after one transition is always the transition's new state. -/
lemma step_state (M : TM) (c : Config M) :
    (step M c).state = (M.step c.state c.head).1 := by
  rcases c with ⟨q, l, a, r⟩
  rcases htr : M.step q a with ⟨q', w, dir⟩
  cases dir <;> cases l <;> cases r <;> simp [step, htr]

/-- Read a tape cell at absolute index `i`, given that the head is at `p`. -/
def cellAt (M : TM) (c : Config M) (p i : Nat) : Bool :=
  if i < p then c.left.getD (p - i - 1) false
  else if i = p then c.head
  else c.right.getD (i - p - 1) false

lemma getD_eq_false_of_length_le {l : List Bool} {k : Nat} (h : l.length ≤ k) :
    l.getD k false = false := by
  simp [List.getD, List.getElem?_eq_none h]

/-- Moving right preserves every cell except the old head cell, which receives
    the symbol that was written. -/
lemma cellAt_step_right (M : TM) (c : Config M) (p i : Nat)
    (hdir : (M.step c.state c.head).2.2 = true) :
    cellAt M (step M c) (p + 1) i =
      if i = p then (M.step c.state c.head).2.1 else cellAt M c p i := by
  rcases c with ⟨q, l, a, r⟩
  rcases htr : M.step q a with ⟨q', w, dir⟩
  rw [htr] at hdir
  simp at hdir
  subst dir
  cases r with
  | nil =>
      by_cases hip : i < p
      · have hlt : i < p + 1 := by omega
        have hidx : p + 1 - i - 1 = p - i := by omega
        have hipne : i ≠ p := by omega
        simp [step, cellAt, htr, hip, hlt, hipne, hidx]
        cases hp0 : p - i with
        | zero => omega
        | succ k => simp
      · by_cases hipeq : i = p
        · subst i
          simp [step, cellAt, htr]
        · by_cases hip1 : i = p + 1
          · subst i
            simp [step, cellAt, htr]
          · have hpi : p < i := by omega
            have hlt' : ¬ i < p + 1 := by omega
            simp [step, cellAt, htr, hip, hipeq, hlt']
  | cons b bs =>
      by_cases hip : i < p
      · have hlt : i < p + 1 := by omega
        have hidx : p + 1 - i - 1 = p - i := by omega
        have hipne : i ≠ p := by omega
        simp [step, cellAt, htr, hip, hlt, hipne, hidx]
        cases hp0 : p - i with
        | zero => omega
        | succ k => simp
      · by_cases hipeq : i = p
        · subst i
          simp [step, cellAt, htr]
        · by_cases hip1 : i = p + 1
          · subst i
            simp [step, cellAt, htr]
          · have hpi : p < i := by omega
            have hlt' : ¬ i < p + 1 := by omega
            have hold : i - p - 1 = (i - (p + 1) - 1) + 1 := by omega
            simp [step, cellAt, htr, hip, hipeq, hlt', hip1, hold]

/-- Moving left preserves every cell except the old head cell. -/
lemma cellAt_step_left (M : TM) (c : Config M) (p i : Nat)
    (hp : 0 < p) (hdir : (M.step c.state c.head).2.2 = false) :
    cellAt M (step M c) (p - 1) i =
      if i = p then (M.step c.state c.head).2.1 else cellAt M c p i := by
  rcases c with ⟨q, l, a, r⟩
  rcases htr : M.step q a with ⟨q', w, dir⟩
  rw [htr] at hdir
  simp at hdir
  subst dir
  cases l with
  | nil =>
      by_cases hip : i < p
      · by_cases him : i < p - 1
        · have hipne : i ≠ p := by omega
          simp [step, cellAt, htr, him, hip, hipne]
        · have hieq : i = p - 1 := by omega
          subst i
          have hpne1 : p - 1 ≠ p := by omega
          have hnle : ¬ p ≤ p - 1 := by omega
          have hidx : p - (p - 1) - 1 = 0 := by omega
          simp [step, cellAt, htr, hpne1, hnle, hidx]
      · by_cases hipeq : i = p
        · subst i
          have hlt : ¬ p < p - 1 := by omega
          have hpne0 : p ≠ p - 1 := by omega
          have hidx : p - (p - 1) - 1 = 0 := by omega
          simp [step, cellAt, htr, hlt, hpne0, hidx]
        · have hpi : p < i := by omega
          have hnlt : ¬ i < p := by omega
          have hlt : ¬ i < p - 1 := by omega
          have hipm1 : i ≠ p - 1 := by omega
          have hnew : i - (p - 1) - 1 = i - p := by omega
          have hold : i - p = i - p - 1 + 1 := by omega
          simp [step, cellAt, htr, hnlt, hlt, hipeq, hipm1, hnew]
          rw [hold]
          simp
  | cons b bs =>
      by_cases hip : i < p
      · by_cases him : i < p - 1
        · have hipne : i ≠ p := by omega
          have hold : p - i - 1 = (p - 1 - i - 1) + 1 := by omega
          simp [step, cellAt, htr, him, hip, hipne, hold]
        · have hieq : i = p - 1 := by omega
          subst i
          have hpne1 : p - 1 ≠ p := by omega
          have hnle : ¬ p ≤ p - 1 := by omega
          have hidx : p - (p - 1) - 1 = 0 := by omega
          simp [step, cellAt, htr, hpne1, hnle, hidx]
      · by_cases hipeq : i = p
        · subst i
          have hlt : ¬ p < p - 1 := by omega
          have hpne0 : p ≠ p - 1 := by omega
          have hidx : p - (p - 1) - 1 = 0 := by omega
          simp [step, cellAt, htr, hlt, hpne0, hidx]
        · have hpi : p < i := by omega
          have hnlt : ¬ i < p := by omega
          have hlt : ¬ i < p - 1 := by omega
          have hipm1 : i ≠ p - 1 := by omega
          have hnew : i - (p - 1) - 1 = i - p := by omega
          have hold : i - p = i - p - 1 + 1 := by omega
          simp [step, cellAt, htr, hnlt, hlt, hipeq, hipm1, hnew]
          rw [hold]
          simp

/-- One transition of the original machine, with halting configurations frozen. -/
def nextConfig (M : TM) (c : Config M) : Config M :=
  if halted M c then c else step M c

/-- The bounded configuration represents the original configuration after `s`
    steps, with absolute head position `p`. -/
def Simulates (M : TM) (t s : Nat) (c : Config M) (b : BConfig M t) : Prop :=
  ∃ p : Nat,
    t - s ≤ p ∧ p ≤ t + s ∧
    c.state = b.state ∧
    (∀ i : Fin (2 * t + 1), b.pos = i ↔ p = i.val) ∧
      (∀ i : Fin (2 * t + 1), b.tape i = cellAt M c p i.val)

lemma simulates_init (M : TM) (t : Nat) (x : Word) :
    Simulates M t 0 (init M x) (binit M t x) := by
  refine ⟨t, by omega, by omega, ?_, ?_, ?_⟩
  · cases x <;> rfl
  · intro i
    simp [binit, Fin.ext_iff]
  · intro i
    cases x with
    | nil =>
        by_cases hbelow : i.val < t
        · simp [binit, cellAt, init, hbelow]
        · by_cases heq : i.val = t
          · simp [binit, cellAt, init, heq]
          · simp [binit, cellAt, init, hbelow, heq]
    | cons b bs =>
        by_cases hbelow : i.val < t
        · simp [binit, cellAt, init, hbelow]
        · by_cases heq : i.val = t
          · simp [binit, cellAt, init, heq]
          · have habove : t < i.val := by omega
            have hle : t ≤ i.val := by omega
            by_cases hlt : i.val < t + (b :: bs).length
            · have hlt' : i.val < t + (bs.length + 1) := by simpa using hlt
              have hidx : i.val - t = (i.val - t - 1) + 1 := by omega
              simp [binit, cellAt, init, hbelow, heq, hle, hlt']
              rw [hidx]
              simp
            · have hlen : bs.length ≤ i.val - t - 1 := by
                simp at hlt
                omega
              have hltF' : ¬ i.val < t + (bs.length + 1) := by simpa using hlt
              have hfalse : bs.getD (i.val - t - 1) false = false :=
                getD_eq_false_of_length_le hlen
              have hidx : i.val - t = (i.val - t - 1) + 1 := by omega
              simp [binit, cellAt, init, hbelow, heq, hle, hltF']
              rw [hidx]
              simp
              exact hfalse

lemma simulates_step (M : TM) (t s : Nat) (hs : s < t) (c : Config M)
    (b : BConfig M t) (hsim : Simulates M t s c b) :
    Simulates M t (s + 1) (nextConfig M c) (bnext M t b) := by
  rcases hsim with ⟨p, hp_low, hp_high, hstate, hpos, htape⟩
  have hp_pos : 0 < p := by omega
  have hp_lt : p < 2 * t := by omega
  have hbposval : b.pos.val = p := by
    exact ((hpos b.pos).1 rfl).symm
  have hbhead : b.tape b.pos = c.head := by
    rw [htape b.pos, hbposval]
    simp [cellAt]
  have hstepEq : M.step b.state (b.tape b.pos) = M.step c.state c.head := by
    rw [← hstate, hbhead]
  by_cases hhalt : halted M c = true
  · have hbhalt : bhalt M b = true := by
      simpa [halted, bhalt, hstate] using hhalt
    refine ⟨p, by omega, by omega, ?_, ?_, ?_⟩
    · simp [nextConfig, hhalt, hstate, bnext, hbhalt]
    · intro i
      simpa [bnext, hbhalt] using hpos i
    · intro i
      simpa [nextConfig, hhalt, bnext, hbhalt] using htape i
  · have hhaltF : halted M c = false := by
      cases h : halted M c <;> simp_all
    have hbhalt : bhalt M b = false := by
      simpa [halted, bhalt, hstate] using hhaltF
    have hbnext : bnext M t b = bstep M t b := by
      simp [bnext, hbhalt]
    let tr := M.step c.state c.head
    have hstepEqTr : M.step b.state (b.tape b.pos) = tr := by
      simpa [tr] using hstepEq
    by_cases hdir : tr.2.2 = true
    · let p' := p + 1
      have hposEq : (bstep M t b).pos = ⟨p', by omega⟩ := by
        apply Fin.ext
        simp [bstep, hstepEqTr, hdir, hbposval, hp_lt, p']
      refine ⟨p', by omega, by omega, ?_, ?_, ?_⟩
      · have hstepState : (step M c).state = tr.1 := by
          simpa [tr] using step_state M c
        simp [nextConfig, hhaltF, hbnext, hstepState, bstep, hstepEqTr]
      · intro i
        rw [hbnext, hposEq]
        simp [Fin.ext_iff]
      · intro i
        have hcell : cellAt M (nextConfig M c) p' i.val =
            if i.val = p then tr.2.1 else cellAt M c p i.val := by
          unfold nextConfig
          rw [ite_eq_right (by simp [hhaltF])]
          change cellAt M (step M c) (p + 1) i.val =
            if i.val = p then (M.step c.state c.head).2.1 else cellAt M c p i.val
          exact cellAt_step_right M c p i.val (by simpa [tr] using hdir)
        calc
          (bnext M t b).tape i
              = if i.val == b.pos.val then tr.2.1 else b.tape i := by
                  simp [hbnext, bstep, hstepEqTr]
          _ = if i.val = p then tr.2.1 else cellAt M c p i.val := by
                  rw [hbposval]
                  by_cases hip : i.val = p <;> simp [hip, htape i]
          _ = cellAt M (nextConfig M c) p' i.val := by
                  rw [hcell]
    · have hdirF : tr.2.2 = false := by
        cases h : tr.2.2 <;> simp_all
      let p' := p - 1
      have hposEq : (bstep M t b).pos = ⟨p', by omega⟩ := by
        apply Fin.ext
        simp [bstep, hstepEqTr, hdirF, hbposval, hp_pos, p']
      refine ⟨p', by omega, by omega, ?_, ?_, ?_⟩
      · have hstepState : (step M c).state = tr.1 := by
          simpa [tr] using step_state M c
        simp [nextConfig, hhaltF, hbnext, hstepState, bstep, hstepEqTr]
      · intro i
        rw [hbnext, hposEq]
        simp [Fin.ext_iff]
      · intro i
        have hcell : cellAt M (nextConfig M c) p' i.val =
            if i.val = p then tr.2.1 else cellAt M c p i.val := by
          unfold nextConfig
          rw [ite_eq_right (by simp [hhaltF])]
          change cellAt M (step M c) (p - 1) i.val =
            if i.val = p then (M.step c.state c.head).2.1 else cellAt M c p i.val
          exact cellAt_step_left M c p i.val hp_pos (by simpa [tr] using hdirF)
        calc
          (bnext M t b).tape i
              = if i.val == b.pos.val then tr.2.1 else b.tape i := by
                  simp [hbnext, bstep, hstepEqTr]
          _ = if i.val = p then tr.2.1 else cellAt M c p i.val := by
                  rw [hbposval]
                  by_cases hip : i.val = p <;> simp [hip, htape i]
          _ = cellAt M (nextConfig M c) p' i.val := by
                  rw [hcell]

lemma run_halted (M : TM) (c : Config M) (k : Nat) (h : halted M c = true) :
    run M k c = c := by
  cases k <;> simp [run, h]

lemma run_succ_eq_run_nextConfig (M : TM) (c : Config M) (k : Nat) :
    run M (k + 1) c = run M k (nextConfig M c) := by
  by_cases h : halted M c = true
  · simp [run, h, nextConfig, run_halted M c k h]
  · simp [run, h, nextConfig]

lemma run_add_eq (M : TM) (c : Config M) (a b : Nat) :
    run M (a + b) c = run M b (run M a c) := by
  induction a generalizing c with
  | zero => simp [run]
  | succ a ih =>
      rw [Nat.succ_add, run_succ_eq_run_nextConfig]
      rw [run_succ_eq_run_nextConfig M c a]
      exact ih (nextConfig M c)

/-- Once a run has halted, extending the clock does not change the final
    configuration. -/
lemma run_eq_of_halted_within (M : TM) (c : Config M) {s t : Nat} (hs : s ≤ t)
    (hh : halted M (run M s c) = true) : run M t c = run M s c := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
  rw [hk, run_add_eq, run_halted M (run M s c) k hh]

lemma acceptsIn_eq_of_halted_within (M : TM) (x : Word) {s t : Nat} (hs : s ≤ t)
    (hh : halted M (run M s (init M x)) = true) :
    acceptsIn M x t = acceptsIn M x s := by
  dsimp [acceptsIn]
  rw [run_eq_of_halted_within M (init M x) hs hh]

lemma brun_succ_eq_brun_bnext (M : TM) (t : Nat) (b : BConfig M t) (k : Nat) :
    brun M t (k + 1) b = brun M t k (bnext M t b) := by
  induction k with
  | zero => simp [brun]
  | succ k ih => simpa [brun] using congrArg (bnext M t) ih

lemma simulates_more (M : TM) (t : Nat) :
    ∀ (k s0 : Nat) (c : Config M) (b : BConfig M t),
      s0 + k ≤ t → Simulates M t s0 c b →
        Simulates M t (s0 + k) (run M k c) (brun M t k b) := by
  intro k s0
  induction k generalizing s0 with
  | zero =>
      intro c b hle hsim
      simpa [run, brun] using hsim
  | succ k ih =>
      intro c b hle hsim
      have hs_lt : s0 < t := by omega
      have hstep := simulates_step M t s0 hs_lt c b hsim
      have hle' : (s0 + 1) + k ≤ t := by omega
      have hrec := ih (s0 + 1) (nextConfig M c) (bnext M t b) hle' hstep
      rw [run_succ_eq_run_nextConfig, brun_succ_eq_brun_bnext]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec

lemma simulates_run_init (M : TM) (t s : Nat) (x : Word) (hs : s ≤ t) :
    Simulates M t s (run M s (init M x)) (brun M t s (binit M t x)) := by
  simpa using simulates_more M t s 0 (init M x) (binit M t x) (by simpa using hs)
    (simulates_init M t x)

lemma bacceptsIn_eq_acceptsIn (M : TM) (t : Nat) (x : Word) :
    bacceptsIn M t t x = acceptsIn M x t := by
  have hsim := simulates_run_init M t t x le_rfl
  rcases hsim with ⟨p, hp_low, hp_high, hstate, hpos, htape⟩
  dsimp [bacceptsIn, acceptsIn]
  rw [← hstate]

/-- Boolean vectors of circuits representing a bounded configuration. -/
structure SimBits (S N : Nat) where
  state : Fin S → Circuit
  head : Fin N → Circuit
  tape : Fin N → Circuit

namespace SimBits

/-- All distinct circuit nodes used by a bounded-configuration bit vector. -/
def nodes (b : SimBits S N) : Finset Circuit :=
  ((Finset.univ.biUnion fun q : Fin S => (b.state q).nodes) ∪
    (Finset.univ.biUnion fun i : Fin N => (b.head i).nodes)) ∪
    (Finset.univ.biUnion fun i : Fin N => (b.tape i).nodes)

/-- Sharing-aware size of a bounded-configuration bit vector. -/
def size (b : SimBits S N) : Nat := b.nodes.card

/-- All component circuits use only variables below `B`. -/
def BoundedVars (b : SimBits S N) (B : Nat) : Prop :=
  (∀ q : Fin S, (b.state q).maxVar ≤ B) ∧
    (∀ i : Fin N, (b.head i).maxVar ≤ B) ∧
      (∀ i : Fin N, (b.tape i).maxVar ≤ B)

/-- All component circuits use only input bits below `m`, as a `vars` bound. -/
def VarsBounded (b : SimBits S N) (m : Nat) : Prop :=
  (∀ q : Fin S, (b.state q).vars ⊆ Finset.range m) ∧
    (∀ i : Fin N, (b.head i).vars ⊆ Finset.range m) ∧
      (∀ i : Fin N, (b.tape i).vars ⊆ Finset.range m)

lemma state_nodes_subset (b : SimBits S N) (q : Fin S) :
    (b.state q).nodes ⊆ b.nodes := by
  intro c hc
  simp [nodes]
  exact Or.inl ⟨q, hc⟩

lemma head_nodes_subset (b : SimBits S N) (i : Fin N) :
    (b.head i).nodes ⊆ b.nodes := by
  intro c hc
  simp [nodes]
  exact Or.inr (Or.inl ⟨i, hc⟩)

lemma tape_nodes_subset (b : SimBits S N) (i : Fin N) :
    (b.tape i).nodes ⊆ b.nodes := by
  intro c hc
  simp [nodes]
  exact Or.inr (Or.inr ⟨i, hc⟩)

lemma rel_state_zero (b : SimBits S N) (q : Fin S) :
    ((b.state q).nodes \ b.nodes).card = 0 := by
  have h : (b.state q).nodes \ b.nodes = ∅ :=
    Finset.sdiff_eq_empty_iff_subset.mpr (state_nodes_subset b q)
  simp [h]

lemma rel_head_zero (b : SimBits S N) (i : Fin N) :
    ((b.head i).nodes \ b.nodes).card = 0 := by
  have h : (b.head i).nodes \ b.nodes = ∅ :=
    Finset.sdiff_eq_empty_iff_subset.mpr (head_nodes_subset b i)
  simp [h]

lemma rel_tape_zero (b : SimBits S N) (i : Fin N) :
    ((b.tape i).nodes \ b.nodes).card = 0 := by
  have h : (b.tape i).nodes \ b.nodes = ∅ :=
    Finset.sdiff_eq_empty_iff_subset.mpr (tape_nodes_subset b i)
  simp [h]

lemma nodes_sdiff_le_sum (b b' : SimBits S N) :
    (b'.nodes \ b.nodes).card ≤
      (∑ q : Fin S, (((b'.state q).nodes \ b.nodes).card)) +
      (∑ i : Fin N, (((b'.head i).nodes \ b.nodes).card)) +
      (∑ i : Fin N, (((b'.tape i).nodes \ b.nodes).card)) := by
  let Ustate : Finset Circuit :=
    Finset.univ.biUnion fun q : Fin S => ((b'.state q).nodes \ b.nodes)
  let Uhead : Finset Circuit :=
    Finset.univ.biUnion fun i : Fin N => ((b'.head i).nodes \ b.nodes)
  let Utape : Finset Circuit :=
    Finset.univ.biUnion fun i : Fin N => ((b'.tape i).nodes \ b.nodes)
  have hsub : b'.nodes \ b.nodes ⊆ (Ustate ∪ Uhead) ∪ Utape := by
    intro c hc
    have hcNodes : c ∈ b'.nodes := (Finset.mem_sdiff.mp hc).1
    have hcNot : c ∉ b.nodes := (Finset.mem_sdiff.mp hc).2
    change c ∈ (((Finset.univ.biUnion fun q : Fin S => (b'.state q).nodes) ∪
      (Finset.univ.biUnion fun i : Fin N => (b'.head i).nodes)) ∪
      (Finset.univ.biUnion fun i : Fin N => (b'.tape i).nodes)) at hcNodes
    rw [Finset.mem_union] at hcNodes
    rcases hcNodes with hcNodes | hcNodes
    · rw [Finset.mem_union] at hcNodes
      rcases hcNodes with hcState | hcHead
      · rw [Finset.mem_biUnion] at hcState
        rcases hcState with ⟨q, -, hq⟩
        have hqU : c ∈ Ustate := by
          change c ∈ (Finset.univ.biUnion fun q : Fin S => ((b'.state q).nodes \ b.nodes))
          rw [Finset.mem_biUnion]
          exact ⟨q, Finset.mem_univ q, Finset.mem_sdiff.mpr ⟨hq, hcNot⟩⟩
        rw [Finset.mem_union, Finset.mem_union]
        exact Or.inl (Or.inl hqU)
      · rw [Finset.mem_biUnion] at hcHead
        rcases hcHead with ⟨i, -, hi⟩
        have hiU : c ∈ Uhead := by
          change c ∈ (Finset.univ.biUnion fun i : Fin N => ((b'.head i).nodes \ b.nodes))
          rw [Finset.mem_biUnion]
          exact ⟨i, Finset.mem_univ i, Finset.mem_sdiff.mpr ⟨hi, hcNot⟩⟩
        rw [Finset.mem_union, Finset.mem_union]
        exact Or.inl (Or.inr hiU)
    · rw [Finset.mem_biUnion] at hcNodes
      rcases hcNodes with ⟨i, -, hi⟩
      have hiU : c ∈ Utape := by
        change c ∈ (Finset.univ.biUnion fun i : Fin N => ((b'.tape i).nodes \ b.nodes))
        rw [Finset.mem_biUnion]
        exact ⟨i, Finset.mem_univ i, Finset.mem_sdiff.mpr ⟨hi, hcNot⟩⟩
      rw [Finset.mem_union]
      exact Or.inr hiU
  have hcard := Finset.card_le_card hsub
  have hU1 := Finset.card_union_le Ustate Uhead
  have hU2 := Finset.card_union_le (Ustate ∪ Uhead) Utape
  have hs := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin S)))
      (t := fun q : Fin S => ((b'.state q).nodes \ b.nodes))
  have hh := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin N)))
      (t := fun i : Fin N => ((b'.head i).nodes \ b.nodes))
  have ht := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin N)))
      (t := fun i : Fin N => ((b'.tape i).nodes \ b.nodes))
  simp [Ustate, Uhead, Utape] at hs hh ht hcard hU1 hU2 ⊢
  omega

lemma size_le_add_rel (b b' : SimBits S N) :
    b'.size ≤ b.size + (b'.nodes \ b.nodes).card := by
  have hsub : b'.nodes ⊆ b.nodes ∪ (b'.nodes \ b.nodes) := by
    intro c hc
    rw [Finset.mem_union]
    by_cases h : c ∈ b.nodes
    · exact Or.inl h
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨hc, h⟩)
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le b.nodes (b'.nodes \ b.nodes)
  dsimp [size]
  omega

lemma nodes_le_sum_size (b : SimBits S N) :
    b.size ≤ (∑ q : Fin S, (b.state q).size) +
      (∑ i : Fin N, (b.head i).size) +
      (∑ i : Fin N, (b.tape i).size) := by
  let Ustate : Finset Circuit :=
    Finset.univ.biUnion fun q : Fin S => (b.state q).nodes
  let Uhead : Finset Circuit :=
    Finset.univ.biUnion fun i : Fin N => (b.head i).nodes
  let Utape : Finset Circuit :=
    Finset.univ.biUnion fun i : Fin N => (b.tape i).nodes
  have hsub : b.nodes ⊆ (Ustate ∪ Uhead) ∪ Utape := by
    intro c hc
    change c ∈ (((Finset.univ.biUnion fun q : Fin S => (b.state q).nodes) ∪
      (Finset.univ.biUnion fun i : Fin N => (b.head i).nodes)) ∪
      (Finset.univ.biUnion fun i : Fin N => (b.tape i).nodes)) at hc
    simpa [Ustate, Uhead, Utape] using hc
  have hcard := Finset.card_le_card hsub
  have hU1 := Finset.card_union_le Ustate Uhead
  have hU2 := Finset.card_union_le (Ustate ∪ Uhead) Utape
  have hs := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin S)))
      (t := fun q : Fin S => (b.state q).nodes)
  have hh := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin N)))
      (t := fun i : Fin N => (b.head i).nodes)
  have ht := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin N)))
      (t := fun i : Fin N => (b.tape i).nodes)
  simp [Ustate, Uhead, Utape, size, Circuit.size] at hs hh ht hcard hU1 hU2 ⊢
  omega

lemma state_size_le (b : SimBits S N) (q : Fin S) :
    (b.state q).size ≤ b.size := by
  dsimp [Circuit.size, size]
  exact Finset.card_le_card (state_nodes_subset b q)

lemma tape_size_le (b : SimBits S N) (i : Fin N) :
    (b.tape i).size ≤ b.size := by
  dsimp [Circuit.size, size]
  exact Finset.card_le_card (tape_nodes_subset b i)

end SimBits

lemma maxVar_orMany_ofFn_le {n : Nat} (f : Fin n → Circuit) (B : Nat)
    (h : ∀ i : Fin n, (f i).maxVar ≤ B) : (Circuit.orMany (List.ofFn f)).maxVar ≤ B := by
  apply Circuit.maxVar_orMany_le
  intro c hc
  rw [List.mem_ofFn] at hc
  rcases hc with ⟨i, rfl⟩
  exact h i

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
          (Circuit.const
            (if j.val < 2 * t then j.val + 1 == i.val else j.val == i.val))
          (Circuit.const
            (if 0 < j.val then i.val + 1 == j.val else j.val == i.val))))
  let nextTape : Fin (2 * t + 1) → Circuit := fun i =>
    Circuit.or (Circuit.and (b.head i) writeBit)
      (Circuit.and (Circuit.not (b.head i)) (b.tape i))
  { state := fun q' => Circuit.ite haltedBits (b.state q') (nextState q')
    head := fun i => Circuit.ite haltedBits (b.head i) (nextHead i)
    tape := fun i => Circuit.ite haltedBits (b.tape i) (nextTape i) }

lemma stepBits_boundedVars (M : TM) (t : Nat)
    (b : SimBits M.numStates (2 * t + 1)) (B : Nat)
    (hb : b.BoundedVars B) : (stepBits M t b).BoundedVars B := by
  rcases hb with ⟨hstate, hhead, htape⟩
  let haltedBits : Circuit := Circuit.or (b.state M.accept) (b.state M.reject)
  have hhalted : haltedBits.maxVar ≤ B := by
    dsimp [haltedBits]
    exact max_le (hstate M.accept) (hstate M.reject)
  let scan : Circuit :=
    Circuit.orMany (List.ofFn fun i : Fin (2 * t + 1) =>
      Circuit.and (b.head i) (b.tape i))
  have hscan : scan.maxVar ≤ B := by
    dsimp [scan]
    apply maxVar_orMany_ofFn_le
    intro i
    exact max_le (hhead i) (htape i)
  let dirRight : Circuit :=
    Circuit.orMany (List.ofFn fun q : Fin M.numStates =>
      Circuit.and (b.state q)
        (Circuit.ite scan
          (Circuit.const (M.step q true).2.2)
          (Circuit.const (M.step q false).2.2)))
  have hdir : dirRight.maxVar ≤ B := by
    dsimp [dirRight]
    apply maxVar_orMany_ofFn_le
    intro q
    exact max_le (hstate q) (Circuit.maxVar_ite_le hscan
      (Circuit.const_maxVar_le B _) (Circuit.const_maxVar_le B _))
  let writeBit : Circuit :=
    Circuit.orMany (List.ofFn fun q : Fin M.numStates =>
      Circuit.and (b.state q)
        (Circuit.ite scan
          (Circuit.const (M.step q true).2.1)
          (Circuit.const (M.step q false).2.1)))
  have hwrite : writeBit.maxVar ≤ B := by
    dsimp [writeBit]
    apply maxVar_orMany_ofFn_le
    intro q
    exact max_le (hstate q) (Circuit.maxVar_ite_le hscan
      (Circuit.const_maxVar_le B _) (Circuit.const_maxVar_le B _))
  let nextState : Fin M.numStates → Circuit := fun q' =>
    Circuit.orMany (List.ofFn fun q : Fin M.numStates =>
      Circuit.and (b.state q)
        (Circuit.ite scan
          (Circuit.const ((M.step q true).1 == q'))
          (Circuit.const ((M.step q false).1 == q'))))
  have hnextState : ∀ q', (nextState q').maxVar ≤ B := by
    intro q'
    dsimp [nextState]
    apply maxVar_orMany_ofFn_le
    intro q
    exact max_le (hstate q) (Circuit.maxVar_ite_le hscan
      (Circuit.const_maxVar_le B _) (Circuit.const_maxVar_le B _))
  let nextHead : Fin (2 * t + 1) → Circuit := fun i =>
    Circuit.orMany (List.ofFn fun j : Fin (2 * t + 1) =>
      Circuit.and (b.head j)
        (Circuit.ite dirRight
          (Circuit.const
            (if j.val < 2 * t then j.val + 1 == i.val else j.val == i.val))
          (Circuit.const
            (if 0 < j.val then i.val + 1 == j.val else j.val == i.val))))
  have hnextHead : ∀ i, (nextHead i).maxVar ≤ B := by
    intro i
    dsimp [nextHead]
    apply maxVar_orMany_ofFn_le
    intro j
    exact max_le (hhead j) (Circuit.maxVar_ite_le hdir
      (Circuit.const_maxVar_le B _) (Circuit.const_maxVar_le B _))
  let nextTape : Fin (2 * t + 1) → Circuit := fun i =>
    Circuit.or (Circuit.and (b.head i) writeBit)
      (Circuit.and (Circuit.not (b.head i)) (b.tape i))
  have hnextTape : ∀ i, (nextTape i).maxVar ≤ B := by
    intro i
    dsimp [nextTape]
    exact max_le (max_le (hhead i) hwrite) (max_le (hhead i) (htape i))
  dsimp [stepBits, SimBits.BoundedVars]
  refine ⟨?_, ?_, ?_⟩
  · intro q'
    exact Circuit.maxVar_ite_le hhalted (hstate q') (hnextState q')
  · intro i
    exact Circuit.maxVar_ite_le hhalted (hhead i) (hnextHead i)
  · intro i
    exact Circuit.maxVar_ite_le hhalted (htape i) (hnextTape i)

lemma stepBits_varsBounded (M : TM) (t : Nat)
    (b : SimBits M.numStates (2 * t + 1)) (m : Nat)
    (hb : b.VarsBounded m) : (stepBits M t b).VarsBounded m := by
  rcases hb with ⟨hstate, hhead, htape⟩
  let haltedBits : Circuit := Circuit.or (b.state M.accept) (b.state M.reject)
  have hhalted : haltedBits.vars ⊆ Finset.range m := by
    dsimp [haltedBits]
    exact Circuit.vars_or_subset (hstate M.accept) (hstate M.reject)
  let scan : Circuit :=
    Circuit.orMany (List.ofFn fun i : Fin (2 * t + 1) =>
      Circuit.and (b.head i) (b.tape i))
  have hscan : scan.vars ⊆ Finset.range m := by
    dsimp [scan]
    apply Circuit.vars_orMany_subset
    intro c hc
    rw [List.mem_ofFn] at hc
    rcases hc with ⟨i, rfl⟩
    exact Circuit.vars_and_subset (hhead i) (htape i)
  let dirRight : Circuit :=
    Circuit.orMany (List.ofFn fun q : Fin M.numStates =>
      Circuit.and (b.state q)
        (Circuit.ite scan
          (Circuit.const (M.step q true).2.2)
          (Circuit.const (M.step q false).2.2)))
  have hdir : dirRight.vars ⊆ Finset.range m := by
    dsimp [dirRight]
    apply Circuit.vars_orMany_subset
    intro c hc
    rw [List.mem_ofFn] at hc
    rcases hc with ⟨q, rfl⟩
    exact Circuit.vars_and_subset (hstate q)
      (Circuit.vars_ite_subset hscan (by simp [Circuit.vars]) (by simp [Circuit.vars]))
  let writeBit : Circuit :=
    Circuit.orMany (List.ofFn fun q : Fin M.numStates =>
      Circuit.and (b.state q)
        (Circuit.ite scan
          (Circuit.const (M.step q true).2.1)
          (Circuit.const (M.step q false).2.1)))
  have hwrite : writeBit.vars ⊆ Finset.range m := by
    dsimp [writeBit]
    apply Circuit.vars_orMany_subset
    intro c hc
    rw [List.mem_ofFn] at hc
    rcases hc with ⟨q, rfl⟩
    exact Circuit.vars_and_subset (hstate q)
      (Circuit.vars_ite_subset hscan (by simp [Circuit.vars]) (by simp [Circuit.vars]))
  let nextState : Fin M.numStates → Circuit := fun q' =>
    Circuit.orMany (List.ofFn fun q : Fin M.numStates =>
      Circuit.and (b.state q)
        (Circuit.ite scan
          (Circuit.const ((M.step q true).1 == q'))
          (Circuit.const ((M.step q false).1 == q'))))
  have hnextState : ∀ q', (nextState q').vars ⊆ Finset.range m := by
    intro q'
    dsimp [nextState]
    apply Circuit.vars_orMany_subset
    intro c hc
    rw [List.mem_ofFn] at hc
    rcases hc with ⟨q, rfl⟩
    exact Circuit.vars_and_subset (hstate q)
      (Circuit.vars_ite_subset hscan (by simp [Circuit.vars]) (by simp [Circuit.vars]))
  let nextHead : Fin (2 * t + 1) → Circuit := fun i =>
    Circuit.orMany (List.ofFn fun j : Fin (2 * t + 1) =>
      Circuit.and (b.head j)
        (Circuit.ite dirRight
          (Circuit.const
            (if j.val < 2 * t then j.val + 1 == i.val else j.val == i.val))
          (Circuit.const
            (if 0 < j.val then i.val + 1 == j.val else j.val == i.val))))
  have hnextHead : ∀ i, (nextHead i).vars ⊆ Finset.range m := by
    intro i
    dsimp [nextHead]
    apply Circuit.vars_orMany_subset
    intro c hc
    rw [List.mem_ofFn] at hc
    rcases hc with ⟨j, rfl⟩
    exact Circuit.vars_and_subset (hhead j)
      (Circuit.vars_ite_subset hdir (by simp [Circuit.vars]) (by simp [Circuit.vars]))
  let nextTape : Fin (2 * t + 1) → Circuit := fun i =>
    Circuit.or (Circuit.and (b.head i) writeBit)
      (Circuit.and (Circuit.not (b.head i)) (b.tape i))
  have hnextTape : ∀ i, (nextTape i).vars ⊆ Finset.range m := by
    intro i
    dsimp [nextTape]
    apply Circuit.vars_or_subset
    · exact Circuit.vars_and_subset (hhead i) hwrite
    · exact Circuit.vars_and_subset (Circuit.vars_not_subset (hhead i)) (htape i)
  dsimp [stepBits, SimBits.VarsBounded]
  refine ⟨?_, ?_, ?_⟩
  · intro q'
    exact Circuit.vars_ite_subset hhalted (hstate q') (hnextState q')
  · intro i
    exact Circuit.vars_ite_subset hhalted (hhead i) (hnextHead i)
  · intro i
    exact Circuit.vars_ite_subset hhalted (htape i) (hnextTape i)

/-- Unroll `s` transition circuits starting from the initial configuration. -/
def unrollBits (M : TM) (t n : Nat) : Nat → SimBits M.numStates (2 * t + 1)
  | 0 => initBits M t n
  | s + 1 => stepBits M t (unrollBits M t n s)

/-- The accept-state circuit of a bounded bit vector. -/
def acceptCircuit (M : TM) (t : Nat) (b : SimBits M.numStates (2 * t + 1)) : Circuit :=
  b.state M.accept

lemma sum_le_card_mul {α : Type} [DecidableEq α] (s : Finset α) (f : α → Nat) (k : Nat)
    (h : ∀ a ∈ s, f a ≤ k) : s.sum f ≤ s.card * k := by
  revert h
  refine Finset.induction_on s ?empty ?insert
  · intro h
    simp
  · intro a s ha ih h
    have ha' : f a ≤ k := h a (by simp)
    have hs' : ∀ b ∈ s, f b ≤ k := by
      intro b hb
      exact h b (by simp [hb])
    have ih' := ih hs'
    rw [Finset.sum_insert ha]
    have hmul : (s.card + 1) * k = s.card * k + k := by
      simp [Nat.succ_mul]
    simp [ha]
    rw [hmul]
    have ih'' : (∑ x ∈ s, f x) ≤ s.card * k := by simpa using ih'
    omega

namespace Circuit

/-- The new top-level node contributed by each original circuit node when
    variables are substituted. -/
def substTop (g : Nat → Circuit) : Circuit → Finset Circuit
  | const b => {const b}
  | var i => (g i).nodes
  | not c => {not (substVars g c)}
  | and c₁ c₂ => {and (substVars g c₁) (substVars g c₂)}
  | or c₁ c₂ => {or (substVars g c₁) (substVars g c₂)}

lemma node_mem_own_nodes (c : Circuit) : c ∈ c.nodes := by
  cases c <;> simp [nodes]

lemma nodes_substVars_subset (g : Nat → Circuit) :
    ∀ c : Circuit, (substVars g c).nodes ⊆ c.nodes.biUnion (substTop g) := by
  intro c
  induction c with
  | const b =>
      intro e he
      change e ∈ ({const b} : Finset Circuit) at he
      rw [Finset.mem_biUnion]
      exact ⟨const b, by simp [nodes], by simpa [substTop] using he⟩
  | var i =>
      intro e he
      change e ∈ (g i).nodes at he
      rw [Finset.mem_biUnion]
      exact ⟨var i, by simp [nodes], by simpa [substTop] using he⟩
  | not c ih =>
      intro e he
      change e ∈ insert (not (substVars g c)) (substVars g c).nodes at he
      rw [Finset.mem_insert] at he
      rcases he with rfl | he
      · rw [Finset.mem_biUnion]
        refine ⟨not c, by simp [nodes], ?_⟩
        simp [substTop]
      · have hc := ih he
        rw [Finset.mem_biUnion] at hc
        rcases hc with ⟨d, hd, hed⟩
        rw [Finset.mem_biUnion]
        refine ⟨d, ?_, hed⟩
        change d ∈ insert (not c) c.nodes
        simp [hd]
  | and c₁ c₂ ih1 ih2 =>
      intro e he
      change e ∈ insert (and (substVars g c₁) (substVars g c₂))
        ((substVars g c₁).nodes ∪ (substVars g c₂).nodes) at he
      rw [Finset.mem_insert] at he
      rcases he with rfl | he
      · rw [Finset.mem_biUnion]
        refine ⟨and c₁ c₂, by simp [nodes], ?_⟩
        simp [substTop]
      · rw [Finset.mem_union] at he
        rcases he with he | he
        · have hc := ih1 he
          rw [Finset.mem_biUnion] at hc
          rcases hc with ⟨d, hd, hed⟩
          rw [Finset.mem_biUnion]
          refine ⟨d, ?_, hed⟩
          change d ∈ insert (and c₁ c₂) (c₁.nodes ∪ c₂.nodes)
          simp [hd]
        · have hc := ih2 he
          rw [Finset.mem_biUnion] at hc
          rcases hc with ⟨d, hd, hed⟩
          rw [Finset.mem_biUnion]
          refine ⟨d, ?_, hed⟩
          change d ∈ insert (and c₁ c₂) (c₁.nodes ∪ c₂.nodes)
          simp [hd]
  | or c₁ c₂ ih1 ih2 =>
      intro e he
      change e ∈ insert (or (substVars g c₁) (substVars g c₂))
        ((substVars g c₁).nodes ∪ (substVars g c₂).nodes) at he
      rw [Finset.mem_insert] at he
      rcases he with rfl | he
      · rw [Finset.mem_biUnion]
        refine ⟨or c₁ c₂, by simp [nodes], ?_⟩
        simp [substTop]
      · rw [Finset.mem_union] at he
        rcases he with he | he
        · have hc := ih1 he
          rw [Finset.mem_biUnion] at hc
          rcases hc with ⟨d, hd, hed⟩
          rw [Finset.mem_biUnion]
          refine ⟨d, ?_, hed⟩
          change d ∈ insert (or c₁ c₂) (c₁.nodes ∪ c₂.nodes)
          simp [hd]
        · have hc := ih2 he
          rw [Finset.mem_biUnion] at hc
          rcases hc with ⟨d, hd, hed⟩
          rw [Finset.mem_biUnion]
          refine ⟨d, ?_, hed⟩
          change d ∈ insert (or c₁ c₂) (c₁.nodes ∪ c₂.nodes)
          simp [hd]

lemma substTop_card_le (g : Nat → Circuit) (k : Nat)
    (hg : ∀ i, (g i).size ≤ k) (hk : 1 ≤ k) (d : Circuit) :
    (substTop g d).card ≤ k := by
  cases d with
  | const b => simpa [substTop, size] using hk
  | var i => simpa [substTop, size] using hg i
  | not c => simpa [substTop] using hk
  | and c₁ c₂ => simpa [substTop] using hk
  | or c₁ c₂ => simpa [substTop] using hk

lemma size_substVars_le (g : Nat → Circuit) (k : Nat)
    (hg : ∀ i, (g i).size ≤ k) (hk : 1 ≤ k) (c : Circuit) :
    (substVars g c).size ≤ c.size * k := by
  have hsub := nodes_substVars_subset g c
  have hcard := Finset.card_le_card hsub
  have hbi := Finset.card_biUnion_le (s := c.nodes) (t := substTop g)
  have hsum := sum_le_card_mul c.nodes (fun d => (substTop g d).card) k (by
    intro d hd
    exact substTop_card_le g k hg hk d)
  dsimp [size] at hcard hbi hsum ⊢
  omega

end Circuit

lemma two_mul_state_bound (S N : Nat) :
    2 * (S * (2 * N + 1)) = 4 * S * N + 2 * S := by
  calc
    2 * (S * (2 * N + 1)) = 2 * (S * (2 * N) + S) := by simp [Nat.mul_add]
    _ = 2 * (S * (2 * N)) + 2 * S := by rw [Nat.mul_add]
    _ = 4 * S * N + 2 * S := by
      have hm : 2 * (S * (2 * N)) = 4 * S * N := by ac_rfl
      rw [hm]

lemma two_mul_head_bound (S N : Nat) :
    2 * (N * (1 + 11 * S + 4 * S * N)) =
      2 * N + 22 * S * N + 8 * S * N ^ 2 := by
  simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, pow_two]

/-- Polynomial bound on the number of *new* distinct circuit nodes introduced by
    one bounded transition, as a function of the window radius `t`.  All machine
    parameters are constants for a fixed TM. -/
def stepRelBound (M : TM) (t : Nat) : Nat :=
  let S := M.numStates
  let N := 2 * t + 1
  S * (8 + 11 * S + 4 * S * N) +
    N * (8 + 11 * N + 22 * S * N + 8 * S * N ^ 2) +
      N * (12 + 11 * S + 4 * S * N)

/-- One bounded transition introduces only polynomially many new distinct
    circuit nodes, because the scan/direction/write subcircuits are shared. -/
lemma step_rel_bound (M : TM) (t : Nat) (b : SimBits M.numStates (2 * t + 1)) :
    ((stepBits M t b).nodes \ b.nodes).card ≤ stepRelBound M t := by
  let S := M.numStates
  let N := 2 * t + 1
  let B : Finset Circuit := b.nodes
  let halted : Circuit := Circuit.or (b.state M.accept) (b.state M.reject)
  let scan : Circuit := Circuit.orMany (List.ofFn fun i : Fin N =>
    Circuit.and (b.head i) (b.tape i))
  let dir : Circuit := Circuit.orMany (List.ofFn fun q : Fin S =>
    Circuit.and (b.state q)
      (Circuit.ite scan
        (Circuit.const (M.step q true).2.2)
        (Circuit.const (M.step q false).2.2)))
  let write : Circuit := Circuit.orMany (List.ofFn fun q : Fin S =>
    Circuit.and (b.state q)
      (Circuit.ite scan
        (Circuit.const (M.step q true).2.1)
        (Circuit.const (M.step q false).2.1)))
  have hstate (q : Fin M.numStates) : Circuit.rel B (b.state q) = 0 := by
    dsimp [B, Circuit.rel]
    simpa using SimBits.rel_state_zero b q
  have hhead (i : Fin N) : Circuit.rel B (b.head i) = 0 := by
    dsimp [B, N, Circuit.rel]
    simpa using SimBits.rel_head_zero b (show Fin (2 * t + 1) from i)
  have htape (i : Fin N) : Circuit.rel B (b.tape i) = 0 := by
    dsimp [B, N, Circuit.rel]
    simpa using SimBits.rel_tape_zero b (show Fin (2 * t + 1) from i)
  have hhalt : Circuit.rel B halted ≤ 1 := by
    dsimp [halted]
    have h := Circuit.rel_or B (b.state M.accept) (b.state M.reject)
    rw [hstate, hstate] at h
    omega
  have hscan : Circuit.rel B scan ≤ 2 * N + 1 := by
    change Circuit.rel B (Circuit.orMany (List.ofFn fun i : Fin N =>
      Circuit.and (b.head i) (b.tape i))) ≤ 2 * N + 1
    have h := Circuit.rel_orMany_le B
      (List.ofFn fun i : Fin N => Circuit.and (b.head i) (b.tape i)) 1 (by
        intro c hc
        rw [List.mem_ofFn] at hc
        rcases hc with ⟨i, rfl⟩
        have hi := Circuit.rel_and B (b.head i) (b.tape i)
        rw [hhead i, htape i] at hi
        omega)
    have hlen :
        (List.ofFn fun i : Fin N => Circuit.and (b.head i) (b.tape i)).length = N := by
      simpa using (List.length_ofFn (f := fun i : Fin N =>
        Circuit.and (b.head i) (b.tape i)))
    rw [hlen] at h
    omega
  have hdirRaw : Circuit.rel B dir ≤ S + 1 + S * (8 + 2 * Circuit.rel B scan) := by
    change Circuit.rel B (Circuit.orMany (List.ofFn fun q : Fin S =>
      Circuit.and (b.state q)
        (Circuit.ite scan
          (Circuit.const (M.step q true).2.2)
          (Circuit.const (M.step q false).2.2)))) ≤
        S + 1 + S * (8 + 2 * Circuit.rel B scan)
    have h := Circuit.rel_orMany_le B
      (List.ofFn fun q : Fin S =>
        Circuit.and (b.state q)
          (Circuit.ite scan
            (Circuit.const (M.step q true).2.2)
            (Circuit.const (M.step q false).2.2)))
      (8 + 2 * Circuit.rel B scan) (by
        intro c hc
        rw [List.mem_ofFn] at hc
        rcases hc with ⟨q, rfl⟩
        have hite := Circuit.rel_ite B scan
          (Circuit.const (M.step q true).2.2)
          (Circuit.const (M.step q false).2.2)
        have hc1 := Circuit.rel_const_le_one B (M.step q true).2.2
        have hc2 := Circuit.rel_const_le_one B (M.step q false).2.2
        have hterm := Circuit.rel_and B (b.state q)
          (Circuit.ite scan
            (Circuit.const (M.step q true).2.2)
            (Circuit.const (M.step q false).2.2))
        rw [hstate] at hterm
        omega)
    simpa [List.length_ofFn] using h
  have hdirMul : S * Circuit.rel B scan ≤ S * (2 * N + 1) :=
    Nat.mul_le_mul_left S hscan
  have hdir : Circuit.rel B dir ≤ 1 + 11 * S + 4 * S * N := by
    have htwo : 2 * (S * Circuit.rel B scan) ≤ 2 * (S * (2 * N + 1)) :=
      Nat.mul_le_mul_left 2 hdirMul
    have hA : S * (8 + 2 * Circuit.rel B scan) =
        8 * S + 2 * (S * Circuit.rel B scan) := by
      simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
    have hB := two_mul_state_bound S N
    rw [hA] at hdirRaw
    rw [hB] at htwo
    omega
  have hwrite : Circuit.rel B write ≤ 1 + 11 * S + 4 * S * N := by
    change Circuit.rel B (Circuit.orMany (List.ofFn fun q : Fin S =>
      Circuit.and (b.state q)
        (Circuit.ite scan
          (Circuit.const (M.step q true).2.1)
          (Circuit.const (M.step q false).2.1)))) ≤ 1 + 11 * S + 4 * S * N
    have h := Circuit.rel_orMany_le B
      (List.ofFn fun q : Fin S =>
        Circuit.and (b.state q)
          (Circuit.ite scan
            (Circuit.const (M.step q true).2.1)
            (Circuit.const (M.step q false).2.1)))
      (8 + 2 * Circuit.rel B scan) (by
        intro c hc
        rw [List.mem_ofFn] at hc
        rcases hc with ⟨q, rfl⟩
        have hite := Circuit.rel_ite B scan
          (Circuit.const (M.step q true).2.1)
          (Circuit.const (M.step q false).2.1)
        have hc1 := Circuit.rel_const_le_one B (M.step q true).2.1
        have hc2 := Circuit.rel_const_le_one B (M.step q false).2.1
        have hterm := Circuit.rel_and B (b.state q)
          (Circuit.ite scan
            (Circuit.const (M.step q true).2.1)
            (Circuit.const (M.step q false).2.1))
        rw [hstate] at hterm
        omega)
    have hraw : Circuit.rel B (Circuit.orMany (List.ofFn fun q : Fin S =>
        Circuit.and (b.state q)
          (Circuit.ite scan
            (Circuit.const (M.step q true).2.1)
            (Circuit.const (M.step q false).2.1)))) ≤
        S + 1 + S * (8 + 2 * Circuit.rel B scan) := by
      simpa [List.length_ofFn] using h
    have hdirMul' : S * Circuit.rel B scan ≤ S * (2 * N + 1) :=
      Nat.mul_le_mul_left S hscan
    have htwo : 2 * (S * Circuit.rel B scan) ≤ 2 * (S * (2 * N + 1)) :=
      Nat.mul_le_mul_left 2 hdirMul'
    have hA : S * (8 + 2 * Circuit.rel B scan) =
        8 * S + 2 * (S * Circuit.rel B scan) := by
      simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
    have hB := two_mul_state_bound S N
    rw [hA] at hraw
    rw [hB] at htwo
    omega
  have hnextState (q' : Fin M.numStates) :
      Circuit.rel B (Circuit.orMany (List.ofFn fun q : Fin M.numStates =>
        Circuit.and (b.state q)
          (Circuit.ite scan
            (Circuit.const ((M.step q true).1 == q'))
            (Circuit.const ((M.step q false).1 == q'))))) ≤
        1 + 11 * S + 4 * S * N := by
    have h := Circuit.rel_orMany_le B
      (List.ofFn fun q : Fin S =>
        Circuit.and (b.state q)
          (Circuit.ite scan
            (Circuit.const ((M.step q true).1 == q'))
            (Circuit.const ((M.step q false).1 == q'))))
      (8 + 2 * Circuit.rel B scan) (by
        intro c hc
        rw [List.mem_ofFn] at hc
        rcases hc with ⟨q, rfl⟩
        have hite := Circuit.rel_ite B scan
          (Circuit.const ((M.step q true).1 == q'))
          (Circuit.const ((M.step q false).1 == q'))
        have hc1 := Circuit.rel_const_le_one B ((M.step q true).1 == q')
        have hc2 := Circuit.rel_const_le_one B ((M.step q false).1 == q')
        have hterm := Circuit.rel_and B (b.state q)
          (Circuit.ite scan
            (Circuit.const ((M.step q true).1 == q'))
            (Circuit.const ((M.step q false).1 == q')))
        rw [hstate] at hterm
        omega)
    have hraw : Circuit.rel B (Circuit.orMany (List.ofFn fun q : Fin S =>
        Circuit.and (b.state q)
          (Circuit.ite scan
            (Circuit.const ((M.step q true).1 == q'))
            (Circuit.const ((M.step q false).1 == q'))))) ≤
        S + 1 + S * (8 + 2 * Circuit.rel B scan) := by
      simpa [List.length_ofFn] using h
    have hdirMul' : S * Circuit.rel B scan ≤ S * (2 * N + 1) :=
      Nat.mul_le_mul_left S hscan
    have htwo : 2 * (S * Circuit.rel B scan) ≤ 2 * (S * (2 * N + 1)) :=
      Nat.mul_le_mul_left 2 hdirMul'
    have hA : S * (8 + 2 * Circuit.rel B scan) =
        8 * S + 2 * (S * Circuit.rel B scan) := by
      simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
    have hB := two_mul_state_bound S N
    rw [hA] at hraw
    rw [hB] at htwo
    dsimp [S, N] at hraw htwo hscan hdirRaw hdir hstate hhead htape ⊢
    omega
  have hnextHeadRaw (i : Fin N) :
      Circuit.rel B (Circuit.orMany (List.ofFn fun j : Fin N =>
        Circuit.and (b.head j)
          (Circuit.ite dir
            (Circuit.const
              (if j.val < 2 * t then j.val + 1 == i.val else j.val == i.val))
            (Circuit.const
              (if 0 < j.val then i.val + 1 == j.val else j.val == i.val))))) ≤
        N + 1 + N * (8 + 2 * Circuit.rel B dir) := by
    have h := Circuit.rel_orMany_le B
      (List.ofFn fun j : Fin N =>
        Circuit.and (b.head j)
          (Circuit.ite dir
            (Circuit.const
              (if j.val < 2 * t then j.val + 1 == i.val else j.val == i.val))
            (Circuit.const
              (if 0 < j.val then i.val + 1 == j.val else j.val == i.val))))
      (8 + 2 * Circuit.rel B dir) (by
        intro c hc
        rw [List.mem_ofFn] at hc
        rcases hc with ⟨j, rfl⟩
        have hite := Circuit.rel_ite B dir
          (Circuit.const
            (if j.val < 2 * t then j.val + 1 == i.val else j.val == i.val))
          (Circuit.const
            (if 0 < j.val then i.val + 1 == j.val else j.val == i.val))
        have hc1 := Circuit.rel_const_le_one B
          (if j.val < 2 * t then j.val + 1 == i.val else j.val == i.val)
        have hc2 := Circuit.rel_const_le_one B
          (if 0 < j.val then i.val + 1 == j.val else j.val == i.val)
        have hterm := Circuit.rel_and B (b.head j)
          (Circuit.ite dir
            (Circuit.const
              (if j.val < 2 * t then j.val + 1 == i.val else j.val == i.val))
            (Circuit.const
              (if 0 < j.val then i.val + 1 == j.val else j.val == i.val)))
        rw [hhead j] at hterm
        omega)
    simpa [List.length_ofFn] using h
  have hnextHead (i : Fin N) :
      Circuit.rel B (Circuit.orMany (List.ofFn fun j : Fin N =>
        Circuit.and (b.head j)
          (Circuit.ite dir
            (Circuit.const
              (if j.val < 2 * t then j.val + 1 == i.val else j.val == i.val))
            (Circuit.const
              (if 0 < j.val then i.val + 1 == j.val else j.val == i.val))))) ≤
        1 + 11 * N + 22 * S * N + 8 * S * N ^ 2 := by
    have hNdir : N * Circuit.rel B dir ≤ N * (1 + 11 * S + 4 * S * N) :=
      Nat.mul_le_mul_left N hdir
    have htwo : 2 * (N * Circuit.rel B dir) ≤
        2 * (N * (1 + 11 * S + 4 * S * N)) := Nat.mul_le_mul_left 2 hNdir
    have hA : N * (8 + 2 * Circuit.rel B dir) =
        8 * N + 2 * (N * Circuit.rel B dir) := by
      simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
    have hB := two_mul_head_bound S N
    have hmid : 2 * (N * Circuit.rel B dir) ≤
        2 * N + 22 * S * N + 8 * S * N ^ 2 := by
      rw [← hB]
      exact htwo
    have hraw := hnextHeadRaw i
    rw [hA] at hraw
    omega
  have hnextTape (i : Fin N) :
      Circuit.rel B (Circuit.or
        (Circuit.and (b.head i) write)
        (Circuit.and (Circuit.not (b.head i)) (b.tape i))) ≤
        5 + 11 * S + 4 * S * N := by
    have h1 := Circuit.rel_or B
      (Circuit.and (b.head i) write)
      (Circuit.and (Circuit.not (b.head i)) (b.tape i))
    have hfirst0 : Circuit.rel B (Circuit.and (b.head i) write) ≤ 1 + Circuit.rel B write := by
      have hfirst := Circuit.rel_and B (b.head i) write
      rw [hhead i] at hfirst
      omega
    have hnot0 : Circuit.rel B (Circuit.not (b.head i)) ≤ 1 := by
      have hnot := Circuit.rel_not B (b.head i)
      rw [hhead i] at hnot
      omega
    have hsecond0 :
        Circuit.rel B (Circuit.and (Circuit.not (b.head i)) (b.tape i)) ≤ 2 := by
      have hsecond := Circuit.rel_and B (Circuit.not (b.head i)) (b.tape i)
      have ht0 := htape i
      omega
    omega
  have hfinalState (q : Fin M.numStates) :
      Circuit.rel B (Circuit.ite halted (b.state q)
        (Circuit.orMany (List.ofFn fun q' : Fin M.numStates =>
          Circuit.and (b.state q')
            (Circuit.ite scan
              (Circuit.const ((M.step q' true).1 == q))
              (Circuit.const ((M.step q' false).1 == q)))))) ≤
        8 + 11 * S + 4 * S * N := by
    have h := Circuit.rel_ite B halted (b.state q)
      (Circuit.orMany (List.ofFn fun q' : Fin M.numStates =>
        Circuit.and (b.state q')
          (Circuit.ite scan
            (Circuit.const ((M.step q' true).1 == q))
            (Circuit.const ((M.step q' false).1 == q)))))
    rw [hstate q] at h
    have hns := hnextState q
    omega
  have hfinalHead (i : Fin N) :
      Circuit.rel B (Circuit.ite halted (b.head i)
        (Circuit.orMany (List.ofFn fun j : Fin N =>
          Circuit.and (b.head j)
            (Circuit.ite dir
              (Circuit.const
                (if j.val < 2 * t then j.val + 1 == i.val else j.val == i.val))
              (Circuit.const
                (if 0 < j.val then i.val + 1 == j.val else j.val == i.val)))))) ≤
        8 + 11 * N + 22 * S * N + 8 * S * N ^ 2 := by
    have h := Circuit.rel_ite B halted (b.head i)
      (Circuit.orMany (List.ofFn fun j : Fin N =>
        Circuit.and (b.head j)
          (Circuit.ite dir
            (Circuit.const
              (if j.val < 2 * t then j.val + 1 == i.val else j.val == i.val))
            (Circuit.const
              (if 0 < j.val then i.val + 1 == j.val else j.val == i.val)))))
    rw [hhead i] at h
    have hnh := hnextHead i
    omega
  have hfinalTape (i : Fin N) :
      Circuit.rel B (Circuit.ite halted (b.tape i)
        (Circuit.or
          (Circuit.and (b.head i) write)
          (Circuit.and (Circuit.not (b.head i)) (b.tape i)))) ≤
        12 + 11 * S + 4 * S * N := by
    have h := Circuit.rel_ite B halted (b.tape i)
      (Circuit.or
        (Circuit.and (b.head i) write)
        (Circuit.and (Circuit.not (b.head i)) (b.tape i)))
    rw [htape i] at h
    have hnt := hnextTape i
    omega
  have hsum := SimBits.nodes_sdiff_le_sum b (stepBits M t b)
  have hstateSum :
      (∑ q : Fin M.numStates, (((stepBits M t b).state q).nodes \ B).card) ≤
        S * (8 + 11 * S + 4 * S * N) := by
    have h := sum_le_card_mul (Finset.univ : Finset (Fin M.numStates))
      (fun q => (((stepBits M t b).state q).nodes \ B).card)
      (8 + 11 * S + 4 * S * N) (by
        intro q hq
        dsimp [B, S, N]
        simpa [stepBits, S, N, B, halted, scan, Circuit.rel] using hfinalState q)
    simpa [S] using h
  have hheadSum :
      (∑ i : Fin (2 * t + 1), (((stepBits M t b).head i).nodes \ B).card) ≤
        N * (8 + 11 * N + 22 * S * N + 8 * S * N ^ 2) := by
    have h := sum_le_card_mul (Finset.univ : Finset (Fin (2 * t + 1)))
      (fun i => (((stepBits M t b).head i).nodes \ B).card)
      (8 + 11 * N + 22 * S * N + 8 * S * N ^ 2) (by
        intro i hi
        dsimp [B, N]
        simpa [stepBits, S, N, B, halted, scan, dir, Circuit.rel] using
          hfinalHead (show Fin N from i))
    simpa [N] using h
  have htapeSum :
      (∑ i : Fin (2 * t + 1), (((stepBits M t b).tape i).nodes \ B).card) ≤
        N * (12 + 11 * S + 4 * S * N) := by
    have h := sum_le_card_mul (Finset.univ : Finset (Fin (2 * t + 1)))
      (fun i => (((stepBits M t b).tape i).nodes \ B).card)
      (12 + 11 * S + 4 * S * N) (by
        intro i hi
        dsimp [B, N]
        simpa [stepBits, S, N, B, halted, scan, dir, write, Circuit.rel] using
          hfinalTape (show Fin N from i))
    simpa [N] using h
  change ((stepBits M t b).nodes \ b.nodes).card ≤
    S * (8 + 11 * S + 4 * S * N) +
      N * (8 + 11 * N + 22 * S * N + 8 * S * N ^ 2) +
        N * (12 + 11 * S + 4 * S * N)
  dsimp [B] at hsum hstateSum hheadSum htapeSum
  dsimp [S, N] at hstateSum hheadSum htapeSum hsum ⊢
  omega

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

theorem stepBitsCorrect (M : TM) (t : Nat) : StepBitsCorrect M t := by
  intro x c b hstate hhead htape
  dsimp
  by_cases hhalt : bhalt M c = true
  · have hhaltProp : c.state = M.accept ∨ c.state = M.reject := by
      simpa [bhalt] using hhalt
    have hhaltBits :
        (Circuit.or (b.state M.accept) (b.state M.reject)).eval x = true := by
      simp [hstate, hhaltProp]
    refine ⟨?_, ?_, ?_⟩
    · intro q
      simp [stepBits, hhaltBits, bnext, hhalt, hstate]
    · intro i
      simp [stepBits, hhaltBits, bnext, hhalt, hhead]
    · intro i
      simp [stepBits, hhaltBits, bnext, hhalt, htape]
  · have hhaltFalse : bhalt M c = false := by
      cases h : bhalt M c <;> simp_all
    have hhaltPropFalse : ¬ (c.state = M.accept ∨ c.state = M.reject) := by
      simpa [bhalt] using hhalt
    have hhaltSep : c.state ≠ M.accept ∧ c.state ≠ M.reject := by
      simpa using hhaltPropFalse
    have hhaltBits :
        (Circuit.or (b.state M.accept) (b.state M.reject)).eval x = false := by
      simp [hstate, hhaltSep]
    let scanCircuit : Circuit :=
      Circuit.orMany (List.ofFn fun i : Fin (2 * t + 1) =>
        Circuit.and (b.head i) (b.tape i))
    have hscan : scanCircuit.eval x = c.tape c.pos := by
      by_cases ha : c.tape c.pos = true
      · rw [ha]
        apply (Circuit.eval_orMany_eq_true_iff _ x).2
        refine ⟨Circuit.and (b.head c.pos) (b.tape c.pos), ?_, ?_⟩
        · rw [List.mem_ofFn]
          exact ⟨c.pos, rfl⟩
        · simp [hhead c.pos, htape c.pos, ha]
      · have haf : c.tape c.pos = false := by
          cases h : c.tape c.pos <;> simp_all
        rw [haf]
        apply (Circuit.eval_orMany_eq_false_iff _ x).2
        intro d hd
        rw [List.mem_ofFn] at hd
        rcases hd with ⟨i, rfl⟩
        by_cases hi : (c.pos == i) = true
        · have hiEq : c.pos = i := by simpa using hi
          subst i
          simp [hhead c.pos, htape c.pos, haf]
        · have hif : (c.pos == i) = false := by
            cases h : c.pos == i <;> simp_all
          simp [hif, hhead i]
    let dirCircuit : Circuit :=
      Circuit.orMany (List.ofFn fun q : Fin M.numStates =>
        Circuit.and (b.state q)
          (Circuit.ite scanCircuit
            (Circuit.const (M.step q true).2.2)
            (Circuit.const (M.step q false).2.2)))
    have hdir : dirCircuit.eval x = (M.step c.state (c.tape c.pos)).2.2 := by
      by_cases hd : (M.step c.state (c.tape c.pos)).2.2 = true
      · rw [hd]
        apply (Circuit.eval_orMany_eq_true_iff _ x).2
        refine ⟨Circuit.and (b.state c.state)
          (Circuit.ite scanCircuit
            (Circuit.const (M.step c.state true).2.2)
            (Circuit.const (M.step c.state false).2.2)), ?_, ?_⟩
        · rw [List.mem_ofFn]
          exact ⟨c.state, rfl⟩
        · simp only [Circuit.eval_and, Circuit.eval_ite, Circuit.eval_const, hstate c.state, hscan]
          by_cases ha : c.tape c.pos = true
          · simpa [ha] using hd
          · simpa [ha] using hd
      · have hdf : (M.step c.state (c.tape c.pos)).2.2 = false := by
          cases h : (M.step c.state (c.tape c.pos)).2.2 <;> simp_all
        rw [hdf]
        apply (Circuit.eval_orMany_eq_false_iff _ x).2
        intro d hdmem
        rw [List.mem_ofFn] at hdmem
        rcases hdmem with ⟨q, rfl⟩
        by_cases hq : (c.state == q) = true
        · have hqeq : c.state = q := by simpa using hq
          subst q
          simp only [Circuit.eval_and, Circuit.eval_ite, Circuit.eval_const, hstate c.state, hscan]
          by_cases ha : c.tape c.pos = true
          · simpa [ha] using hdf
          · simpa [ha] using hdf
        · have hqf : (c.state == q) = false := by
            cases h : c.state == q <;> simp_all
          simp [Circuit.eval_and, hstate q, hqf]
    let writeCircuit : Circuit :=
      Circuit.orMany (List.ofFn fun q : Fin M.numStates =>
        Circuit.and (b.state q)
          (Circuit.ite scanCircuit
            (Circuit.const (M.step q true).2.1)
            (Circuit.const (M.step q false).2.1)))
    have hwrite : writeCircuit.eval x = (M.step c.state (c.tape c.pos)).2.1 := by
      by_cases hw : (M.step c.state (c.tape c.pos)).2.1 = true
      · rw [hw]
        apply (Circuit.eval_orMany_eq_true_iff _ x).2
        refine ⟨Circuit.and (b.state c.state)
          (Circuit.ite scanCircuit
            (Circuit.const (M.step c.state true).2.1)
            (Circuit.const (M.step c.state false).2.1)), ?_, ?_⟩
        · rw [List.mem_ofFn]
          exact ⟨c.state, rfl⟩
        · simp only [Circuit.eval_and, Circuit.eval_ite, Circuit.eval_const, hstate c.state, hscan]
          by_cases ha : c.tape c.pos = true
          · simpa [ha] using hw
          · simpa [ha] using hw
      · have hwf : (M.step c.state (c.tape c.pos)).2.1 = false := by
          cases h : (M.step c.state (c.tape c.pos)).2.1 <;> simp_all
        rw [hwf]
        apply (Circuit.eval_orMany_eq_false_iff _ x).2
        intro d hdmem
        rw [List.mem_ofFn] at hdmem
        rcases hdmem with ⟨q, rfl⟩
        by_cases hq : (c.state == q) = true
        · have hqeq : c.state = q := by simpa using hq
          subst q
          simp only [Circuit.eval_and, Circuit.eval_ite, Circuit.eval_const, hstate c.state, hscan]
          by_cases ha : c.tape c.pos = true
          · simpa [ha] using hwf
          · simpa [ha] using hwf
        · have hqf : (c.state == q) = false := by
            cases h : c.state == q <;> simp_all
          simp [Circuit.eval_and, hstate q, hqf]
    refine ⟨?_, ?_, ?_⟩
    · intro q'
      have htarget :
          ((bnext M t c).state == q') =
            ((M.step c.state (c.tape c.pos)).1 == q') := by
        simp [bnext, hhaltFalse, bstep]
      rw [htarget]
      dsimp [stepBits]
      rw [Circuit.eval_ite, hhaltBits]
      change
        (Circuit.orMany (List.ofFn fun q : Fin M.numStates =>
          Circuit.and (b.state q)
            (Circuit.ite scanCircuit
              (Circuit.const ((M.step q true).1 == q'))
              (Circuit.const ((M.step q false).1 == q'))))).eval x =
          ((M.step c.state (c.tape c.pos)).1 == q')
      by_cases hq' : ((M.step c.state (c.tape c.pos)).1 == q') = true
      · rw [hq']
        apply (Circuit.eval_orMany_eq_true_iff _ x).2
        refine ⟨Circuit.and (b.state c.state)
          (Circuit.ite scanCircuit
            (Circuit.const ((M.step c.state true).1 == q'))
            (Circuit.const ((M.step c.state false).1 == q'))), ?_, ?_⟩
        · rw [List.mem_ofFn]
          exact ⟨c.state, rfl⟩
        · simp only [Circuit.eval_and, Circuit.eval_ite, Circuit.eval_const, hstate c.state, hscan]
          by_cases ha : c.tape c.pos = true
          · simpa [ha] using hq'
          · simpa [ha] using hq'
      · have hq'f : ((M.step c.state (c.tape c.pos)).1 == q') = false := by
          cases h : (M.step c.state (c.tape c.pos)).1 == q' <;> simp_all
        rw [hq'f]
        apply (Circuit.eval_orMany_eq_false_iff _ x).2
        intro d hdmem
        rw [List.mem_ofFn] at hdmem
        rcases hdmem with ⟨q, rfl⟩
        by_cases hq : (c.state == q) = true
        · have hqeq : c.state = q := by simpa using hq
          subst q
          simp only [Circuit.eval_and, Circuit.eval_ite, Circuit.eval_const, hstate c.state, hscan]
          by_cases ha : c.tape c.pos = true
          · simpa [ha] using hq'f
          · simpa [ha] using hq'f
        · have hqf : (c.state == q) = false := by
            cases h : c.state == q <;> simp_all
          simp [Circuit.eval_and, hstate q, hqf]
    · intro i
      have htarget :
          ((bnext M t c).pos == i) =
            if (M.step c.state (c.tape c.pos)).2.2 then
              if c.pos.val < 2 * t then c.pos.val + 1 == i.val else c.pos.val == i.val
            else
              if 0 < c.pos.val then i.val + 1 == c.pos.val else c.pos.val == i.val := by
        by_cases hdirv : (M.step c.state (c.tape c.pos)).2.2 = true
        · by_cases hb : c.pos.val < 2 * t
          · simp [bnext, hhaltFalse, bstep, hdirv, hb, Fin.ext_iff]
          · simp [bnext, hhaltFalse, bstep, hdirv, hb, Fin.ext_iff]
        · have hdirf : (M.step c.state (c.tape c.pos)).2.2 = false := by
            cases h : (M.step c.state (c.tape c.pos)).2.2 <;> simp_all
          by_cases hb : 0 < c.pos.val
          · simp [bnext, hhaltFalse, bstep, hdirf, hb, Fin.ext_iff]
            omega
          · simp [bnext, hhaltFalse, bstep, hdirf, hb, Fin.ext_iff]
      rw [htarget]
      dsimp [stepBits]
      rw [Circuit.eval_ite, hhaltBits]
      change
        (Circuit.orMany (List.ofFn fun j : Fin (2 * t + 1) =>
          Circuit.and (b.head j)
            (Circuit.ite dirCircuit
              (Circuit.const
                (if j.val < 2 * t then j.val + 1 == i.val else j.val == i.val))
              (Circuit.const
                (if 0 < j.val then i.val + 1 == j.val else j.val == i.val))))).eval x =
          (if (M.step c.state (c.tape c.pos)).2.2 then
            if c.pos.val < 2 * t then c.pos.val + 1 == i.val else c.pos.val == i.val
          else
            if 0 < c.pos.val then i.val + 1 == c.pos.val else c.pos.val == i.val)
      by_cases hi : (if (M.step c.state (c.tape c.pos)).2.2 then
              if c.pos.val < 2 * t then c.pos.val + 1 == i.val else c.pos.val == i.val
            else
              if 0 < c.pos.val then i.val + 1 == c.pos.val else c.pos.val == i.val) = true
      · rw [hi]
        apply (Circuit.eval_orMany_eq_true_iff _ x).2
        refine ⟨Circuit.and (b.head c.pos)
          (Circuit.ite dirCircuit
            (Circuit.const
              (if c.pos.val < 2 * t then c.pos.val + 1 == i.val else c.pos.val == i.val))
            (Circuit.const
              (if 0 < c.pos.val then i.val + 1 == c.pos.val else c.pos.val == i.val))), ?_, ?_⟩
        · rw [List.mem_ofFn]
          exact ⟨c.pos, rfl⟩
        · simp only [Circuit.eval_and, Circuit.eval_ite, Circuit.eval_const, hhead c.pos, hdir]
          have hself : (c.pos == c.pos) = true := by simp
          simpa [hself] using hi
      · have hif : (if (M.step c.state (c.tape c.pos)).2.2 then
              if c.pos.val < 2 * t then c.pos.val + 1 == i.val else c.pos.val == i.val
            else
              if 0 < c.pos.val then i.val + 1 == c.pos.val else c.pos.val == i.val) = false := by
          cases h : (if (M.step c.state (c.tape c.pos)).2.2 then
              if c.pos.val < 2 * t then c.pos.val + 1 == i.val else c.pos.val == i.val
            else
              if 0 < c.pos.val then i.val + 1 == c.pos.val else c.pos.val == i.val) <;> simp_all
        rw [hif]
        apply (Circuit.eval_orMany_eq_false_iff _ x).2
        intro d hdmem
        rw [List.mem_ofFn] at hdmem
        rcases hdmem with ⟨j, rfl⟩
        by_cases hj : (c.pos == j) = true
        · have hjEq : c.pos = j := by simpa using hj
          subst j
          simp only [Circuit.eval_and, Circuit.eval_ite, Circuit.eval_const, hhead c.pos, hdir]
          have hself : (c.pos == c.pos) = true := by simp
          simpa [hself] using hif
        · have hjf : (c.pos == j) = false := by
            cases h : c.pos == j <;> simp_all
          simp [Circuit.eval_and, hjf, hhead j]
    · intro i
      have htarget :
          (bnext M t c).tape i =
            if i.val == c.pos.val then (M.step c.state (c.tape c.pos)).2.1
            else c.tape i := by
        simp [bnext, hhaltFalse, bstep]
      rw [htarget]
      dsimp [stepBits]
      rw [Circuit.eval_ite, hhaltBits]
      change
        (Circuit.or (Circuit.and (b.head i) writeCircuit)
          (Circuit.and (Circuit.not (b.head i)) (b.tape i))).eval x =
          (if i.val == c.pos.val then (M.step c.state (c.tape c.pos)).2.1 else c.tape i)
      by_cases hi : (i.val == c.pos.val) = true
      · have hiEq : i = c.pos := by
          apply Fin.ext
          simpa using hi
        subst i
        simp only [Circuit.eval_or, Circuit.eval_and, Circuit.eval_not, hhead c.pos, hwrite]
        simp
      · have hif : (i.val == c.pos.val) = false := by
          cases h : i.val == c.pos.val <;> simp_all
        have hposi : (c.pos == i) = false := by
          cases h : c.pos == i <;> simp_all
        simp [hposi, hhead i, htape i, hif]

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

/-- Circuit bits for a bounded configuration whose first `x.length` symbols
    are hardcoded to `x` and whose next `m` symbols are free certificate bits. -/
def npInitBits (M : TM) (t m : Nat) (x : Word) : SimBits M.numStates (2 * t + 1) where
  state q := Circuit.const (M.start == q)
  head i := Circuit.const (i.val == t)
  tape i :=
    if t ≤ i.val ∧ i.val < t + x.length then
      Circuit.const (x.getD (i.val - t) false)
    else if t + x.length ≤ i.val ∧ i.val < t + x.length + m then
      Circuit.var (i.val - (t + x.length))
    else
      Circuit.const false

lemma npInitBits_correct (V : TM) (t m : Nat) (x y : Word) (hy : y.length ≤ m) :
    let b := npInitBits V t m x
    let c := binit V t (x ++ y)
    (∀ q : Fin V.numStates, (b.state q).eval y = (c.state == q)) ∧
      (∀ i : Fin (2 * t + 1), (b.head i).eval y = (c.pos == i)) ∧
        (∀ i : Fin (2 * t + 1), (b.tape i).eval y = c.tape i) := by
  dsimp [npInitBits, binit]
  simp only [List.length_append] at *
  constructor
  · intro q
    simp
  constructor
  · intro i
    simp [Fin.ext_iff]
    omega
  · intro i
    by_cases h1 : t ≤ i.val ∧ i.val < t + x.length
    · rw [ite_eq_left h1]
      have hj : i.val - t < x.length := by omega
      have hb : t ≤ i.val ∧ i.val < t + (x.length + y.length) := by omega
      rw [ite_eq_left hb]
      rw [List.getD_append x y false (i.val - t) hj]
      simp
    · rw [ite_eq_right h1]
      by_cases h2 : t + x.length ≤ i.val ∧ i.val < t + x.length + m
      · rw [ite_eq_left h2]
        by_cases hb : t ≤ i.val ∧ i.val < t + (x.length + y.length)
        · rw [ite_eq_left hb]
          rw [List.getD_append_right x y false (i.val - t) (by omega)]
          change y.getD (i.val - (t + x.length)) false =
            y.getD ((i.val - t) - x.length) false
          congr 1
          omega
        · rw [ite_eq_right hb]
          have hge' : y.length ≤ i.val - (t + x.length) := by omega
          change y.getD (i.val - (t + x.length)) false = false
          rw [List.getD_eq_default (l := y) (d := false) hge']
      · rw [ite_eq_right h2]
        by_cases hb : t ≤ i.val ∧ i.val < t + (x.length + y.length)
        · exfalso
          omega
        · rw [ite_eq_right hb]
          simp

/-- Unroll `s` transitions from an arbitrary initial bit vector. -/
def unrollBitsFrom (M : TM) (t : Nat) (b0 : SimBits M.numStates (2 * t + 1)) :
    Nat → SimBits M.numStates (2 * t + 1)
  | 0 => b0
  | s + 1 => stepBits M t (unrollBitsFrom M t b0 s)

lemma unrollBitsFrom_correct (V : TM) (t m s : Nat) (x y : Word) (hy : y.length ≤ m) :
    let b := unrollBitsFrom V t (npInitBits V t m x) s
    let c := brun V t s (binit V t (x ++ y))
    (∀ q : Fin V.numStates, (b.state q).eval y = (c.state == q)) ∧
      (∀ i : Fin (2 * t + 1), (b.head i).eval y = (c.pos == i)) ∧
        (∀ i : Fin (2 * t + 1), (b.tape i).eval y = c.tape i) := by
  induction s with
  | zero =>
      exact npInitBits_correct V t m x y hy
  | succ s ih =>
      dsimp at ih
      dsimp [unrollBitsFrom, brun]
      exact stepBitsCorrect V t y (brun V t s (binit V t (x ++ y)))
        (unrollBitsFrom V t (npInitBits V t m x) s) ih.1 ih.2.1 ih.2.2

/-- The polynomial-size verifier circuit: it simulates `V` on `x ++ y` with
    `x` hardcoded and `y` left as free input bits. -/
def npVerifierCircuit (V : TM) (p q : TimeBound) (x : Word) : Circuit :=
  let m := q.eval x.length
  let t := p.eval (x.length + m)
  (unrollBitsFrom V t (npInitBits V t m x) t).state V.accept

lemma npVerifierCircuit_eval_eq_acceptsIn (V : TM) (p q : TimeBound)
    (x y : Word) (hy : y.length ≤ q.eval x.length) :
    (npVerifierCircuit V p q x).eval y =
      acceptsIn V (x ++ y) (p.eval (x.length + q.eval x.length)) := by
  let m := q.eval x.length
  let t := p.eval (x.length + m)
  have hc := unrollBitsFrom_correct V t m t x y (by simpa [m] using hy)
  dsimp [npVerifierCircuit, t, m]
  rw [hc.1 V.accept]
  simpa [bacceptsIn, Nat.add_assoc] using (bacceptsIn_eq_acceptsIn V t (x ++ y))

lemma npInitBits_boundedVars (M : TM) (t m : Nat) (x : Word) :
    (npInitBits M t m x).BoundedVars (m - 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    simp [npInitBits, Circuit.maxVar]
  · intro i
    simp [npInitBits, Circuit.maxVar]
  · intro i
    dsimp [npInitBits]
    by_cases h1 : t ≤ i.val ∧ i.val < t + x.length
    · rw [ite_eq_left h1]
      simp [Circuit.maxVar]
    · rw [ite_eq_right h1]
      by_cases h2 : t + x.length ≤ i.val ∧ i.val < t + x.length + m
      · rw [ite_eq_left h2]
        have hle : i.val - (t + x.length) ≤ m - 1 := by omega
        simpa [Circuit.maxVar] using hle
      · rw [ite_eq_right h2]
        simp [Circuit.maxVar]

lemma unrollBitsFrom_boundedVars (V : TM) (t m s : Nat) (x : Word) :
    (unrollBitsFrom V t (npInitBits V t m x) s).BoundedVars (m - 1) := by
  induction s with
  | zero => exact npInitBits_boundedVars V t m x
  | succ s ih =>
      dsimp [unrollBitsFrom]
      exact stepBits_boundedVars V t _ (m - 1) ih

lemma npInitBits_varsBounded (M : TM) (t m : Nat) (x : Word) :
    (npInitBits M t m x).VarsBounded m := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    simp [npInitBits, Circuit.vars]
  · intro i
    simp [npInitBits, Circuit.vars]
  · intro i
    dsimp [npInitBits]
    by_cases h1 : t ≤ i.val ∧ i.val < t + x.length
    · rw [ite_eq_left h1]
      simp [Circuit.vars]
    · rw [ite_eq_right h1]
      by_cases h2 : t + x.length ≤ i.val ∧ i.val < t + x.length + m
      · rw [ite_eq_left h2]
        intro j hj
        simp only [Circuit.vars, Finset.mem_singleton] at hj
        subst j
        simp only [Finset.mem_range]
        omega
      · rw [ite_eq_right h2]
        simp [Circuit.vars]

lemma unrollBitsFrom_varsBounded (V : TM) (t m s : Nat) (x : Word) :
    (unrollBitsFrom V t (npInitBits V t m x) s).VarsBounded m := by
  induction s with
  | zero => exact npInitBits_varsBounded V t m x
  | succ s ih =>
      dsimp [unrollBitsFrom]
      exact stepBits_varsBounded V t _ m ih

lemma npVerifierCircuit_vars_subset (V : TM) (p q : TimeBound) (x : Word) :
    (npVerifierCircuit V p q x).vars ⊆ Finset.range (q.eval x.length) := by
  let m := q.eval x.length
  let t := p.eval (x.length + m)
  have hb := unrollBitsFrom_varsBounded V t m t x
  dsimp [npVerifierCircuit, t, m]
  exact hb.1 V.accept

/-- One output bit of the polynomial-time transducer, represented as a
    circuit on the original input.  Bits beyond the fixed output length are
    constantly false. -/
def reductionBits (M : TM) (p : TimeBound) (n : Nat) : Nat → Circuit :=
  fun i =>
    if h : i < p.eval n + 1 then
      (unrollBits M (p.eval n) n (p.eval n)).tape ⟨p.eval n + i, by
        have hi : i < p.eval n + 1 := h
        omega⟩
    else
      Circuit.const false

lemma reductionBits_of_not_lt (M : TM) (p : TimeBound) (n i : Nat)
    (hi : ¬ i < p.eval n + 1) :
    reductionBits M p n i = Circuit.const false := by
  simp [reductionBits, hi]

lemma reductionBits_eval (M : TM) (p : TimeBound) (x : Word) (i : Nat)
    (hi : i < p.eval x.length + 1) :
    (reductionBits M p x.length i).eval x =
      (boutputIn M (p.eval x.length) x).getD i false := by
  dsimp [reductionBits]
  rw [dite_eq_left hi]
  have hc := (unrollBits_correct M (p.eval x.length)
    (stepBitsCorrect M (p.eval x.length)) x (p.eval x.length)).2.2
  have hbit := hc ⟨p.eval x.length + i, by omega⟩
  rw [boutputIn_getD M (p.eval x.length) x i hi]
  exact hbit

/-- The bounded simulation agrees with the original TM for clocked runs. -/
def BRunsLikeTM : Prop :=
  ∀ (M : TM) (p : TimeBound),
    (∀ x : Word, halted M (run M (p.eval x.length) (init M x)) = true) →
      ∀ x : Word,
        bacceptsIn M (p.eval x.length) (p.eval x.length) x =
          acceptsIn M x (p.eval x.length)

/-- The bounded run agrees with the original machine: after `t` steps the
    window still contains the whole visited tape region, so the two acceptance
    tests coincide. -/
theorem brunsLikeTM : BRunsLikeTM := by
  intro M p hhalt x
  exact bacceptsIn_eq_acceptsIn M (p.eval x.length) x

/-- Polynomial bound for the initial bounded configuration. -/
noncomputable def initPoly (M : TM) (p : TimeBound) : TimeBound :=
  C (M.numStates + 2) + C 4 * p

/-- Polynomial bound for the new nodes introduced by one transition. -/
noncomputable def stepPoly (M : TM) : TimeBound :=
  let S := M.numStates
  let N : TimeBound := C 2 * X + C 1
  C S * (C 8 + C (11 * S) + C (4 * S) * N) +
    N * (C 8 + C 11 * N + C (22 * S) * N + C (8 * S) * N ^ 2) +
      N * (C 12 + C (11 * S) + C (4 * S) * N)

/-- Total polynomial bound for the unrolled accept circuit. -/
noncomputable def unrollPoly (M : TM) (p : TimeBound) : TimeBound :=
  initPoly M p + p * (stepPoly M).comp p

lemma initBits_size_bound (M : TM) (p : TimeBound) (n : Nat) :
    (initBits M (p.eval n) n).size ≤ (initPoly M p).eval n := by
  have hnodes := SimBits.nodes_le_sum_size (initBits M (p.eval n) n)
  have hstate :
      (∑ q : Fin M.numStates, ((initBits M (p.eval n) n).state q).size) ≤
        M.numStates := by
    have h := sum_le_card_mul (Finset.univ : Finset (Fin M.numStates))
      (fun q => ((initBits M (p.eval n) n).state q).size) 1 (by
        intro q hq
        simp [initBits])
    simpa using h
  have hhead :
      (∑ i : Fin (2 * p.eval n + 1), ((initBits M (p.eval n) n).head i).size) ≤
        2 * p.eval n + 1 := by
    have h := sum_le_card_mul (Finset.univ : Finset (Fin (2 * p.eval n + 1)))
      (fun i => ((initBits M (p.eval n) n).head i).size) 1 (by
        intro i hi
        simp [initBits])
    simpa using h
  have htape :
      (∑ i : Fin (2 * p.eval n + 1), ((initBits M (p.eval n) n).tape i).size) ≤
        2 * p.eval n + 1 := by
    have h := sum_le_card_mul (Finset.univ : Finset (Fin (2 * p.eval n + 1)))
      (fun i => ((initBits M (p.eval n) n).tape i).size) 1 (by
        intro i hi
        by_cases h : p.eval n ≤ i.val ∧ i.val < p.eval n + n <;>
          simp [initBits, h])
    simpa using h
  have htotal :
      (initBits M (p.eval n) n).size ≤
        M.numStates + 2 * (2 * p.eval n + 1) := by
    omega
  simp [initPoly]
  omega

lemma stepBits_size_bound (M : TM) (t : Nat)
    (b : SimBits M.numStates (2 * t + 1)) :
    (stepBits M t b).size ≤ b.size + stepRelBound M t := by
  have h := SimBits.size_le_add_rel b (stepBits M t b)
  have hs := step_rel_bound M t b
  omega

lemma stepRelBound_le_stepPoly (M : TM) (t : Nat) :
    stepRelBound M t ≤ (stepPoly M).eval t := by
  simp [stepRelBound, stepPoly]

lemma unrollBits_size_bound (M : TM) (p : TimeBound) (n s : Nat) :
    (unrollBits M (p.eval n) n s).size ≤
      (initPoly M p).eval n + s * (stepPoly M).eval (p.eval n) := by
  induction s with
  | zero =>
      dsimp [unrollBits]
      have h := initBits_size_bound M p n
      simpa using h
  | succ s ih =>
      dsimp [unrollBits]
      have hstep := stepBits_size_bound M (p.eval n) (unrollBits M (p.eval n) n s)
      have hpoly := stepRelBound_le_stepPoly M (p.eval n)
      have hsucc : (s + 1) * (stepPoly M).eval (p.eval n) =
          s * (stepPoly M).eval (p.eval n) + (stepPoly M).eval (p.eval n) := by
        simp [Nat.succ_mul]
      rw [hsucc]
      omega

lemma reductionBits_size_le (M : TM) (p : TimeBound) (n i : Nat) :
    (reductionBits M p n i).size ≤ (unrollPoly M p).eval n + 1 := by
  by_cases hi : i < p.eval n + 1
  · have hbit := SimBits.tape_size_le (unrollBits M (p.eval n) n (p.eval n))
      (⟨p.eval n + i, by omega⟩ : Fin (2 * p.eval n + 1))
    have hb := unrollBits_size_bound M p n (p.eval n)
    have hb' : (unrollBits M (p.eval n) n (p.eval n)).size ≤
        (unrollPoly M p).eval n := by
      have hb0 := hb
      simp [initPoly] at hb0
      simpa [unrollPoly, initPoly] using hb0
    dsimp [reductionBits]
    rw [dite_eq_left hi]
    omega
  · rw [reductionBits_of_not_lt M p n i hi]
    simp

/-- The size obligation for the unrolled accept circuit, now discharged using
    the sharing-aware circuit-size measure. -/
def UnrollPolySize : Prop :=
  ∀ (M : TM) (p : TimeBound),
    ∃ P : TimeBound, ∀ n : Nat,
      (acceptCircuit M (p.eval n) (unrollBits M (p.eval n) n (p.eval n))).size ≤ P.eval n

theorem unrollPolySize : UnrollPolySize := by
  intro M p
  refine ⟨unrollPoly M p, ?_⟩
  intro n
  dsimp [acceptCircuit]
  have hacc :
      ((unrollBits M (p.eval n) n (p.eval n)).state M.accept).size ≤
        (unrollBits M (p.eval n) n (p.eval n)).size :=
    SimBits.state_size_le _ M.accept
  have hb := unrollBits_size_bound M p n (p.eval n)
  simp [initPoly] at hb
  simp [unrollPoly, initPoly]
  omega

/-- Assembling the bounded obligations gives the original compilation lemma. -/
theorem bounded_unroll_implies_TMCompiles
    (hsize : UnrollPolySize) : TMCompilesToPolyCircuits := by
  intro M p hhalt
  let F : CircuitFamily := fun n =>
    acceptCircuit M (p.eval n) (unrollBits M (p.eval n) n (p.eval n))
  refine ⟨F, hsize M p, ?_⟩
  intro x
  dsimp [F, acceptCircuit]
  have hc := unrollBits_correct M (p.eval x.length)
    (stepBitsCorrect M (p.eval x.length)) x (p.eval x.length)
  dsimp at hc
  rw [hc.1 M.accept]
  exact brunsLikeTM M p hhalt x

/-- The compilation lemma is now unconditional. -/
theorem tmCompilesToPolyCircuits : TMCompilesToPolyCircuits :=
  bounded_unroll_implies_TMCompiles unrollPolySize

/-- Consequently P is contained in P/poly without any extra assumption. -/
theorem P_subset_PPoly_unconditional : ∀ L : Language, InP L → InPPoly L :=
  P_subset_PPoly tmCompilesToPolyCircuits

/-- The 3b route, with only the concrete lower-bound hypothesis left open. -/
theorem NPNotInPPoly_implies_not_PEqualsNP : NPNotInPPoly → ¬ PEqualsNP :=
  NP_not_in_PPoly_implies_not_PEqualsNP tmCompilesToPolyCircuits

-- -----------------------------------------------------------------------------
-- 10. A concrete lower-bound target: SAT
-- -----------------------------------------------------------------------------

/-- Propositional formulas over numbered variables. -/
inductive Formula where
  | var (i : Nat)
  | not (f : Formula)
  | and (f g : Formula)
  | or (f g : Formula)
  deriving Repr, DecidableEq

namespace Formula

/-- Boolean evaluation of a formula under a total assignment. -/
def eval : Formula → (Nat → Bool) → Bool
  | var i, a => a i
  | not f, a => Bool.not (f.eval a)
  | and f g, a => Bool.and (f.eval a) (g.eval a)
  | or f g, a => Bool.or (f.eval a) (g.eval a)

@[simp] lemma eval_var (i : Nat) (a : Nat → Bool) : (var i).eval a = a i := rfl
@[simp] lemma eval_not (f : Formula) (a : Nat → Bool) : (not f).eval a = !(f.eval a) := rfl
@[simp] lemma eval_and (f g : Formula) (a : Nat → Bool) :
    (and f g).eval a = (f.eval a && g.eval a) := rfl
@[simp] lemma eval_or (f g : Formula) (a : Nat → Bool) :
    (or f g).eval a = (f.eval a || g.eval a) := rfl

/-- Constant-true and constant-false formulas, built from variable `0`. -/
def trueFormula : Formula := or (var 0) (not (var 0))
def falseFormula : Formula := and (var 0) (not (var 0))

@[simp] lemma eval_trueFormula (a : Nat → Bool) : trueFormula.eval a = true := by
  cases h : a 0 <;> simp [trueFormula, eval, h]
@[simp] lemma eval_falseFormula (a : Nat → Bool) : falseFormula.eval a = false := by
  cases h : a 0 <;> simp [falseFormula, eval, h]

/-- Direct tree expansion of a circuit into a formula.  This preserves
    evaluation but can blow up in size, so it is not yet the Tseitin
    translation needed for a polynomial Cook–Levin reduction. -/
def ofCircuit : Circuit → Formula
  | Circuit.const b => if b then trueFormula else falseFormula
  | Circuit.var i => var i
  | Circuit.not c => not (ofCircuit c)
  | Circuit.and c₁ c₂ => and (ofCircuit c₁) (ofCircuit c₂)
  | Circuit.or c₁ c₂ => or (ofCircuit c₁) (ofCircuit c₂)

lemma ofCircuit_eval (c : Circuit) (x : Word) :
    (ofCircuit c).eval (fun i => x.getD i false) = c.eval x := by
  induction c with
  | const b => cases b <;> simp [ofCircuit]
  | var i => simp [ofCircuit, Circuit.eval]
  | not c ih =>
      dsimp [ofCircuit, Circuit.eval]
      rw [ih]
  | and c₁ c₂ ih1 ih2 =>
      dsimp [ofCircuit, Circuit.eval]
      rw [ih1, ih2]
  | or c₁ c₂ ih1 ih2 =>
      dsimp [ofCircuit, Circuit.eval]
      rw [ih1, ih2]

/-- A simple injective encoding of natural numbers as Boolean words. -/
def encodeNat (n : Nat) : Word := List.replicate n true ++ [false]

lemma encodeNat_length (n : Nat) : (encodeNat n).length = n + 1 := by
  simp [encodeNat]

lemma encodeNat_injective : Function.Injective encodeNat := by
  intro m n h
  have hlen := congrArg List.length h
  simp [encodeNat] at hlen
  omega

/-- Unary-number encodings cannot be split differently. -/
lemma encodeNat_append_cancel (i j : Nat) (a b : Word)
    (h : encodeNat i ++ a = encodeNat j ++ b) : i = j ∧ a = b := by
  induction i generalizing j a b with
  | zero =>
      cases j with
      | zero =>
          simp [encodeNat] at h
          exact ⟨rfl, h⟩
      | succ j =>
          simp [encodeNat, List.replicate_succ] at h
  | succ i ih =>
      cases j with
      | zero =>
          simp [encodeNat, List.replicate_succ] at h
      | succ j =>
          simp [encodeNat, List.replicate_succ] at h
          have h' : encodeNat i ++ a = encodeNat j ++ b := by
            simpa [encodeNat] using h
          have hij : i = j := (ih j a b h').1
          have hab : a = b := (ih j a b h').2
          exact ⟨by omega, hab⟩

/-- A prefix encoding of formulas as Boolean words. -/
def encode : Formula → Word
  | var i => [false, false] ++ encodeNat i
  | not f => [false, true] ++ f.encode
  | and f g => [true, false] ++ f.encode ++ g.encode
  | or f g => [true, true] ++ f.encode ++ g.encode

/-- Each constructor is a fixed-tag prepend on encoded inputs. -/
lemma encode_var_eq (i : Nat) : (var i).encode = [false, false] ++ encodeNat i := rfl
lemma encode_not_eq (f : Formula) : (not f).encode = [false, true] ++ f.encode := rfl
lemma encode_and_eq (f g : Formula) :
    (and f g).encode = [true, false] ++ f.encode ++ g.encode := rfl
lemma encode_or_eq (f g : Formula) :
    (or f g).encode = [true, true] ++ f.encode ++ g.encode := rfl

/-- A concrete transducer computes the encoding of the variable whose index is
    the input length. -/
theorem dPolyTimeComputable_var_encoding :
    DPolyTimeComputable (fun x => (var x.length).encode) := by
  simpa [encode_var_eq, encodeNat] using PNP.dPolyTimeComputable_var_encoding_length

/-- The unary connective is a fixed-tag prepend. -/
theorem dPolyTimeComputable_not_encoding :
    DPolyTimeComputable (fun z => ([false, true] : Word) ++ z) := by
  simpa using PNP.dPolyTimeComputable_prepend ([false, true] : Word)

lemma not_encoding_correct (f : Formula) :
    ([false, true] : Word) ++ f.encode = (not f).encode := by
  simp [encode_not_eq]

/-- The binary connectives prepend a fixed tag to the concatenation of the two
    encoded subformulas.  Thus the pair format is simply `f.encode ++ g.encode`. -/
theorem dPolyTimeComputable_and_encoding :
    DPolyTimeComputable (fun z => ([true, false] : Word) ++ z) := by
  simpa using PNP.dPolyTimeComputable_prepend ([true, false] : Word)

lemma and_encoding_correct (f g : Formula) :
    ([true, false] : Word) ++ (f.encode ++ g.encode) = (and f g).encode := by
  simp [encode_and_eq]

theorem dPolyTimeComputable_or_encoding :
    DPolyTimeComputable (fun z => ([true, true] : Word) ++ z) := by
  simpa using PNP.dPolyTimeComputable_prepend ([true, true] : Word)

lemma or_encoding_correct (f g : Formula) :
    ([true, true] : Word) ++ (f.encode ++ g.encode) = (or f g).encode := by
  simp [encode_or_eq]

/-- Unique splitting of formula encodings, by strong induction on the total
    encoded length of the two formulas and two suffixes.  This proves that the
    prefix encoding above is injective and uniquely decodable. -/
lemma encode_append_cancel_aux : ∀ n : Nat, ∀ f f' : Formula, ∀ a b : Word,
    f.encode.length + a.length + f'.encode.length + b.length = n →
    f.encode ++ a = f'.encode ++ b → f = f' ∧ a = b := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
      intro f f' a b hmeasure h
      cases f with
      | var i =>
          cases f' with
          | var j =>
              simp [encode] at h
              rcases encodeNat_append_cancel i j a b h with ⟨hij, hab⟩
              exact ⟨by simp [hij], hab⟩
          | not f1 => simp [encode] at h
          | and f1 f2 => simp [encode] at h
          | or f1 f2 => simp [encode] at h
      | not f1 =>
          cases f' with
          | var j => simp [encode] at h
          | not f2 =>
              simp [encode] at h
              have hm : f1.encode.length + a.length + f2.encode.length + b.length < n := by
                simp [encode] at hmeasure
                omega
              have hres := ih (f1.encode.length + a.length + f2.encode.length + b.length) hm
                f1 f2 a b rfl h
              exact ⟨by simp [hres.1], hres.2⟩
          | and f1' f2' => simp [encode] at h
          | or f1' f2' => simp [encode] at h
      | and f1 f2 =>
          cases f' with
          | var j => simp [encode] at h
          | not f1' => simp [encode] at h
          | and f1' f2' =>
              simp [encode] at h
              have htail : f1.encode ++ (f2.encode ++ a) =
                  f1'.encode ++ (f2'.encode ++ b) := by
                simpa [List.append_assoc] using h
              have hm1 : f1.encode.length + (f2.encode ++ a).length +
                  f1'.encode.length + (f2'.encode ++ b).length < n := by
                simp [encode] at hmeasure
                simp
                omega
              have h1 := ih (f1.encode.length + (f2.encode ++ a).length +
                  f1'.encode.length + (f2'.encode ++ b).length) hm1
                f1 f1' (f2.encode ++ a) (f2'.encode ++ b) rfl htail
              have htail2 : f2.encode ++ a = f2'.encode ++ b := h1.2
              have hm2 : f2.encode.length + a.length + f2'.encode.length + b.length < n := by
                simp [encode] at hmeasure
                omega
              have h2 := ih (f2.encode.length + a.length + f2'.encode.length + b.length) hm2
                f2 f2' a b rfl htail2
              exact ⟨by simp [h1.1, h2.1], h2.2⟩
          | or f1' f2' => simp [encode] at h
      | or f1 f2 =>
          cases f' with
          | var j => simp [encode] at h
          | not f1' => simp [encode] at h
          | and f1' f2' => simp [encode] at h
          | or f1' f2' =>
              simp [encode] at h
              have htail : f1.encode ++ (f2.encode ++ a) =
                  f1'.encode ++ (f2'.encode ++ b) := by
                simpa [List.append_assoc] using h
              have hm1 : f1.encode.length + (f2.encode ++ a).length +
                  f1'.encode.length + (f2'.encode ++ b).length < n := by
                simp [encode] at hmeasure
                simp
                omega
              have h1 := ih (f1.encode.length + (f2.encode ++ a).length +
                  f1'.encode.length + (f2'.encode ++ b).length) hm1
                f1 f1' (f2.encode ++ a) (f2'.encode ++ b) rfl htail
              have htail2 : f2.encode ++ a = f2'.encode ++ b := h1.2
              have hm2 : f2.encode.length + a.length + f2'.encode.length + b.length < n := by
                simp [encode] at hmeasure
                omega
              have h2 := ih (f2.encode.length + a.length + f2'.encode.length + b.length) hm2
                f2 f2' a b rfl htail2
              exact ⟨by simp [h1.1, h2.1], h2.2⟩

lemma encode_injective : Function.Injective encode := by
  intro f g h
  have h' : f.encode ++ ([] : Word) = g.encode ++ ([] : Word) := by simpa using h
  exact (encode_append_cancel_aux
    (f.encode.length + ([] : Word).length + g.encode.length + ([] : Word).length)
    f g [] [] rfl h').1

/-- Parse the unary-encoded variable index at the start of a word. -/
def parseNat : Word → Option (Nat × Word)
  | false :: rest => some (0, rest)
  | true :: rest =>
      match parseNat rest with
      | some (n, rest') => some (n + 1, rest')
      | none => none
  | [] => none

lemma parseNat_encodeNat (n : Nat) (w : Word) :
    parseNat (encodeNat n ++ w) = some (n, w) := by
  induction n with
  | zero => simp [parseNat, encodeNat]
  | succ n ih =>
      change parseNat (true :: (encodeNat n ++ w)) = some (n + 1, w)
      simp [parseNat, ih]

/-- A fueled prefix parser for formulas.  The fuel bounds recursive descent by
    the length of the word being parsed. -/
def parseFuel : Nat → Word → Option (Formula × Word)
  | 0, _ => none
  | _ + 1, false :: false :: rest =>
      match parseNat rest with
      | some (i, rest') => some (var i, rest')
      | none => none
  | n + 1, false :: true :: rest =>
      match parseFuel n rest with
      | some (f, rest') => some (not f, rest')
      | none => none
  | n + 1, true :: false :: rest =>
      match parseFuel n rest with
      | some (f, rest') =>
          match parseFuel n rest' with
          | some (g, rest'') => some (and f g, rest'')
          | none => none
      | none => none
  | n + 1, true :: true :: rest =>
      match parseFuel n rest with
      | some (f, rest') =>
          match parseFuel n rest' with
          | some (g, rest'') => some (or f g, rest'')
          | none => none
      | none => none
  | _ + 1, _ => none

/-- The un fueled parser uses the word length as fuel. -/
def parse (z : Word) : Option (Formula × Word) := parseFuel z.length z

lemma parseFuel_encode : ∀ (f : Formula) (n : Nat) (w : Word),
    f.encode.length ≤ n → parseFuel n (f.encode ++ w) = some (f, w) := by
  intro f
  induction f with
  | var i =>
      intro n w hn
      cases n with
      | zero =>
          simp [encode, encodeNat] at hn
      | succ n =>
          change (match parseNat (encodeNat i ++ w) with
            | some (i', rest') => some (var i', rest')
            | none => none) = some (var i, w)
          rw [parseNat_encodeNat]
  | not f ih =>
      intro n w hn
      cases n with
      | zero =>
          simp [encode] at hn
      | succ n =>
          change (match parseFuel n (f.encode ++ w) with
            | some (f', rest') => some (not f', rest')
            | none => none) = some (not f, w)
          rw [ih n w (by simp [encode] at hn; omega)]
  | and f g ihf ihg =>
      intro n w hn
      cases n with
      | zero =>
          simp [encode] at hn
      | succ n =>
          have hf : f.encode.length ≤ n := by
            simp [encode] at hn
            omega
          have hg : g.encode.length ≤ n := by
            simp [encode] at hn
            omega
          dsimp [encode]
          change (match parseFuel n (f.encode ++ g.encode ++ w) with
            | some (f', rest') =>
                match parseFuel n rest' with
                | some (g', rest'') => some (and f' g', rest'')
                | none => none
            | none => none) = some (and f g, w)
          rw [List.append_assoc f.encode g.encode w]
          rw [ihf n (g.encode ++ w) hf]
          simp
          rw [ihg n w hg]
  | or f g ihf ihg =>
      intro n w hn
      cases n with
      | zero =>
          simp [encode] at hn
      | succ n =>
          have hf : f.encode.length ≤ n := by
            simp [encode] at hn
            omega
          have hg : g.encode.length ≤ n := by
            simp [encode] at hn
            omega
          dsimp [encode]
          change (match parseFuel n (f.encode ++ g.encode ++ w) with
            | some (f', rest') =>
                match parseFuel n rest' with
                | some (g', rest'') => some (or f' g', rest'')
                | none => none
            | none => none) = some (or f g, w)
          rw [List.append_assoc f.encode g.encode w]
          rw [ihf n (g.encode ++ w) hf]
          simp
          rw [ihg n w hg]

lemma parse_encode (f : Formula) (w : Word) :
    parse (f.encode ++ w) = some (f, w) := by
  dsimp [parse]
  apply parseFuel_encode
  simp

lemma parseNat_spec {w : Word} {n : Nat} {rest : Word}
    (h : parseNat w = some (n, rest)) : w = encodeNat n ++ rest := by
  induction w generalizing n rest with
  | nil => simp [parseNat] at h
  | cons b w ih =>
      cases b with
      | false =>
          simp [parseNat] at h
          rcases h with ⟨hn, hr⟩
          have hn' : n = 0 := hn.symm
          have hr' : rest = w := hr.symm
          subst n
          subst rest
          simp [encodeNat]
      | true =>
          cases ho : parseNat w with
          | none => simp [parseNat, ho] at h
          | some p =>
              rcases p with ⟨n', rest'⟩
              have hw : w = encodeNat n' ++ rest' := ih ho
              simp [parseNat, ho] at h
              rcases h with ⟨hn, hr⟩
              have hn' : n = n' + 1 := hn.symm
              have hr' : rest = rest' := hr.symm
              subst n
              subst rest
              simp [encodeNat, List.replicate_succ, hw]

lemma parseFuel_spec : ∀ (n : Nat) (z : Word) (f : Formula) (rest : Word),
    parseFuel n z = some (f, rest) → z = f.encode ++ rest := by
  intro n
  induction n with
  | zero =>
      intro z f rest h
      simp [parseFuel] at h
  | succ n ih =>
      intro z f rest h
      cases z with
      | nil => simp [parseFuel] at h
      | cons b1 z =>
          cases b1 with
          | false =>
              cases z with
              | nil => simp [parseFuel] at h
              | cons b2 z =>
                  cases b2 with
                  | false =>
                      cases ho : parseNat z with
                      | none => simp [parseFuel, ho] at h
                      | some p =>
                          rcases p with ⟨i, rest'⟩
                          have hz : z = encodeNat i ++ rest' := parseNat_spec ho
                          simp [parseFuel, ho] at h
                          rcases h with ⟨hf, hr⟩
                          subst f
                          subst rest
                          simp [encode, hz]
                  | true =>
                      cases ho : parseFuel n z with
                      | none => simp [parseFuel, ho] at h
                      | some p =>
                          rcases p with ⟨f', rest'⟩
                          have hz : z = f'.encode ++ rest' := ih z f' rest' ho
                          simp [parseFuel, ho] at h
                          rcases h with ⟨hf, hr⟩
                          subst f
                          subst rest
                          simp [encode, hz]
          | true =>
              cases z with
              | nil => simp [parseFuel] at h
              | cons b2 z =>
                  cases b2 with
                  | false =>
                      cases ho1 : parseFuel n z with
                      | none => simp [parseFuel, ho1] at h
                      | some p1 =>
                          rcases p1 with ⟨f', rest'⟩
                          have hz1 : z = f'.encode ++ rest' := ih z f' rest' ho1
                          cases ho2 : parseFuel n rest' with
                          | none => simp [parseFuel, ho1, ho2] at h
                          | some p2 =>
                              rcases p2 with ⟨g', rest''⟩
                              have hz2 : rest' = g'.encode ++ rest'' :=
                                ih rest' g' rest'' ho2
                              simp [parseFuel, ho1, ho2] at h
                              rcases h with ⟨hf, hr⟩
                              subst f
                              subst rest
                              simp [encode, hz1, hz2, List.append_assoc]
                  | true =>
                      cases ho1 : parseFuel n z with
                      | none => simp [parseFuel, ho1] at h
                      | some p1 =>
                          rcases p1 with ⟨f', rest'⟩
                          have hz1 : z = f'.encode ++ rest' := ih z f' rest' ho1
                          cases ho2 : parseFuel n rest' with
                          | none => simp [parseFuel, ho1, ho2] at h
                          | some p2 =>
                              rcases p2 with ⟨g', rest''⟩
                              have hz2 : rest' = g'.encode ++ rest'' :=
                                ih rest' g' rest'' ho2
                              simp [parseFuel, ho1, ho2] at h
                              rcases h with ⟨hf, hr⟩
                              subst f
                              subst rest
                              simp [encode, hz1, hz2, List.append_assoc]

lemma parse_spec {z : Word} {f : Formula} {rest : Word}
    (h : parse z = some (f, rest)) : z = f.encode ++ rest := by
  exact parseFuel_spec z.length z f rest h

lemma parse_eq_iff (z : Word) (f : Formula) (rest : Word) :
    parse z = some (f, rest) ↔ z = f.encode ++ rest := by
  constructor
  · exact parse_spec
  · intro hz
    rw [hz]
    exact parse_encode f rest

/-- A classical decoder for formula encodings.  This is useful for semantic
    lemmas; it is not the computable parser needed for a TM verifier. -/
noncomputable def decode (x : Word) : Option Formula := by
  classical
  exact if h : ∃ f : Formula, f.encode = x then some (Classical.choose h) else none

lemma decode_encode (f : Formula) : decode f.encode = some f := by
  classical
  dsimp [decode]
  have h : ∃ g : Formula, g.encode = f.encode := ⟨f, rfl⟩
  rw [dite_eq_left h]
  apply congrArg some
  apply encode_injective
  exact Classical.choose_spec h

lemma decode_spec {x : Word} {f : Formula} (hdec : decode x = some f) :
    f.encode = x := by
  classical
  by_cases h : ∃ g : Formula, g.encode = x
  · dsimp [decode] at hdec
    rw [dite_eq_left h] at hdec
    have hchoose : Classical.choose h = f := Option.some.inj hdec
    simpa [hchoose] using Classical.choose_spec h
  · dsimp [decode] at hdec
    rw [dite_eq_right h] at hdec
    cases hdec

theorem decode_eq_iff {x : Word} {f : Formula} :
    decode x = some f ↔ f.encode = x := by
  constructor
  · exact decode_spec
  · intro hfx
    have hf := decode_encode f
    rwa [hfx] at hf

theorem decode_eq_none_iff (x : Word) :
    decode x = none ↔ ∀ f : Formula, f.encode ≠ x := by
  classical
  constructor
  · intro hdec f hfx
    have hs : decode x = some f := by
      have hf := decode_encode f
      rwa [hfx] at hf
    rw [hdec] at hs
    cases hs
  · intro hnone
    by_cases h : ∃ f : Formula, f.encode = x
    · rcases h with ⟨f, hfx⟩
      exfalso
      exact hnone f hfx
    · dsimp [decode]
      rw [dite_eq_right h]

/-- A computable enumeration of formulas whose encoding length is at most `n`. -/
def enum : Nat → List Formula
  | 0 => []
  | n + 1 =>
      ((List.range (n + 1)).map fun i => var i) ++
      (enum n).map not ++
      ((enum n).product (enum n)).filterMap (fun p =>
        if p.1.encode.length + p.2.encode.length + 2 ≤ n + 1 then
          some (and p.1 p.2)
        else none) ++
      ((enum n).product (enum n)).filterMap (fun p =>
        if p.1.encode.length + p.2.encode.length + 2 ≤ n + 1 then
          some (or p.1 p.2)
        else none)

lemma mem_enum_of_encode_length_le : ∀ (f : Formula) (n : Nat),
    f.encode.length ≤ n → f ∈ enum n := by
  intro f n
  induction n generalizing f with
  | zero =>
      intro h
      cases f <;> simp [encode, encodeNat] at h
  | succ n ih =>
      intro h
      cases f with
      | var i =>
          simp [enum, encode, encodeNat, List.mem_range] at h ⊢
          omega
      | not f =>
          have hf : f.encode.length ≤ n := by
            simp [encode] at h
            omega
          have hfmem := ih f hf
          simp [enum, hfmem]
      | and f g =>
          have hf : f.encode.length ≤ n := by
            simp [encode] at h
            omega
          have hg : g.encode.length ≤ n := by
            simp [encode] at h
            omega
          have hfmem := ih f hf
          have hgmem := ih g hg
          have hsum : f.encode.length + g.encode.length + 1 ≤ n := by
            simp [encode] at h
            omega
          simp [enum, List.mem_filterMap, hfmem, hgmem, hsum]
      | or f g =>
          have hf : f.encode.length ≤ n := by
            simp [encode] at h
            omega
          have hg : g.encode.length ≤ n := by
            simp [encode] at h
            omega
          have hfmem := ih f hf
          have hgmem := ih g hg
          have hsum : f.encode.length + g.encode.length + 1 ≤ n := by
            simp [encode] at h
            omega
          simp [enum, List.mem_filterMap, hfmem, hgmem, hsum]

/-- A computable decoder obtained by searching the finite enumeration. -/
def decodeComp (x : Word) : Option Formula :=
  (enum x.length).find? (fun f => f.encode == x)

lemma decodeComp_encode (f : Formula) : decodeComp f.encode = some f := by
  unfold decodeComp
  apply find?_eq_some_of_mem_of_unique
  · intro a b ha hb
    apply encode_injective
    have hae : a.encode = f.encode := by simpa using ha
    have hbe : b.encode = f.encode := by simpa using hb
    exact hae.trans hbe.symm
  · apply mem_enum_of_encode_length_le
    simp
  · simp

lemma decodeComp_spec {x : Word} {f : Formula} (h : decodeComp x = some f) :
    f.encode = x := by
  unfold decodeComp at h
  have hp := find?_pred_of_eq_some (fun g : Formula => g.encode == x) h
  simpa using hp

theorem decodeComp_eq_decode (x : Word) : decodeComp x = decode x := by
  classical
  cases hc : decodeComp x with
  | none =>
      apply Eq.symm
      rw [decode_eq_none_iff]
      intro f hfx
      have hsome := decodeComp_encode f
      rw [hfx] at hsome
      rw [hc] at hsome
      cases hsome
  | some f =>
      have hfx := decodeComp_spec hc
      have hd : decode x = some f := (decode_eq_iff).2 hfx
      exact hd.symm

/-- The largest variable index occurring in a formula. -/
def maxVar : Formula → Nat
  | var i => i
  | not f => f.maxVar
  | and f g => max f.maxVar g.maxVar
  | or f g => max f.maxVar g.maxVar

lemma ofCircuit_maxVar_le (c : Circuit) : (ofCircuit c).maxVar ≤ c.maxVar := by
  induction c with
  | const b =>
      cases b <;> simp [ofCircuit, maxVar, trueFormula, falseFormula]
  | var i => simp [ofCircuit, maxVar, Circuit.maxVar]
  | not c ih => simpa [ofCircuit, maxVar, Circuit.maxVar] using ih
  | and c₁ c₂ ih1 ih2 =>
      dsimp [ofCircuit, maxVar, Circuit.maxVar]
      exact max_le_max ih1 ih2
  | or c₁ c₂ ih1 ih2 =>
      dsimp [ofCircuit, maxVar, Circuit.maxVar]
      exact max_le_max ih1 ih2

/-- The reverse bridge: a formula is also a circuit, with one gate per
    connective.  Unlike `ofCircuit`, this direction is tree-sized but preserves
    the structural shape of the formula. -/
def toCircuit : Formula → Circuit
  | var i => Circuit.var i
  | not f => Circuit.not (toCircuit f)
  | and f g => Circuit.and (toCircuit f) (toCircuit g)
  | or f g => Circuit.or (toCircuit f) (toCircuit g)

lemma toCircuit_eval (f : Formula) (x : Word) :
    (toCircuit f).eval x = f.eval (fun i => x.getD i false) := by
  induction f with
  | var i => simp [toCircuit, eval]
  | not f ih => simp [toCircuit, eval, ih]
  | and f g ihf ihg => simp [toCircuit, eval, ihf, ihg]
  | or f g ihf ihg => simp [toCircuit, eval, ihf, ihg]

lemma toCircuit_maxVar_le (f : Formula) : (toCircuit f).maxVar ≤ f.maxVar := by
  induction f with
  | var i => simp [toCircuit, Circuit.maxVar, maxVar]
  | not f ih => simpa [toCircuit, Circuit.maxVar, maxVar] using ih
  | and f g ihf ihg =>
      dsimp [toCircuit, Circuit.maxVar, maxVar]
      exact max_le_max ihf ihg
  | or f g ihf ihg =>
      dsimp [toCircuit, Circuit.maxVar, maxVar]
      exact max_le_max ihf ihg

/-- Evaluation only depends on assignment entries up to `maxVar`. -/
lemma eval_eq_of_agree_on_vars (f : Formula) {a b : Nat → Bool}
    (h : ∀ i, i ≤ f.maxVar → a i = b i) : f.eval a = f.eval b := by
  induction f with
  | var i =>
      simp [eval, h i le_rfl]
  | not f ih =>
      have hf : f.eval a = f.eval b := ih (by
        intro i hi
        exact h i hi)
      simp [eval, hf]
  | and f g ihf ihg =>
      have hf : f.eval a = f.eval b := ihf (by
        intro i hi
        exact h i (Nat.le_trans hi (Nat.le_max_left _ _)))
      have hg : g.eval a = g.eval b := ihg (by
        intro i hi
        exact h i (Nat.le_trans hi (Nat.le_max_right _ _)))
      simp [eval, hf, hg]
  | or f g ihf ihg =>
      have hf : f.eval a = f.eval b := ihf (by
        intro i hi
        exact h i (Nat.le_trans hi (Nat.le_max_left _ _)))
      have hg : g.eval a = g.eval b := ihg (by
        intro i hi
        exact h i (Nat.le_trans hi (Nat.le_max_right _ _)))
      simp [eval, hf, hg]

lemma toCircuit_sat_iff (f : Formula) :
    (∃ a : Nat → Bool, f.eval a = true) ↔
      ∃ x : Word, (toCircuit f).eval x = true := by
  constructor
  · rintro ⟨a, ha⟩
    let x : Word := List.ofFn (fun i : Fin (f.maxVar + 1) => a i)
    refine ⟨x, ?_⟩
    rw [toCircuit_eval]
    have hget : ∀ i, i ≤ f.maxVar → x.getD i false = a i := by
      intro i hi
      have hi' : i < f.maxVar + 1 := by omega
      rw [List.getD_eq_getElem x false (by simpa [x] using hi')]
      simpa [x] using (List.getElem_ofFn
        (f := fun j : Fin (f.maxVar + 1) => a j) (by simpa using hi'))
    exact (eval_eq_of_agree_on_vars f hget).trans ha
  · rintro ⟨x, hx⟩
    refine ⟨fun i => x.getD i false, ?_⟩
    rw [← toCircuit_eval]
    exact hx

/-- The finite set of variables occurring in a formula. -/
def vars : Formula → Finset Nat
  | var i => {i}
  | not f => f.vars
  | and f g => f.vars ∪ g.vars
  | or f g => f.vars ∪ g.vars

lemma toCircuit_vars (f : Formula) : (toCircuit f).vars = f.vars := by
  induction f with
  | var i => simp [Formula.toCircuit, Formula.vars, Circuit.vars]
  | not f ih => simpa [Formula.toCircuit, Formula.vars, Circuit.vars] using ih
  | and f g ihf ihg =>
      simp [Formula.toCircuit, Formula.vars, Circuit.vars, ihf, ihg]
  | or f g ihf ihg =>
      simp [Formula.toCircuit, Formula.vars, Circuit.vars, ihf, ihg]

@[simp] lemma mem_vars_var (i j : Nat) : i ∈ (var j : Formula).vars ↔ i = j := by
  simp [vars]

lemma eval_eq_of_agree_on_vars_finset (f : Formula) {a b : Nat → Bool}
    (h : ∀ i, i ∈ f.vars → a i = b i) : f.eval a = f.eval b := by
  induction f with
  | var i =>
      exact h i (by simp [vars])
  | not f ih =>
      have hf : f.eval a = f.eval b := ih (by
        intro i hi
        exact h i hi)
      simp [eval, hf]
  | and f g ihf ihg =>
      have hf : f.eval a = f.eval b := ihf (by
        intro i hi
        exact h i (by simp [vars, hi]))
      have hg : g.eval a = g.eval b := ihg (by
        intro i hi
        exact h i (by simp [vars, hi]))
      simp [eval, hf, hg]
  | or f g ihf ihg =>
      have hf : f.eval a = f.eval b := ihf (by
        intro i hi
        exact h i (by simp [vars, hi]))
      have hg : g.eval a = g.eval b := ihg (by
        intro i hi
        exact h i (by simp [vars, hi]))
      simp [eval, hf, hg]

lemma mem_vars_le_maxVar {f : Formula} {i : Nat} (hi : i ∈ f.vars) :
    i ≤ f.maxVar := by
  induction f with
  | var j =>
      have hij : i = j := by simpa [vars] using hi
      subst i
      simp [maxVar]
  | not f ih =>
      exact ih hi
  | and f g ihf ihg =>
      simp [vars] at hi
      rcases hi with hi | hi
      · exact Nat.le_trans (ihf hi) (Nat.le_max_left _ _)
      · exact Nat.le_trans (ihg hi) (Nat.le_max_right _ _)
  | or f g ihf ihg =>
      simp [vars] at hi
      rcases hi with hi | hi
      · exact Nat.le_trans (ihf hi) (Nat.le_max_left _ _)
      · exact Nat.le_trans (ihg hi) (Nat.le_max_right _ _)

/-- Extend a finite assignment on `Fin (maxVar + 1)` to a total assignment. -/
def assign (f : Formula) (a : Fin (f.maxVar + 1) → Bool) : Nat → Bool :=
  fun i => if h : i < f.maxVar + 1 then a ⟨i, h⟩ else false

lemma assign_agree (f : Formula) (a : Fin (f.maxVar + 1) → Bool)
    (i : Nat) (hi : i < f.maxVar + 1) :
    f.assign a i = a ⟨i, hi⟩ := by
  simp [assign, hi]

/-- A computable enumeration of all Boolean assignments on `Fin n`. -/
def assignments : (n : Nat) → List (Fin n → Bool)
  | 0 => [Fin.elim0]
  | n + 1 =>
      (assignments n).flatMap fun a =>
        [ fun i => if h : i.val < n then a ⟨i.val, h⟩ else false
        , fun i => if h : i.val < n then a ⟨i.val, h⟩ else true ]

lemma mem_assignments : ∀ (n : Nat) (a : Fin n → Bool), a ∈ assignments n := by
  intro n
  induction n with
  | zero =>
      intro a
      simp [assignments]
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      intro a
      let a0 : Fin n → Bool := fun i => a ⟨i.val, by omega⟩
      have ha0 : a0 ∈ assignments n := ih a0
      cases hlast : a ⟨n, by omega⟩
      · simp [assignments]
        refine ⟨a0, ha0, Or.inl ?_⟩
        ext i
        by_cases hi : i.val < n
        · simp [hi, a0]
        · have hin : i.val = n := by omega
          have hiEq : i = ⟨n, by omega⟩ := Fin.ext hin
          simpa [hiEq] using hlast
      · simp [assignments]
        refine ⟨a0, ha0, Or.inr ?_⟩
        ext i
        by_cases hi : i.val < n
        · simp [hi, a0]
        · have hin : i.val = n := by omega
          have hiEq : i = ⟨n, by omega⟩ := Fin.ext hin
          simpa [hiEq] using hlast

lemma assignments_length : ∀ n : Nat, (assignments n).length = 2 ^ n := by
  intro n
  induction n with
  | zero => simp [assignments]
  | succ n ih =>
      simp [assignments, ih, Nat.pow_succ, Nat.mul_comm]

/-- Read a bounded assignment from a Boolean word, using `false` past the end. -/
def assignOfWord (f : Formula) (w : Word) : Fin (f.maxVar + 1) → Bool :=
  fun i => w.getD i.val false

lemma assignOfWord_ofFn (f : Formula) (a : Fin (f.maxVar + 1) → Bool) :
    assignOfWord f (List.ofFn a) = a := by
  funext i
  dsimp [assignOfWord]
  rw [List.getD_eq_getElem (List.ofFn a) false (by simp)]
  rw [List.getElem_ofFn (i := i.val) (f := a) (by simp)]

lemma assignOfWord_eq_of_length (f : Formula) {w : Word}
    (hw : w.length = f.maxVar + 1) (i : Fin (f.maxVar + 1)) :
    assignOfWord f w i = w.get ⟨i.val, by simp [hw]⟩ := by
  simp [assignOfWord, hw]

/-- Satisfiability of a fixed formula is equivalent to satisfiability by an
    assignment over only the variables that occur in it. -/
lemma sat_iff_bounded (f : Formula) :
    (∃ a : Nat → Bool, f.eval a = true) ↔
      ∃ a : Fin (f.maxVar + 1) → Bool, f.eval (f.assign a) = true := by
  constructor
  · rintro ⟨a, ha⟩
    let b : Fin (f.maxVar + 1) → Bool := fun i => a i.val
    refine ⟨b, ?_⟩
    have hagree : ∀ i, i ≤ f.maxVar → f.assign b i = a i := by
      intro i hi
      have hai := f.assign_agree b i (by omega)
      simpa [b] using hai
    exact (eval_eq_of_agree_on_vars f hagree).trans ha
  · rintro ⟨a, ha⟩
    exact ⟨f.assign a, ha⟩

/-- Bounded satisfiability can be checked over the finite assignment enumeration. -/
theorem sat_iff_bounded_assignments (f : Formula) :
    (∃ a : Nat → Bool, f.eval a = true) ↔
      ∃ a ∈ assignments (f.maxVar + 1), f.eval (f.assign a) = true := by
  constructor
  · intro h
    rcases (f.sat_iff_bounded).1 h with ⟨a, ha⟩
    exact ⟨a, mem_assignments (f.maxVar + 1) a, ha⟩
  · rintro ⟨a, -, ha⟩
    exact ⟨f.assign a, ha⟩

/-- A finite search procedure for satisfiability of a formula. -/
def satSearch (f : Formula) : Bool :=
  (assignments (f.maxVar + 1)).any (fun a => f.eval (f.assign a))

theorem satSearch_eq_true (f : Formula) :
    satSearch f = true ↔ ∃ a : Nat → Bool, f.eval a = true := by
  rw [show satSearch f = true ↔
        ∃ a ∈ assignments (f.maxVar + 1), f.eval (f.assign a) = true by
    simp [satSearch, List.any_eq_true]]
  exact (f.sat_iff_bounded_assignments).symm

/-- The index of any occurring variable is smaller than the encoded length. -/
lemma maxVar_lt_encode_length (f : Formula) : f.maxVar < f.encode.length := by
  induction f with
  | var i =>
      simp [maxVar, encode, encodeNat]
      omega
  | not f ih =>
      simp [maxVar, encode]
      omega
  | and f g ihf ihg =>
      simp [maxVar, encode]
      omega
  | or f g ihf ihg =>
      simp [maxVar, encode]
      omega

end Formula

/-- SAT as a language of encoded satisfiable formulas. -/
def SAT : Language :=
  {x | ∃ f : Formula, f.encode = x ∧ ∃ a : Nat → Bool, f.eval a = true}

lemma Formula.encode_length_and_var (f : Formula) (k : Nat) :
    (Formula.and f (Formula.var k)).encode.length = f.encode.length + k + 5 := by
  simp [Formula.encode, Formula.encodeNat_length]
  omega

lemma Formula.and_var_sat_iff_of_fresh (f : Formula) (k : Nat) (hk : f.maxVar < k) :
    (∃ a : Nat → Bool, (Formula.and f (Formula.var k)).eval a = true) ↔
      ∃ a : Nat → Bool, f.eval a = true := by
  constructor
  · rintro ⟨a, ha⟩
    cases hf : f.eval a <;> simp [hf] at ha
    exact ⟨a, hf⟩
  · rintro ⟨a, ha⟩
    let b : Nat → Bool := fun i => if i = k then true else a i
    have hb_agree : ∀ i, i ≤ f.maxVar → b i = a i := by
      intro i hi
      dsimp [b]
      split_ifs with h
      · subst k
        omega
      · rfl
    have hfb : f.eval b = f.eval a := Formula.eval_eq_of_agree_on_vars f hb_agree
    refine ⟨b, ?_⟩
    change f.eval b && b k = true
    rw [hfb, ha]
    simp [b]

lemma Formula.mem_SAT_of_eval_true (f : Formula) (a : Nat → Bool)
    (h : f.eval a = true) : f.encode ∈ SAT := by
  refine ⟨f, rfl, a, h⟩

lemma Formula.mem_SAT_iff_sat (f : Formula) :
    f.encode ∈ SAT ↔ ∃ a : Nat → Bool, f.eval a = true := by
  constructor
  · rintro ⟨g, hg, a, ha⟩
    have hgf : g = f := Formula.encode_injective hg
    subst g
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    exact Formula.mem_SAT_of_eval_true f a ha

/-- A satisfying assignment for a circuit gives a SAT instance via the direct
    tree expansion. -/
lemma circuit_formula_mem_SAT_of_eval_true (c : Circuit) (x : Word)
    (h : c.eval x = true) : (Formula.ofCircuit c).encode ∈ SAT := by
  apply Formula.mem_SAT_of_eval_true
  rw [Formula.ofCircuit_eval]
  exact h

lemma formula_mem_SAT_ofCircuit_eval_true {c : Circuit}
    (h : (Formula.ofCircuit c).encode ∈ SAT) :
    ∃ x : Word, c.eval x = true := by
  rcases h with ⟨f, hf, a, ha⟩
  have hfc : f = Formula.ofCircuit c := Formula.encode_injective hf
  subst f
  let x : Word := List.ofFn (fun i : Fin (c.maxVar + 1) => a i.val)
  refine ⟨x, ?_⟩
  rw [← Formula.ofCircuit_eval c x]
  have hxget (i : Nat) (hi : i ≤ c.maxVar) : x.getD i false = a i := by
    dsimp [x]
    rw [List.getD_eq_getElem
      (List.ofFn (fun j : Fin (c.maxVar + 1) => a j.val)) false
      (by simpa using Nat.lt_succ_of_le hi)]
    rw [List.getElem_ofFn (i := i)
      (f := fun j : Fin (c.maxVar + 1) => a j.val)
      (by simpa using Nat.lt_succ_of_le hi)]
  have hagree : ∀ i, i ≤ (Formula.ofCircuit c).maxVar →
      a i = (fun j => x.getD j false) i := by
    intro i hi
    exact (hxget i (Nat.le_trans hi (Formula.ofCircuit_maxVar_le c))).symm
  exact ((Formula.eval_eq_of_agree_on_vars (Formula.ofCircuit c) hagree).symm).trans ha

theorem circuit_formula_SAT_iff (c : Circuit) :
    (∃ x : Word, c.eval x = true) ↔ (Formula.ofCircuit c).encode ∈ SAT := by
  constructor
  · rintro ⟨x, hx⟩
    exact circuit_formula_mem_SAT_of_eval_true c x hx
  · exact formula_mem_SAT_ofCircuit_eval_true

lemma sat_var_zero : (Formula.var 0).encode ∈ SAT := by
  refine Formula.mem_SAT_of_eval_true (Formula.var 0) (fun _ => true) ?_
  simp [Formula.eval]

lemma sat_tautology : (Formula.or (Formula.var 0) (Formula.not (Formula.var 0))).encode ∈ SAT := by
  refine Formula.mem_SAT_of_eval_true
    (Formula.or (Formula.var 0) (Formula.not (Formula.var 0))) (fun _ => true) ?_
  simp [Formula.eval]

lemma unsat_contradiction :
    (Formula.and (Formula.var 0) (Formula.not (Formula.var 0))).encode ∉ SAT := by
  rintro ⟨f, hf, a, ha⟩
  have hf' : f = Formula.and (Formula.var 0) (Formula.not (Formula.var 0)) :=
    Formula.encode_injective hf
  subst f
  simp [Formula.eval] at ha

lemma Formula.bounded_assignment_mem_SAT (f : Formula)
    (a : Fin (f.maxVar + 1) → Bool) (h : f.eval (f.assign a) = true) :
    f.encode ∈ SAT := by
  exact Formula.mem_SAT_of_eval_true f (f.assign a) h

/-- A bounded assignment has length at most the formula encoding length. -/
lemma Formula.bounded_assignment_length_le (f : Formula)
    (a : Fin (f.maxVar + 1) → Bool) :
    (List.ofFn a).length ≤ f.encode.length := by
  simp
  have h := f.maxVar_lt_encode_length
  omega

/-- The formula witnessing membership of a SAT word is unique. -/
lemma SAT_formula_unique {x : Word} {f g : Formula}
    (hf : f.encode = x) (hg : g.encode = x) : f = g :=
  Formula.encode_injective (hf.trans hg.symm)

/-- SAT membership can be stated in terms of the classical decoder. -/
theorem SAT_iff_decode_sat (x : Word) :
    x ∈ SAT ↔ ∃ (f : Formula) (a : Nat → Bool),
      Formula.decode x = some f ∧ f.eval a = true := by
  constructor
  · rintro ⟨f, hfx, a, ha⟩
    exact ⟨f, a, (Formula.decode_eq_iff).2 hfx, ha⟩
  · rintro ⟨f, a, hdec, ha⟩
    exact ⟨f, (Formula.decode_eq_iff).1 hdec, a, ha⟩

/-- A concrete Boolean certificate checker for SAT.  It decodes the formula
    from the instance word, reads the assignment from the certificate word,
    and evaluates the decoded formula. -/
def SATVerify (x cert : Word) : Bool :=
  match Formula.decodeComp x with
  | none => false
  | some f =>
      if cert.length = f.maxVar + 1 then
        f.eval (f.assign (Formula.assignOfWord f cert))
      else false

theorem SATVerify_eq_true_iff (x cert : Word) :
    SATVerify x cert = true ↔
      ∃ f : Formula, Formula.decodeComp x = some f ∧
        cert.length = f.maxVar + 1 ∧
        f.eval (f.assign (Formula.assignOfWord f cert)) = true := by
  unfold SATVerify
  cases hdec : Formula.decodeComp x with
  | none => simp
  | some f => simp

theorem SATVerify_sound {x cert : Word} (h : SATVerify x cert = true) :
    x ∈ SAT := by
  rcases (SATVerify_eq_true_iff x cert).1 h with ⟨f, hdec, hlen, heval⟩
  have hfx : f.encode = x := Formula.decodeComp_spec hdec
  have hmem : f.encode ∈ SAT :=
    Formula.mem_SAT_of_eval_true f (f.assign (Formula.assignOfWord f cert)) heval
  simpa [hfx] using hmem

/-- SAT membership is equivalent to existence of a bounded assignment for the
    witnessing formula.  This avoids needing a parser for the concrete TM
    verifier: the formula witness is part of the SAT definition. -/
theorem SAT_iff_bounded_witness (x : Word) :
    x ∈ SAT ↔
      ∃ (f : Formula) (a : Fin (f.maxVar + 1) → Bool),
        f.encode = x ∧ f.eval (f.assign a) = true := by
  constructor
  · rintro ⟨f, rfl, a, ha⟩
    rcases (f.sat_iff_bounded).1 ⟨a, ha⟩ with ⟨b, hb⟩
    exact ⟨f, b, rfl, hb⟩
  · rintro ⟨f, a, rfl, ha⟩
    exact ⟨f, rfl, f.assign a, ha⟩

/-- Every SAT instance has a satisfying certificate no longer than the input. -/
lemma SAT_bounded_certificate {x : Word} (hx : x ∈ SAT) :
    ∃ (f : Formula) (a : Fin (f.maxVar + 1) → Bool),
      f.encode = x ∧ f.eval (f.assign a) = true ∧
        (List.ofFn a).length ≤ x.length := by
  rcases (SAT_iff_bounded_witness x).1 hx with ⟨f, a, hfx, htrue⟩
  refine ⟨f, a, hfx, htrue, ?_⟩
  rw [← hfx]
  exact f.bounded_assignment_length_le a

/-- Every SAT instance has a certificate accepted by the concrete checker,
    with certificate length bounded by the input length. -/
theorem SATVerify_complete {x : Word} (hx : x ∈ SAT) :
    ∃ cert : Word, cert.length ≤ x.length ∧ SATVerify x cert = true := by
  rcases SAT_bounded_certificate hx with ⟨f, a, hfx, htrue, hlen⟩
  refine ⟨List.ofFn a, ?_, ?_⟩
  · simpa using hlen
  · have hdec : Formula.decodeComp x = some f := by
      rw [Formula.decodeComp_eq_decode x]
      exact (Formula.decode_eq_iff).2 hfx
    unfold SATVerify
    rw [hdec]
    change (if (List.ofFn a).length = f.maxVar + 1 then
        f.eval (f.assign (Formula.assignOfWord f (List.ofFn a))) else false) = true
    split
    next h =>
      rw [Formula.assignOfWord_ofFn f a]
      exact htrue
    next h =>
      simp at h

/-- A checked SAT verifier that first requires the instance word to parse as a
    complete formula encoding.  Malformed instance words are rejected without
    inspecting the certificate. -/
def SATVerifyParsed (x cert : Word) : Bool :=
  match Formula.parse x with
  | some (_, []) => SATVerify x cert
  | _ => false

theorem SATVerifyParsed_sound {x cert : Word} (h : SATVerifyParsed x cert = true) :
    x ∈ SAT := by
  unfold SATVerifyParsed at h
  cases hp : Formula.parse x with
  | none => simp [hp] at h
  | some p =>
      rcases p with ⟨f, rest⟩
      cases rest with
      | nil =>
          simp [hp] at h
          have hfx : f.encode = x := by
            have hparse := (Formula.parse_eq_iff x f []).1 hp
            simpa using hparse.symm
          have hdecode : Formula.decodeComp x = some f := by
            rw [Formula.decodeComp_eq_decode x]
            exact (Formula.decode_eq_iff).2 hfx
          rcases (SATVerify_eq_true_iff x cert).1 h with
            ⟨g, hgdecode, hglen, hgeval⟩
          have hgf : g = f := Option.some.inj (hgdecode.symm.trans hdecode)
          subst g
          have hmem : f.encode ∈ SAT := Formula.mem_SAT_of_eval_true f
            (f.assign (Formula.assignOfWord f cert)) hgeval
          simpa [hfx] using hmem
      | cons b bs => simp [hp] at h

theorem SATVerifyParsed_eq_SATVerify {x cert : Word} (hx : x ∈ SAT) :
    SATVerifyParsed x cert = SATVerify x cert := by
  unfold SATVerifyParsed
  rcases (SAT_iff_bounded_witness x).1 hx with ⟨f, a, hfx, htrue⟩
  have hp : Formula.parse x = some (f, ([] : Word)) := by
    rw [← hfx]
    simpa using Formula.parse_encode f ([] : Word)
  simp [hp]

/-- Every SAT instance has a certificate accepted by the checked verifier. -/
theorem SATVerifyParsed_complete {x : Word} (hx : x ∈ SAT) :
    ∃ cert : Word, cert.length ≤ x.length ∧ SATVerifyParsed x cert = true := by
  rcases SATVerify_complete hx with ⟨cert, hlen, hacc⟩
  refine ⟨cert, hlen, ?_⟩
  rw [SATVerifyParsed_eq_SATVerify hx]
  exact hacc

/-- The Cook-Levin obligation for this encoding: SAT has a polynomial-time
    verifier in the concrete TM model.  This is the standard but lengthy
    construction of a machine that checks a certificate assignment. -/
def SATVerifierExists : Prop := InNP SAT

/-- The remaining concrete verifier obligation, stated directly in terms of
    `SATVerify`: a TM computes the certificate checker on input `x ++ cert`.
    Parsing the formula prefix of `x ++ cert` is part of this obligation. -/
def SATVerifierTMExists : Prop :=
  ∃ (V : TM) (p : TimeBound),
    (∀ x cert : Word,
      halted V (run V (p.eval (x ++ cert).length) (init V (x ++ cert))) = true) ∧
    ∀ x cert : Word,
      acceptsIn V (x ++ cert) (p.eval (x ++ cert).length) = true ↔
        SATVerify x cert = true

/-- A TM implementing `SATVerify` is enough to discharge `SATVerifierExists`. -/
theorem SATVerifierTMExists_implies_SATVerifierExists :
    SATVerifierTMExists → SATVerifierExists := by
  intro h
  rcases h with ⟨V, p, hhalt, hcorrect⟩
  refine ⟨V, p, Polynomial.X, ?_, ?_⟩
  · exact hhalt
  · intro x
    constructor
    · intro hx
      rcases SATVerify_complete hx with ⟨cert, hlen, hacc⟩
      refine ⟨cert, ?_, ?_⟩
      · simpa using hlen
      · exact (hcorrect x cert).2 hacc
    · rintro ⟨cert, hlen, hacc⟩
      have hverify : SATVerify x cert = true := (hcorrect x cert).1 hacc
      exact SATVerify_sound hverify

/-- The concrete circuit lower bound needed for the 3b route. -/
def SATNotInPPoly : Prop := ¬ InPPoly SAT

/-- Reducing the concrete lower-bound target to `P ≠ NP`. -/
theorem SATNotInPPoly_implies_not_PEqualsNP (hver : SATVerifierExists) :
    SATNotInPPoly → ¬ PEqualsNP := by
  intro hlow
  exact NPNotInPPoly_implies_not_PEqualsNP ⟨SAT, hver, hlow⟩

/-- P/poly is closed under polynomial-time many-one reductions. -/
def PPolyClosedUnderReductions : Prop :=
  ∀ L₁ L₂ : Language, InPPoly L₂ → Reducible L₁ L₂ → InPPoly L₁

/-- The standard closure proof: compile the reduction transducer into one
    output-bit circuit family and substitute those circuits into the family for
    the target language. -/
theorem pPolyClosedUnderReductions : PPolyClosedUnderReductions := by
  intro L₁ L₂ hL₂ hred
  rcases hL₂ with ⟨F₂, hF₂size, hF₂correct⟩
  rcases hF₂size with ⟨q, hq⟩
  rcases hred with ⟨f, hf, hrediff⟩
  rcases hf with ⟨M, p, hhalt, hout⟩
  let r : TimeBound := p + 1
  let s : TimeBound := unrollPoly M p + 1
  let P : TimeBound := (q.comp r) * s
  let g : Nat → Nat → Circuit := fun n i => reductionBits M p n i
  let F₁ : CircuitFamily := fun n => Circuit.substVars (g n) (F₂ (r.eval n))
  have hflen : ∀ x : Word, (f x).length = r.eval x.length := by
    intro x
    rw [← hout x]
    simp [r, boutputIn]
  refine ⟨F₁, ?_, ?_⟩
  · refine ⟨P, ?_⟩
    intro n
    have hk : 1 ≤ s.eval n := by
      simp [s]
    have hbits : ∀ i, (g n i).size ≤ s.eval n := by
      intro i
      have hb := reductionBits_size_le M p n i
      simpa [g, s] using hb
    have hsub := Circuit.size_substVars_le (g n) (s.eval n) hbits hk (F₂ (r.eval n))
    have hmul : (F₂ (r.eval n)).size * s.eval n ≤ q.eval (r.eval n) * s.eval n :=
      Nat.mul_le_mul_right (s.eval n) (hq (r.eval n))
    have hP : P.eval n = q.eval (r.eval n) * s.eval n := by
      simp [P]
    dsimp [F₁]
    rw [hP]
    exact le_trans hsub hmul
  · intro x
    let n := x.length
    let m := r.eval n
    change (F₁ n).eval x = true ↔ x ∈ L₁
    have hgout : ∀ i, m ≤ i → g n i = Circuit.const false := by
      intro i hi
      dsimp [g, m, r] at hi ⊢
      exact reductionBits_of_not_lt M p n i (by simpa using hi)
    have hcomp := Circuit.eval_substVars (g n) m hgout (F₂ m) x
    have hfxlen : (f x).length = m := by
      simpa [m] using hflen x
    have hy : List.ofFn (fun i : Fin m => (g n i).eval x) = f x := by
      apply List.ext_getElem
      · simp [m, hfxlen]
      · intro i hi₁ hi₂
        have him : i < m := by simpa using hi₁
        have hbit := reductionBits_eval M p x i (by simpa [m, r] using him)
        have hbout : (boutputIn M (p.eval x.length) x).getD i false =
            (f x).getD i false := by
          simpa [n] using congrArg (fun w : Word => w.getD i false) (hout x)
        have hleft : (List.ofFn (fun j : Fin m => (g n j.val).eval x))[i] =
            (g n i).eval x := by
          simp
        have hright : (f x)[i] = (f x).getD i false := by
          simpa using (List.getD_eq_getElem (f x) false hi₂).symm
        rw [hleft, hright]
        exact hbit.trans hbout
    have hEval : (F₁ n).eval x = (F₂ m).eval (f x) := by
      dsimp [F₁]
      rw [hcomp]
      rw [hy]
    have hF₂m : ((F₂ m).eval (f x) = true ↔ f x ∈ L₂) := by
      simpa [hfxlen] using hF₂correct (f x)
    constructor
    · intro htrue
      have ht : (F₂ m).eval (f x) = true := by
        rwa [hEval] at htrue
      exact (hrediff x).1 (hF₂m.1 ht)
    · intro hx
      have ht : (F₂ m).eval (f x) = true :=
        hF₂m.2 ((hrediff x).2 hx)
      rwa [hEval]

/-- Cook-Levin for this SAT encoding, packaged as NP-completeness. -/
def SATNPComplete : Prop := NPComplete SAT

/-- Under the standard closure fact, the abstract and concrete lower bounds
    are equivalent: some NP language is outside P/poly iff SAT is. -/
theorem NPNotInPPoly_iff_SATNotInPPoly (hc : SATNPComplete) :
    NPNotInPPoly ↔ SATNotInPPoly := by
  constructor
  · intro hNP hSAT
    rcases hNP with ⟨L, hLNP, hLnot⟩
    exact hLnot (pPolyClosedUnderReductions L SAT hSAT (hc.2 L hLNP))
  · intro hSAT
    exact ⟨SAT, hc.1, hSAT⟩

/-- Final concrete route using NP-completeness of SAT. -/
theorem SATNPComplete_and_not_PPoly_implies_not_PEqualsNP (hc : SATNPComplete) :
    SATNotInPPoly → ¬ PEqualsNP := by
  intro hlow
  exact NPNotInPPoly_implies_not_PEqualsNP ⟨SAT, hc.1, hlow⟩

/-- If an NP-complete language is in P, then every NP language is in P/poly.
    This avoids a separate machine-composition theorem by using the already
    proved circuit-level closure of P/poly under reductions. -/
theorem NPComplete_in_P_implies_NP_subset_PPoly {L : Language}
    (hc : NPComplete L) (hL : InP L) :
    ∀ L' : Language, InNP L' → InPPoly L' := by
  intro L' hL'
  exact pPolyClosedUnderReductions L' L
    (P_subset_PPoly_unconditional L hL) (hc.2 L' hL')

/-- Specialization to SAT. -/
theorem SAT_in_P_implies_NP_subset_PPoly (hc : SATNPComplete) (hSAT : InP SAT) :
    ∀ L : Language, InNP L → InPPoly L :=
  NPComplete_in_P_implies_NP_subset_PPoly hc hSAT

/-- Consequently, SAT in P contradicts the concrete lower-bound hypothesis. -/
theorem SAT_in_P_implies_not_SATNotInPPoly (hSAT : InP SAT) : ¬ SATNotInPPoly := by
  intro hlow
  exact hlow (P_subset_PPoly_unconditional SAT hSAT)

-- -----------------------------------------------------------------------------
-- 12. Tseitin translation: a polynomial-size bridge from circuits to SAT
-- -----------------------------------------------------------------------------

/-- A computable list version of insertion into a finite set. -/
def tseitinInsert {α : Type} [DecidableEq α] (a : α) : List α → List α
  | [] => [a]
  | b :: bs => if a = b then b :: bs else b :: tseitinInsert a bs

lemma mem_tseitinInsert {α : Type} [DecidableEq α] {a b : α} {l : List α} :
    b ∈ tseitinInsert a l ↔ b = a ∨ b ∈ l := by
  induction l with
  | nil => simp [tseitinInsert]
  | cons c cs ih =>
      by_cases hac : a = c
      · subst c
        simp [tseitinInsert]
      · simp [tseitinInsert, hac, ih, or_left_comm]

lemma nodup_tseitinInsert {α : Type} [DecidableEq α] {a : α} {l : List α}
    (hl : l.Nodup) : (tseitinInsert a l).Nodup := by
  induction l with
  | nil => simp [tseitinInsert]
  | cons c cs ih =>
      by_cases hac : a = c
      · subst c
        simp [tseitinInsert, hl]
      · have hparts : c ∉ cs ∧ cs.Nodup := by simpa using hl
        have hcs : cs.Nodup := hparts.2
        have hcnot : c ∉ tseitinInsert a cs := by
          intro hc
          rcases (mem_tseitinInsert.1 hc) with hca | hccs
          · exact hac hca.symm
          · exact hparts.1 hccs
        have hnodup := ih hcs
        simp [tseitinInsert, hac, hnodup, hcnot]

/-- A computable list version of union for finite sets. -/
def tseitinUnion {α : Type} [DecidableEq α] : List α → List α → List α
  | [], l => l
  | a :: as, l => tseitinUnion as (tseitinInsert a l)

lemma mem_tseitinUnion {α : Type} [DecidableEq α] {a : α} {l₁ l₂ : List α} :
    a ∈ tseitinUnion l₁ l₂ ↔ a ∈ l₁ ∨ a ∈ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp [tseitinUnion]
  | cons b bs ih =>
      simp [tseitinUnion, ih, mem_tseitinInsert, or_assoc, or_left_comm]

lemma nodup_tseitinUnion {α : Type} [DecidableEq α] {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) : (tseitinUnion l₁ l₂).Nodup := by
  induction l₁ generalizing l₂ with
  | nil => simpa [tseitinUnion] using h₂
  | cons b bs ih =>
      have hbs : bs.Nodup := (by simpa using h₁ : b ∉ bs ∧ bs.Nodup).2
      exact ih hbs (nodup_tseitinInsert h₂)

namespace Circuit

/-- A computable duplicate-free enumeration of the distinct circuit nodes. -/
def nodesList : Circuit → List Circuit
  | const b => [const b]
  | var i => [var i]
  | not c => tseitinInsert (not c) c.nodesList
  | and c₁ c₂ => tseitinInsert (and c₁ c₂) (tseitinUnion c₁.nodesList c₂.nodesList)
  | or c₁ c₂ => tseitinInsert (or c₁ c₂) (tseitinUnion c₁.nodesList c₂.nodesList)

lemma mem_nodesList {c n : Circuit} : n ∈ c.nodesList ↔ n ∈ c.nodes := by
  induction c with
  | const b => simp [nodesList, nodes]
  | var i => simp [nodesList, nodes]
  | not c ih => simp [nodesList, nodes, mem_tseitinInsert, ih]
  | and c₁ c₂ ih1 ih2 =>
      simp [nodesList, nodes, mem_tseitinInsert, mem_tseitinUnion, ih1, ih2]
  | or c₁ c₂ ih1 ih2 =>
      simp [nodesList, nodes, mem_tseitinInsert, mem_tseitinUnion, ih1, ih2]

lemma nodup_nodesList (c : Circuit) : c.nodesList.Nodup := by
  induction c with
  | const b => simp [nodesList]
  | var i => simp [nodesList]
  | not c ih => exact nodup_tseitinInsert ih
  | and c₁ c₂ ih1 ih2 =>
      exact nodup_tseitinInsert (nodup_tseitinUnion ih1 ih2)
  | or c₁ c₂ ih1 ih2 =>
      exact nodup_tseitinInsert (nodup_tseitinUnion ih1 ih2)

lemma length_nodesList (c : Circuit) : c.nodesList.length = c.size := by
  have hfinset : c.nodesList.toFinset = c.nodes := by
    ext n
    simp [mem_nodesList]
  have hcard := congrArg Finset.card hfinset
  rw [List.toFinset_card_of_nodup (nodup_nodesList c)] at hcard
  simpa [Circuit.size] using hcard

lemma ne_not (c : Circuit) : c ≠ not c := by
  intro h
  cases h

lemma ne_and_left (c₁ c₂ : Circuit) : c₁ ≠ and c₁ c₂ := by
  intro h
  cases h

lemma ne_and_right (c₁ c₂ : Circuit) : c₂ ≠ and c₁ c₂ := by
  intro h
  cases h

lemma ne_or_left (c₁ c₂ : Circuit) : c₁ ≠ or c₁ c₂ := by
  intro h
  cases h

lemma ne_or_right (c₁ c₂ : Circuit) : c₂ ≠ or c₁ c₂ := by
  intro h
  cases h

lemma mem_nodes_trans {c n m : Circuit} (hn : n ∈ c.nodes) (hm : m ∈ n.nodes) :
    m ∈ c.nodes := by
  induction c generalizing n m with
  | const b =>
      have hnb : n = const b := by simpa [nodes] using hn
      subst n
      simpa using hm
  | var i =>
      have hni : n = var i := by simpa [nodes] using hn
      subst n
      have hmi : m = var i := by simpa [nodes] using hm
      subst m
      simp [nodes]
  | not d ih =>
      simp [nodes] at hn
      rcases hn with hnd | hnd
      · subst n
        simpa [nodes] using hm
      · have hmd : m ∈ d.nodes := ih hnd hm
        exact Finset.mem_insert_of_mem hmd
  | and d e ihd ihe =>
      simp [nodes] at hn
      rcases hn with rfl | hnd | hne
      · simpa using hm
      · have hmd : m ∈ d.nodes := ihd hnd hm
        simp [nodes, hmd]
      · have hme : m ∈ e.nodes := ihe hne hm
        simp [nodes, hme]
  | or d e ihd ihe =>
      simp [nodes] at hn
      rcases hn with rfl | hnd | hne
      · simpa using hm
      · have hmd : m ∈ d.nodes := ihd hnd hm
        simp [nodes, hmd]
      · have hme : m ∈ e.nodes := ihe hne hm
        simp [nodes, hme]

lemma var_mem_nodes_le_maxVar {c : Circuit} {i : Nat} (hi : var i ∈ c.nodes) :
    i ≤ c.maxVar := by
  induction c with
  | const b => simp [nodes] at hi
  | var j =>
      have hij : i = j := by simpa [nodes] using hi
      subst i
      simp [maxVar]
  | not d ih =>
      have hd : var i ∈ d.nodes := by simpa [nodes] using hi
      simpa [maxVar] using ih hd
  | and d e ihd ihe =>
      simp [nodes] at hi
      rcases hi with hd | he
      · exact Nat.le_trans (ihd hd) (Nat.le_max_left _ _)
      · exact Nat.le_trans (ihe he) (Nat.le_max_right _ _)
  | or d e ihd ihe =>
      simp [nodes] at hi
      rcases hi with hd | he
      · exact Nat.le_trans (ihd hd) (Nat.le_max_left _ _)
      · exact Nat.le_trans (ihe he) (Nat.le_max_right _ _)

end Circuit

/-- Fresh variables start just after the largest original input variable. -/
def auxOffset (c : Circuit) : Nat := c.maxVar + 1

/-- The index of a node in the sharing-aware list of distinct nodes. -/
def auxIndex (c n : Circuit) : Nat := c.nodesList.idxOf n

/-- The fresh Boolean variable associated with a circuit node. -/
def auxVar (c n : Circuit) : Nat := auxOffset c + auxIndex c n

lemma auxIndex_lt {c n : Circuit} (hn : n ∈ c.nodes) : auxIndex c n < c.size := by
  dsimp [auxIndex]
  rw [← Circuit.length_nodesList c]
  exact List.idxOf_lt_length_iff.2 ((Circuit.mem_nodesList).2 hn)

lemma auxOffset_le_auxVar (c n : Circuit) : auxOffset c ≤ auxVar c n := by
  simp [auxVar]

lemma auxVar_lt (c n : Circuit) (hn : n ∈ c.nodes) :
    auxVar c n < auxOffset c + c.size := by
  exact Nat.add_lt_add_left (auxIndex_lt hn) (auxOffset c)

lemma auxVar_injective {c n m : Circuit} (hn : n ∈ c.nodes) (_hm : m ∈ c.nodes)
    (h : auxVar c n = auxVar c m) : n = m := by
  have hidx : auxIndex c n = auxIndex c m := by
    unfold auxVar at h
    exact Nat.add_left_cancel h
  unfold auxIndex at hidx
  exact (List.idxOf_inj ((Circuit.mem_nodesList).2 hn)).1 hidx

/-- Recover a node from the index used by its fresh variable. -/
def nodeOfIndex (c : Circuit) (k : Nat) : Circuit :=
  c.nodesList.getD k (Circuit.const false)

lemma nodeOfIndex_auxIndex {c n : Circuit} (hn : n ∈ c.nodes) :
    nodeOfIndex c (auxIndex c n) = n := by
  unfold nodeOfIndex auxIndex
  rw [List.getD_eq_getElem c.nodesList (Circuit.const false)
    (List.idxOf_lt_length_iff.2 ((Circuit.mem_nodesList).2 hn))]
  exact List.getElem_idxOf (List.idxOf_lt_length_iff.2 ((Circuit.mem_nodesList).2 hn))

/-- An assignment to the original input variables extended to fresh node
    variables by evaluating the corresponding node. -/
def tseitinAssignment (c : Circuit) (x : Word) (i : Nat) : Bool :=
  if _h : i < auxOffset c then x.getD i false
  else (nodeOfIndex c (i - auxOffset c)).eval x

lemma tseitinAssignment_aux {c n : Circuit} (hn : n ∈ c.nodes) (x : Word) :
    tseitinAssignment c x (auxVar c n) = n.eval x := by
  unfold tseitinAssignment auxVar
  have hnot : ¬auxOffset c + auxIndex c n < auxOffset c := by omega
  simp [hnot, nodeOfIndex_auxIndex hn]

lemma tseitinAssignment_input (c : Circuit) (x : Word) (i : Nat)
    (hi : i ≤ c.maxVar) : tseitinAssignment c x i = x.getD i false := by
  unfold tseitinAssignment auxOffset
  simp [Nat.lt_succ_of_le hi]

/-- The literal for the fresh variable of a node. -/
def nodeLit (c n : Circuit) : Formula := Formula.var (auxVar c n)

/-- Local equivalence constraints for one distinct circuit node.  For a node
    `a` with children `b` and `d`, these clauses force `a ↔ evalOfNode`. -/
def tseitinConstraint (c : Circuit) : Circuit → Formula
  | Circuit.const b =>
      if b then nodeLit c (Circuit.const b) else Formula.not (nodeLit c (Circuit.const b))
  | Circuit.var i =>
      Formula.and
        (Formula.or (Formula.not (nodeLit c (Circuit.var i))) (Formula.var i))
        (Formula.or (nodeLit c (Circuit.var i)) (Formula.not (Formula.var i)))
  | Circuit.not d =>
      let a := nodeLit c (Circuit.not d)
      let b := nodeLit c d
      Formula.and
        (Formula.or (Formula.not a) (Formula.not b))
        (Formula.or a b)
  | Circuit.and d e =>
      let a := nodeLit c (Circuit.and d e)
      let b := nodeLit c d
      let d' := nodeLit c e
      Formula.and
        (Formula.and
          (Formula.or (Formula.not a) b)
          (Formula.or (Formula.not a) d'))
        (Formula.or (Formula.or a (Formula.not b)) (Formula.not d'))
  | Circuit.or d e =>
      let a := nodeLit c (Circuit.or d e)
      let b := nodeLit c d
      let d' := nodeLit c e
      Formula.and
        (Formula.and
          (Formula.or a (Formula.not b))
          (Formula.or a (Formula.not d')))
        (Formula.or (Formula.or (Formula.not a) b) d')

lemma node_mem_own_nodes (c : Circuit) : c ∈ c.nodes := by
  cases c <;> simp [Circuit.nodes]

lemma tseitinConstraint_eval_true (c : Circuit) (x : Word) (n : Circuit) (hn : n ∈ c.nodes) :
    (tseitinConstraint c n).eval (tseitinAssignment c x) = true := by
  cases n with
  | const b =>
      have ha := tseitinAssignment_aux (c := c) (n := Circuit.const b) hn x
      cases b <;> simp [tseitinConstraint, nodeLit, ha]
  | var i =>
      have hi_le : i ≤ c.maxVar := Circuit.var_mem_nodes_le_maxVar hn
      have ha := tseitinAssignment_aux (c := c) (n := Circuit.var i) hn x
      have hx_i := tseitinAssignment_input c x i hi_le
      simp [tseitinConstraint, nodeLit, ha, hx_i]
  | not d =>
      have hdmem : d ∈ c.nodes := Circuit.mem_nodes_trans hn (by simp [Circuit.nodes, Circuit.ne_not d, node_mem_own_nodes d])
      have ha := tseitinAssignment_aux (c := c) (n := Circuit.not d) hn x
      have hb := tseitinAssignment_aux (c := c) (n := d) hdmem x
      cases hdval : d.eval x <;>
        simp [tseitinConstraint, nodeLit, ha, hb, hdval]
  | and d e =>
      have hdmem : d ∈ c.nodes := Circuit.mem_nodes_trans hn (by simp [Circuit.nodes, Circuit.ne_and_left d e, node_mem_own_nodes d])
      have hemem : e ∈ c.nodes := Circuit.mem_nodes_trans hn (by simp [Circuit.nodes, Circuit.ne_and_right d e, node_mem_own_nodes e])
      have ha := tseitinAssignment_aux (c := c) (n := Circuit.and d e) hn x
      have hb := tseitinAssignment_aux (c := c) (n := d) hdmem x
      have hd' := tseitinAssignment_aux (c := c) (n := e) hemem x
      cases hdval : d.eval x <;> cases heval : e.eval x <;>
        simp [tseitinConstraint, nodeLit, ha, hb, hd', hdval, heval]
  | or d e =>
      have hdmem : d ∈ c.nodes := Circuit.mem_nodes_trans hn (by simp [Circuit.nodes, Circuit.ne_or_left d e, node_mem_own_nodes d])
      have hemem : e ∈ c.nodes := Circuit.mem_nodes_trans hn (by simp [Circuit.nodes, Circuit.ne_or_right d e, node_mem_own_nodes e])
      have ha := tseitinAssignment_aux (c := c) (n := Circuit.or d e) hn x
      have hb := tseitinAssignment_aux (c := c) (n := d) hdmem x
      have hd' := tseitinAssignment_aux (c := c) (n := e) hemem x
      cases hdval : d.eval x <;> cases heval : e.eval x <;>
        simp [tseitinConstraint, nodeLit, ha, hb, hd', hdval, heval]

/-- Conjoin a finite list of formulas. -/
def andMany : List Formula → Formula
  | [] => Formula.trueFormula
  | f :: fs => Formula.and f (andMany fs)

lemma andMany_eval_true_iff (fs : List Formula) (a : Nat → Bool) :
    (andMany fs).eval a = true ↔ ∀ f ∈ fs, f.eval a = true := by
  induction fs with
  | nil => simp [andMany]
  | cons f fs ih =>
      cases hf : f.eval a <;> simp [andMany, hf, ih]

/-- Conjoin all constraints for a circuit. -/
def tseitinConstraints (c : Circuit) : List Formula :=
  c.nodesList.map (fun n => tseitinConstraint c n)

/-- The Tseitin formula adds one fresh variable for every distinct circuit node
    and constrains each such variable to agree with the node's value. -/
def tseitinFormula (c : Circuit) : Formula :=
  Formula.and (andMany (tseitinConstraints c)) (Formula.var (auxVar c c))

lemma tseitinFormula_eval_eq_true_of_eval_true (c : Circuit) (x : Word)
    (h : c.eval x = true) :
    (tseitinFormula c).eval (tseitinAssignment c x) = true := by
  simp only [tseitinFormula, Formula.eval_and, Formula.eval_var, Bool.and_eq_true]
  constructor
  · rw [andMany_eval_true_iff]
    intro n hn
    rcases List.mem_map.1 hn with ⟨m, hm, rfl⟩
    exact tseitinConstraint_eval_true c x m ((Circuit.mem_nodesList).1 hm)
  · rw [tseitinAssignment_aux (node_mem_own_nodes c) x, h]

lemma tseitinFormula_mem_SAT_of_eval_true (c : Circuit) (x : Word)
    (h : c.eval x = true) : (tseitinFormula c).encode ∈ SAT := by
  exact Formula.mem_SAT_of_eval_true (tseitinFormula c) (tseitinAssignment c x)
    (tseitinFormula_eval_eq_true_of_eval_true c x h)

lemma circuit_eval_true_of_tseitinFormula_eval_true {c : Circuit} {a : Nat → Bool}
    (ha : (tseitinFormula c).eval a = true) :
    c.eval (List.ofFn (fun i : Fin (c.maxVar + 1) => a i.val)) = true := by
  let x : Word := List.ofFn (fun i : Fin (c.maxVar + 1) => a i.val)
  have hxget (i : Nat) (hi : i ≤ c.maxVar) : x.getD i false = a i := by
    dsimp [x]
    rw [List.getD_eq_getElem (List.ofFn (fun j : Fin (c.maxVar + 1) => a j.val)) false
      (by simpa using Nat.lt_succ_of_le hi)]
    rw [List.getElem_ofFn (i := i)
      (f := fun j : Fin (c.maxVar + 1) => a j.val)
      (by simpa using Nat.lt_succ_of_le hi)]
  have hall : ∀ n ∈ c.nodes, (tseitinConstraint c n).eval a = true := by
    intro n hn
    have hparts : (andMany (tseitinConstraints c)).eval a = true ∧
        a (auxVar c c) = true := by
      simpa [tseitinFormula] using ha
    have hforall := (andMany_eval_true_iff (tseitinConstraints c) a).1 hparts.1
    exact hforall (tseitinConstraint c n)
      (List.mem_map.2 ⟨n, (Circuit.mem_nodesList).2 hn, rfl⟩)
  have hnode : ∀ n ∈ c.nodes, a (auxVar c n) = n.eval x := by
    intro n hn
    induction n with
    | const b =>
        have hc := hall (Circuit.const b) hn
        cases b <;> simpa [tseitinConstraint, nodeLit] using hc
    | var i =>
        have hi_le : i ≤ c.maxVar := Circuit.var_mem_nodes_le_maxVar hn
        have hxi : x.getD i false = a i := hxget i hi_le
        have hc := hall (Circuit.var i) hn
        change a (auxVar c (Circuit.var i)) = x.getD i false
        rw [hxi]
        cases hai : a (auxVar c (Circuit.var i)) <;> cases hvi : a i <;>
          simp [tseitinConstraint, nodeLit, hai, hvi] at hc ⊢
    | not d ih =>
        have hdmem : d ∈ c.nodes := Circuit.mem_nodes_trans hn (by simp [Circuit.nodes, Circuit.ne_not d, node_mem_own_nodes d])
        have hc := hall (Circuit.not d) hn
        have hdval := ih hdmem
        cases hself : a (auxVar c (Circuit.not d)) <;> cases hd : d.eval x <;>
          simp [tseitinConstraint, nodeLit, hself, hd, hdval] at hc ⊢
    | and d e ihd ihe =>
        have hdmem : d ∈ c.nodes := Circuit.mem_nodes_trans hn (by simp [Circuit.nodes, Circuit.ne_and_left d e, node_mem_own_nodes d])
        have hemem : e ∈ c.nodes := Circuit.mem_nodes_trans hn (by simp [Circuit.nodes, Circuit.ne_and_right d e, node_mem_own_nodes e])
        have hc := hall (Circuit.and d e) hn
        have hdval := ihd hdmem
        have heval := ihe hemem
        cases hself : a (auxVar c (Circuit.and d e)) <;> cases hd : d.eval x <;>
          cases he : e.eval x <;>
          simp [tseitinConstraint, nodeLit, hself, hd, he, hdval, heval] at hc ⊢
    | or d e ihd ihe =>
        have hdmem : d ∈ c.nodes := Circuit.mem_nodes_trans hn (by simp [Circuit.nodes, Circuit.ne_or_left d e, node_mem_own_nodes d])
        have hemem : e ∈ c.nodes := Circuit.mem_nodes_trans hn (by simp [Circuit.nodes, Circuit.ne_or_right d e, node_mem_own_nodes e])
        have hc := hall (Circuit.or d e) hn
        have hdval := ihd hdmem
        have heval := ihe hemem
        cases hself : a (auxVar c (Circuit.or d e)) <;> cases hd : d.eval x <;>
          cases he : e.eval x <;>
          simp [tseitinConstraint, nodeLit, hself, hd, he, hdval, heval] at hc ⊢
  rw [← hnode c (node_mem_own_nodes c)]
  have hparts : (andMany (tseitinConstraints c)).eval a = true ∧
      a (auxVar c c) = true := by
    simpa [tseitinFormula] using ha
  exact hparts.2

lemma eval_true_of_tseitinFormula_mem_SAT {c : Circuit}
    (hSAT : (tseitinFormula c).encode ∈ SAT) : ∃ x : Word, c.eval x = true := by
  rcases hSAT with ⟨f, hf, a, ha⟩
  have hfc : f = tseitinFormula c := Formula.encode_injective hf
  subst f
  exact ⟨List.ofFn (fun i : Fin (c.maxVar + 1) => a i.val),
    circuit_eval_true_of_tseitinFormula_eval_true ha⟩

theorem circuit_tseitin_SAT_iff (c : Circuit) :
    (∃ x : Word, c.eval x = true) ↔ (tseitinFormula c).encode ∈ SAT := by
  constructor
  · rintro ⟨x, hx⟩
    exact tseitinFormula_mem_SAT_of_eval_true c x hx
  · exact eval_true_of_tseitinFormula_mem_SAT

theorem Formula.sat_iff_tseitin_toCircuit (f : Formula) :
    (∃ a : Nat → Bool, f.eval a = true) ↔
      (tseitinFormula (Formula.toCircuit f)).encode ∈ SAT := by
  rw [Formula.toCircuit_sat_iff, circuit_tseitin_SAT_iff]

theorem Formula.mem_SAT_iff_tseitin_toCircuit (f : Formula) :
    f.encode ∈ SAT ↔ (tseitinFormula (Formula.toCircuit f)).encode ∈ SAT := by
  rw [Formula.mem_SAT_iff_sat, Formula.sat_iff_tseitin_toCircuit]

/-- A structural size measure for formulas, counted independently of variable
    index magnitude. -/
def formulaSize : Formula → Nat
  | Formula.var _ => 1
  | Formula.not f => 1 + formulaSize f
  | Formula.and f g => 1 + formulaSize f + formulaSize g
  | Formula.or f g => 1 + formulaSize f + formulaSize g

lemma Circuit.size_le_treeSize (c : Circuit) : c.size ≤ c.treeSize := by
  induction c with
  | const b => simp [Circuit.size, Circuit.treeSize, Circuit.nodes]
  | var i => simp [Circuit.size, Circuit.treeSize, Circuit.nodes]
  | not c ih =>
      exact le_trans (size_not c) (Nat.add_le_add_left ih 1)
  | and c₁ c₂ ih1 ih2 =>
      have h : 1 + c₁.size + c₂.size ≤ 1 + c₁.treeSize + c₂.treeSize := by omega
      exact le_trans (size_and c₁ c₂) (by simpa [Circuit.treeSize] using h)
  | or c₁ c₂ ih1 ih2 =>
      have h : 1 + c₁.size + c₂.size ≤ 1 + c₁.treeSize + c₂.treeSize := by omega
      exact le_trans (size_or c₁ c₂) (by simpa [Circuit.treeSize] using h)

lemma Formula.toCircuit_treeSize (f : Formula) :
    (Formula.toCircuit f).treeSize = formulaSize f := by
  induction f with
  | var i => simp [Formula.toCircuit, Circuit.treeSize, formulaSize]
  | not f ih => simp [Formula.toCircuit, Circuit.treeSize, formulaSize, ih]
  | and f g ihf ihg =>
      simp [Formula.toCircuit, Circuit.treeSize, formulaSize, ihf, ihg]
  | or f g ihf ihg =>
      simp [Formula.toCircuit, Circuit.treeSize, formulaSize, ihf, ihg]

lemma Formula.toCircuit_size_le_formulaSize (f : Formula) :
    (Formula.toCircuit f).size ≤ formulaSize f := by
  rw [← Formula.toCircuit_treeSize f]
  exact Circuit.size_le_treeSize (Formula.toCircuit f)

@[simp] lemma formulaSize_trueFormula : formulaSize Formula.trueFormula = 4 := by
  simp [Formula.trueFormula, formulaSize]

@[simp] lemma formulaSize_falseFormula : formulaSize Formula.falseFormula = 4 := by
  simp [Formula.falseFormula, formulaSize]

lemma formulaSize_andMany_le_of_bound (fs : List Formula) (B : Nat)
    (hB : ∀ f ∈ fs, formulaSize f ≤ B) :
    formulaSize (andMany fs) ≤ fs.length * (B + 1) + 4 := by
  induction fs with
  | nil => simp [andMany]
  | cons f fs ih =>
      have hf : formulaSize f ≤ B := hB f (by simp)
      have hfs : ∀ g ∈ fs, formulaSize g ≤ B := by
        intro g hg
        exact hB g (by simp [hg])
      have ih' := ih hfs
      dsimp [andMany, formulaSize]
      simp [Nat.add_mul, Nat.mul_add] at ih' ⊢
      omega

lemma encode_length_le_formulaSize (f : Formula) :
    f.encode.length ≤ (f.maxVar + 3) * formulaSize f := by
  induction f with
  | var i =>
      simp [Formula.encode, Formula.encodeNat_length, Formula.maxVar, formulaSize]
  | not f ih =>
      have h2 : 2 ≤ f.maxVar + 3 := by omega
      have hstep : f.encode.length + 1 + 1 ≤ 2 + (f.maxVar + 3) * formulaSize f := by omega
      have hadd : 2 + (f.maxVar + 3) * formulaSize f ≤
          (f.maxVar + 3) + (f.maxVar + 3) * formulaSize f :=
        Nat.add_le_add_right h2 ((f.maxVar + 3) * formulaSize f)
      dsimp [Formula.encode, Formula.maxVar, formulaSize]
      change f.encode.length + 1 + 1 ≤ (f.maxVar + 3) * (1 + formulaSize f)
      exact le_trans hstep (by simp [Nat.mul_add] at hadd ⊢)
  | and f g ihf ihg =>
      let A := f.maxVar + 3
      let B := g.maxVar + 3
      let C := max f.maxVar g.maxVar + 3
      have hAf : A ≤ C := by
        dsimp [A, C]
        omega
      have hBg : B ≤ C := by
        dsimp [B, C]
        omega
      have hf' : f.encode.length ≤ C * formulaSize f := le_trans ihf (Nat.mul_le_mul_right (formulaSize f) hAf)
      have hg' : g.encode.length ≤ C * formulaSize g := le_trans ihg (Nat.mul_le_mul_right (formulaSize g) hBg)
      have h2 : 2 ≤ C := by dsimp [C]; omega
      have hstep : 2 + f.encode.length + g.encode.length ≤
          2 + C * formulaSize f + C * formulaSize g := by omega
      have hstep' : f.encode.length + g.encode.length + 1 + 1 ≤
          2 + C * formulaSize f + C * formulaSize g := by omega
      have hadd : 2 + C * formulaSize f + C * formulaSize g ≤
          C + C * formulaSize f + C * formulaSize g := by omega
      dsimp [Formula.encode, Formula.maxVar, formulaSize]
      rw [List.length_append]
      change f.encode.length + g.encode.length + 1 + 1 ≤ C * (1 + formulaSize f + formulaSize g)
      exact le_trans hstep' (by
        simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hadd)
  | or f g ihf ihg =>
      let A := f.maxVar + 3
      let B := g.maxVar + 3
      let C := max f.maxVar g.maxVar + 3
      have hAf : A ≤ C := by
        dsimp [A, C]
        omega
      have hBg : B ≤ C := by
        dsimp [B, C]
        omega
      have hf' : f.encode.length ≤ C * formulaSize f := le_trans ihf (Nat.mul_le_mul_right (formulaSize f) hAf)
      have hg' : g.encode.length ≤ C * formulaSize g := le_trans ihg (Nat.mul_le_mul_right (formulaSize g) hBg)
      have h2 : 2 ≤ C := by dsimp [C]; omega
      have hstep : 2 + f.encode.length + g.encode.length ≤
          2 + C * formulaSize f + C * formulaSize g := by omega
      have hstep' : f.encode.length + g.encode.length + 1 + 1 ≤
          2 + C * formulaSize f + C * formulaSize g := by omega
      have hadd : 2 + C * formulaSize f + C * formulaSize g ≤
          C + C * formulaSize f + C * formulaSize g := by omega
      dsimp [Formula.encode, Formula.maxVar, formulaSize]
      rw [List.length_append]
      change f.encode.length + g.encode.length + 1 + 1 ≤ C * (1 + formulaSize f + formulaSize g)
      exact le_trans hstep' (by
        simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hadd)

lemma tseitinConstraint_formulaSize_le (c n : Circuit) :
    formulaSize (tseitinConstraint c n) ≤ 20 := by
  cases n with
  | const b => cases b <;> simp [tseitinConstraint, nodeLit, formulaSize]
  | var i => simp [tseitinConstraint, nodeLit, formulaSize]
  | not d => simp [tseitinConstraint, nodeLit, formulaSize]
  | and d e => simp [tseitinConstraint, nodeLit, formulaSize]
  | or d e => simp [tseitinConstraint, nodeLit, formulaSize]

lemma length_tseitinConstraints (c : Circuit) : (tseitinConstraints c).length = c.size := by
  simp [tseitinConstraints, Circuit.length_nodesList]

lemma formulaSize_tseitinFormula_le (c : Circuit) :
    formulaSize (tseitinFormula c) ≤ 30 * c.size + 10 := by
  have hB : ∀ f ∈ tseitinConstraints c, formulaSize f ≤ 20 := by
    intro f hf
    rcases List.mem_map.1 hf with ⟨n, hn, rfl⟩
    exact tseitinConstraint_formulaSize_le c n
  have hAnd := formulaSize_andMany_le_of_bound (tseitinConstraints c) 20 hB
  have hlen := length_tseitinConstraints c
  dsimp [tseitinFormula, formulaSize]
  omega

lemma maxVar_andMany_le_of_bound (fs : List Formula) (B : Nat)
    (hB : ∀ f ∈ fs, f.maxVar ≤ B) : (andMany fs).maxVar ≤ B := by
  induction fs with
  | nil => simp [andMany, Formula.trueFormula, Formula.maxVar]
  | cons f fs ih =>
      dsimp [andMany, Formula.maxVar]
      exact max_le (hB f (by simp)) (ih (by
        intro g hg
        exact hB g (by simp [hg])))

lemma maxVar_nodeLit_le {c n : Circuit} (hn : n ∈ c.nodes) :
    (nodeLit c n).maxVar ≤ auxOffset c + c.size := by
  dsimp [nodeLit, Formula.maxVar]
  exact Nat.le_of_lt (auxVar_lt c n hn)

lemma tseitinConstraint_maxVar_le (c n : Circuit) (hn : n ∈ c.nodes) :
    (tseitinConstraint c n).maxVar ≤ auxOffset c + c.size := by
  cases n with
  | const b =>
      cases b
      · simpa [tseitinConstraint, Formula.maxVar] using (maxVar_nodeLit_le (c := c) (n := Circuit.const false) hn)
      · simpa [tseitinConstraint, Formula.maxVar] using (maxVar_nodeLit_le (c := c) (n := Circuit.const true) hn)
  | var i =>
      have hi0 : i ≤ c.maxVar := Circuit.var_mem_nodes_le_maxVar hn
      have hi : i ≤ auxOffset c + c.size := by
        dsimp [auxOffset]
        omega
      have ha := maxVar_nodeLit_le (c := c) (n := Circuit.var i) hn
      have ha' : auxVar c (Circuit.var i) ≤ auxOffset c + c.size := by
        simpa [nodeLit, Formula.maxVar] using ha
      simpa [tseitinConstraint, Formula.maxVar, nodeLit] using max_le ha' hi
  | not d =>
      have hdmem : d ∈ c.nodes := Circuit.mem_nodes_trans hn (by simp [Circuit.nodes, Circuit.ne_not d, node_mem_own_nodes d])
      have ha := maxVar_nodeLit_le (c := c) (n := Circuit.not d) hn
      have hb := maxVar_nodeLit_le (c := c) (n := d) hdmem
      simpa [tseitinConstraint, Formula.maxVar, nodeLit] using max_le ha hb
  | and d e =>
      have hdmem : d ∈ c.nodes := Circuit.mem_nodes_trans hn (by simp [Circuit.nodes, Circuit.ne_and_left d e, node_mem_own_nodes d])
      have hemem : e ∈ c.nodes := Circuit.mem_nodes_trans hn (by simp [Circuit.nodes, Circuit.ne_and_right d e, node_mem_own_nodes e])
      have ha := maxVar_nodeLit_le (c := c) (n := Circuit.and d e) hn
      have hb := maxVar_nodeLit_le (c := c) (n := d) hdmem
      have hd := maxVar_nodeLit_le (c := c) (n := e) hemem
      simpa [tseitinConstraint, Formula.maxVar, nodeLit] using max_le ha (max_le hb hd)
  | or d e =>
      have hdmem : d ∈ c.nodes := Circuit.mem_nodes_trans hn (by simp [Circuit.nodes, Circuit.ne_or_left d e, node_mem_own_nodes d])
      have hemem : e ∈ c.nodes := Circuit.mem_nodes_trans hn (by simp [Circuit.nodes, Circuit.ne_or_right d e, node_mem_own_nodes e])
      have ha := maxVar_nodeLit_le (c := c) (n := Circuit.or d e) hn
      have hb := maxVar_nodeLit_le (c := c) (n := d) hdmem
      have hd := maxVar_nodeLit_le (c := c) (n := e) hemem
      simpa [tseitinConstraint, Formula.maxVar, nodeLit] using max_le ha (max_le hb hd)

lemma tseitinFormula_maxVar_le (c : Circuit) :
    (tseitinFormula c).maxVar ≤ auxOffset c + c.size := by
  have hB : ∀ f ∈ tseitinConstraints c, f.maxVar ≤ auxOffset c + c.size := by
    intro f hf
    rcases List.mem_map.1 hf with ⟨n, hn, rfl⟩
    exact tseitinConstraint_maxVar_le c n ((Circuit.mem_nodesList).1 hn)
  have hAnd := maxVar_andMany_le_of_bound (tseitinConstraints c) (auxOffset c + c.size) hB
  have hOut := maxVar_nodeLit_le (c := c) (n := c) (node_mem_own_nodes c)
  dsimp [tseitinFormula, nodeLit] at hOut ⊢
  exact max_le hAnd hOut

/-- The bounded SAT certificate obtained from a circuit-satisfying input. -/
def tseitinCertificate (c : Circuit) (x : Word) : Word :=
  List.ofFn (fun i : Fin ((tseitinFormula c).maxVar + 1) =>
    tseitinAssignment c x i.val)

@[simp] lemma tseitinCertificate_length (c : Circuit) (x : Word) :
    (tseitinCertificate c x).length = (tseitinFormula c).maxVar + 1 := by
  simp [tseitinCertificate]

lemma tseitinCertificate_verifies (c : Circuit) (x : Word)
    (h : c.eval x = true) :
    (tseitinFormula c).eval ((tseitinFormula c).assign
      (Formula.assignOfWord (tseitinFormula c) (tseitinCertificate c x))) = true := by
  let f := tseitinFormula c
  have hbase : f.eval (tseitinAssignment c x) = true := by
    exact tseitinFormula_eval_eq_true_of_eval_true c x h
  have hagree : ∀ i, i ∈ f.vars →
      f.assign (Formula.assignOfWord f (tseitinCertificate c x)) i =
        tseitinAssignment c x i := by
    intro i hi
    have hle : i ≤ f.maxVar := Formula.mem_vars_le_maxVar hi
    rw [Formula.assign_agree f _ i (Nat.lt_succ_of_le hle)]
    dsimp [tseitinCertificate, Formula.assignOfWord]
    rw [List.getD_eq_getElem (List.ofFn (fun j : Fin (f.maxVar + 1) => tseitinAssignment c x j.val)) false
      (by simpa using Nat.lt_succ_of_le hle)]
    rw [List.getElem_ofFn (i := i)
      (f := fun j : Fin (f.maxVar + 1) => tseitinAssignment c x j.val)
      (by simpa using Nat.lt_succ_of_le hle)]
  rw [Formula.eval_eq_of_agree_on_vars_finset f hagree]
  exact hbase

theorem tseitin_encode_length_le (c : Circuit) :
    (tseitinFormula c).encode.length ≤
      (auxOffset c + c.size + 3) * (30 * c.size + 10) := by
  have hen := encode_length_le_formulaSize (tseitinFormula c)
  have hmv := tseitinFormula_maxVar_le c
  have hsz := formulaSize_tseitinFormula_le c
  have hmv' : (tseitinFormula c).maxVar + 3 ≤ auxOffset c + c.size + 3 := by omega
  have hmul := Nat.mul_le_mul hmv' hsz
  exact le_trans hen hmul

/-- A polynomial witness for the Tseitin encoding blow-up. -/
noncomputable def tseitinPoly : TimeBound :=
  (C 2 * X + C 4) * (C 30 * X + C 10)

lemma tseitin_encode_length_le_poly (c : Circuit) :
    (tseitinFormula c).encode.length ≤ tseitinPoly.eval (c.size + c.maxVar) := by
  let N := c.size + c.maxVar
  have h := tseitin_encode_length_le c
  have h1 : auxOffset c + c.size + 3 ≤ 2 * N + 4 := by
    dsimp [auxOffset, N]
    omega
  have h2 : 30 * c.size + 10 ≤ 30 * N + 10 := by
    dsimp [N]
    omega
  have hmul := Nat.mul_le_mul h1 h2
  dsimp [tseitinPoly, N]
  simpa using (le_trans h hmul)

lemma Formula.tseitin_encode_length_le_poly (f : Formula) :
    (tseitinFormula (Formula.toCircuit f)).encode.length ≤
      tseitinPoly.eval (formulaSize f + f.maxVar) := by
  have h := PNP.tseitin_encode_length_le_poly (Formula.toCircuit f)
  have hs := Formula.toCircuit_size_le_formulaSize f
  have hm := Formula.toCircuit_maxVar_le f
  have hsum : (Formula.toCircuit f).size + (Formula.toCircuit f).maxVar ≤
      formulaSize f + f.maxVar := Nat.add_le_add hs hm
  exact le_trans h (timeBound_eval_monotone tseitinPoly hsum)

lemma tseitinCertificate_length_le_poly (c : Circuit) (x : Word) :
    (tseitinCertificate c x).length ≤ tseitinPoly.eval (c.size + c.maxVar) := by
  have hlen := tseitinCertificate_length c x
  have hlt := Formula.maxVar_lt_encode_length (tseitinFormula c)
  have hp := tseitin_encode_length_le_poly c
  omega

lemma npInitBits_size_bound (M : TM) (t m : Nat) (n : Word) :
    (npInitBits M t m n).size ≤ M.numStates + 2 * (2 * t + 1) := by
  have hnodes := SimBits.nodes_le_sum_size (npInitBits M t m n)
  have hstate :
      (∑ q : Fin M.numStates, ((npInitBits M t m n).state q).size) ≤
        M.numStates := by
    have h := sum_le_card_mul (Finset.univ : Finset (Fin M.numStates))
      (fun q => ((npInitBits M t m n).state q).size) 1 (by
        intro q hq
        simp [npInitBits])
    simpa using h
  have hhead :
      (∑ i : Fin (2 * t + 1), ((npInitBits M t m n).head i).size) ≤
        2 * t + 1 := by
    have h := sum_le_card_mul (Finset.univ : Finset (Fin (2 * t + 1)))
      (fun i => ((npInitBits M t m n).head i).size) 1 (by
        intro i hi
        simp [npInitBits])
    simpa using h
  have htape :
      (∑ i : Fin (2 * t + 1), ((npInitBits M t m n).tape i).size) ≤
        2 * t + 1 := by
    have h := sum_le_card_mul (Finset.univ : Finset (Fin (2 * t + 1)))
      (fun i => ((npInitBits M t m n).tape i).size) 1 (by
        intro i hi
        dsimp [npInitBits]
        by_cases h1 : t ≤ i.val ∧ i.val < t + n.length
        · rw [ite_eq_left h1]
          simp
        · rw [ite_eq_right h1]
          by_cases h2 : t + n.length ≤ i.val ∧ i.val < t + n.length + m <;>
            simp [h2])
    simpa using h
  omega

lemma unrollBitsFrom_size_bound (V : TM) (t m s : Nat) (x : Word) :
    (unrollBitsFrom V t (npInitBits V t m x) s).size ≤
      (V.numStates + 2 * (2 * t + 1)) + s * stepRelBound V t := by
  induction s with
  | zero =>
      dsimp [unrollBitsFrom]
      simpa using (npInitBits_size_bound V t m x)
  | succ s ih =>
      dsimp [unrollBitsFrom]
      have hstep := stepBits_size_bound V t (unrollBitsFrom V t (npInitBits V t m x) s)
      have hsucc : (s + 1) * stepRelBound V t = s * stepRelBound V t + stepRelBound V t := by
        simp [Nat.succ_mul]
      rw [hsucc]
      omega

lemma npVerifierCircuit_size_bound (V : TM) (p q : TimeBound) (x : Word) :
    (npVerifierCircuit V p q x).size ≤
      (V.numStates + 2 * (2 * p.eval (x.length + q.eval x.length) + 1)) +
        p.eval (x.length + q.eval x.length) *
          stepRelBound V (p.eval (x.length + q.eval x.length)) := by
  let m := q.eval x.length
  let t := p.eval (x.length + m)
  have h := unrollBitsFrom_size_bound V t m t x
  have hs := SimBits.state_size_le (unrollBitsFrom V t (npInitBits V t m x) t) V.accept
  dsimp [npVerifierCircuit]
  simpa [m, t] using (le_trans hs h)

/-- The time bound `p.eval (n + q.eval n)` is itself a polynomial in `n`. -/
noncomputable def npTimePoly (p q : TimeBound) : TimeBound :=
  p.comp (X + q)

lemma npTimePoly_eval (p q : TimeBound) (n : Nat) :
    (npTimePoly p q).eval n = p.eval (n + q.eval n) := by
  simp [npTimePoly, Polynomial.eval_comp]

/-- Polynomial bound on the verifier circuit size as a function of `|x|`. -/
noncomputable def npCircuitPoly (V : TM) (p q : TimeBound) : TimeBound :=
  C (V.numStates + 2) + C 4 * npTimePoly p q +
    npTimePoly p q * (stepPoly V).comp (npTimePoly p q)

lemma npVerifierCircuit_size_le_poly (V : TM) (p q : TimeBound) (x : Word) :
    (npVerifierCircuit V p q x).size ≤ (npCircuitPoly V p q).eval x.length := by
  have h := npVerifierCircuit_size_bound V p q x
  have hstep := stepRelBound_le_stepPoly V (p.eval (x.length + q.eval x.length))
  have hmul := Nat.mul_le_mul_left (p.eval (x.length + q.eval x.length)) hstep
  simp [npCircuitPoly, npTimePoly, Polynomial.eval_comp]
  omega

/-- Polynomial bound on the length of the semantic reduction output. -/
noncomputable def npReductionOutputPoly (V : TM) (p q : TimeBound) : TimeBound :=
  tseitinPoly.comp (npCircuitPoly V p q + (X + q))

lemma maxVar_le_of_vars_subset {c : Circuit} {m : Nat} (h : c.vars ⊆ Finset.range m) :
    c.maxVar ≤ m := by
  induction c with
  | const b => simp [Circuit.maxVar]
  | var i =>
      have hi : i ∈ (Circuit.var i : Circuit).vars := by simp [Circuit.vars]
      have hi' := h hi
      have hi'' : i < m := by simpa [Finset.mem_range] using hi'
      simpa [Circuit.maxVar] using (Nat.le_of_lt hi'')
  | not c ih =>
      exact ih (by simpa [Circuit.vars] using h)
  | and c₁ c₂ ih1 ih2 =>
      apply max_le
      · exact ih1 (by intro i hi; exact h (by simp [Circuit.vars, hi]))
      · exact ih2 (by intro i hi; exact h (by simp [Circuit.vars, hi]))
  | or c₁ c₂ ih1 ih2 =>
      apply max_le
      · exact ih1 (by intro i hi; exact h (by simp [Circuit.vars, hi]))
      · exact ih2 (by intro i hi; exact h (by simp [Circuit.vars, hi]))

/-- The explicit semantic reduction from an NP verifier to SAT.  The only
    missing step for a genuine Cook--Levin reduction is showing that this word
    function is computed by a polynomial-time Turing machine. -/
def npReduction (V : TM) (p q : TimeBound) (x : Word) : Word :=
  (tseitinFormula (npVerifierCircuit V p q x)).encode

lemma npReduction_length_le_poly (V : TM) (p q : TimeBound) (x : Word) :
    (npReduction V p q x).length ≤ (npReductionOutputPoly V p q).eval x.length := by
  let C := npVerifierCircuit V p q x
  have hsize := npVerifierCircuit_size_le_poly V p q x
  have hmax : C.maxVar ≤ q.eval x.length := by
    dsimp [C]
    exact maxVar_le_of_vars_subset (npVerifierCircuit_vars_subset V p q x)
  have hXq : (X + q : TimeBound).eval x.length = x.length + q.eval x.length := by simp
  have hsum : C.size + C.maxVar ≤
      (npCircuitPoly V p q).eval x.length + (X + q).eval x.length := by
    dsimp [C] at hsize hmax ⊢
    omega
  have hlen := tseitin_encode_length_le_poly C
  have hmono := timeBound_eval_monotone tseitinPoly hsum
  rw [hXq] at hmono
  dsimp [C] at hlen hmono ⊢
  simp [npReduction, npReductionOutputPoly, Polynomial.eval_comp] at hmono ⊢
  exact le_trans hlen hmono

/-- A polynomial bound whose evaluation is one less than the fixed output
    length of the reduction.  The extra slack is used to add one fresh padding
    variable to the Tseitin formula. -/
noncomputable def npReductionFixedPoly (V : TM) (p q : TimeBound) : TimeBound :=
  C 2 * npReductionOutputPoly V p q + C 6

/-- The reduction with a fixed output length depending only on `|x|`.  The
    Tseitin formula is conjoined with a fresh variable whose index is chosen so
    that the total encoding length is exactly one more than
    `npReductionFixedPoly.eval x.length`. -/
noncomputable def npReductionFixed (V : TM) (p q : TimeBound) (x : Word) : Word :=
  let f := tseitinFormula (npVerifierCircuit V p q x)
  let L := (npReductionFixedPoly V p q).eval x.length + 1
  (Formula.and f (Formula.var (L - f.encode.length - 5))).encode

lemma npReductionFixed_length (V : TM) (p q : TimeBound) (x : Word) :
    (npReductionFixed V p q x).length =
      (npReductionFixedPoly V p q).eval x.length + 1 := by
  let f := tseitinFormula (npVerifierCircuit V p q x)
  let L := (npReductionFixedPoly V p q).eval x.length + 1
  have hlenpoly : f.encode.length ≤ (npReductionOutputPoly V p q).eval x.length := by
    dsimp [f]
    simpa [npReduction] using npReduction_length_le_poly V p q x
  have hL : L = 2 * (npReductionOutputPoly V p q).eval x.length + 7 := by
    dsimp [L, npReductionFixedPoly]
    simp
  have hkcalc : f.encode.length + (L - f.encode.length - 5) + 5 = L := by
    rw [hL]
    omega
  dsimp [npReductionFixed]
  rw [Formula.encode_length_and_var]
  exact hkcalc

lemma npReductionFixed_mem_SAT_iff (V : TM) (p q : TimeBound) (x : Word)
    (_hhalt : ∀ x y : Word,
      halted V (run V (p.eval (x ++ y).length) (init V (x ++ y))) = true) :
    npReductionFixed V p q x ∈ SAT ↔ npReduction V p q x ∈ SAT := by
  let f := tseitinFormula (npVerifierCircuit V p q x)
  let R := (npReductionOutputPoly V p q).eval x.length
  let L := (npReductionFixedPoly V p q).eval x.length + 1
  let k := L - f.encode.length - 5
  have hlenpoly : f.encode.length ≤ R := by
    dsimp [f, R]
    simpa [npReduction] using npReduction_length_le_poly V p q x
  have hmaxlen : f.maxVar < f.encode.length := f.maxVar_lt_encode_length
  have hL : L = 2 * R + 7 := by
    dsimp [L, R, npReductionFixedPoly]
    simp
  have hk : f.maxVar < k := by
    dsimp [k]
    rw [hL]
    omega
  constructor
  · rintro ⟨g, hg, a, ha⟩
    have hgf : g = Formula.and f (Formula.var k) := by
      apply Formula.encode_injective
      simpa [npReductionFixed, f, L, k] using hg
    subst g
    have hfsat : ∃ a : Nat → Bool, f.eval a = true :=
      (Formula.and_var_sat_iff_of_fresh f k hk).1 ⟨a, ha⟩
    exact ⟨f, by simp [npReduction, f], hfsat⟩
  · rintro ⟨g, hg, a, ha⟩
    have hgf : g = f := by
      apply Formula.encode_injective
      simpa [npReduction, f] using hg
    subst g
    refine ⟨Formula.and f (Formula.var k), ?_, ?_⟩
    · simp [npReductionFixed, f, L, k]
    · exact (Formula.and_var_sat_iff_of_fresh f k hk).2 ⟨a, ha⟩

lemma npReduction_mem_SAT_iff (V : TM) (p q : TimeBound) (x : Word)
    (hhalt : ∀ x y : Word,
      halted V (run V (p.eval (x ++ y).length) (init V (x ++ y))) = true) :
    npReduction V p q x ∈ SAT ↔
      ∃ y : Word, y.length ≤ q.eval x.length ∧
        acceptsIn V (x ++ y) (p.eval (x ++ y).length) = true := by
  rw [npReduction, ← circuit_tseitin_SAT_iff]
  let m := q.eval x.length
  let C := npVerifierCircuit V p q x
  have hCvars : C.vars ⊆ Finset.range m := by
    dsimp [C, m]
    exact npVerifierCircuit_vars_subset V p q x
  constructor
  · rintro ⟨y, hy⟩
    let y' : Word := y.take m
    have hy'len : y'.length ≤ m := by
      dsimp [y']
      simp [List.length_take]
    have hagree : ∀ i ∈ C.vars, y'.getD i false = y.getD i false := by
      intro i hi
      apply Circuit.word_getD_take_eq_of_lt
      have hi' := hCvars hi
      simpa [Finset.mem_range] using hi'
    have hy'eval : C.eval y' = C.eval y := Circuit.eval_eq_of_agree_on_vars_finset C hagree
    have hy'true : C.eval y' = true := by rwa [hy'eval]
    have haccT : acceptsIn V (x ++ y') (p.eval (x.length + q.eval x.length)) = true := by
      rw [← npVerifierCircuit_eval_eq_acceptsIn V p q x y' (by simpa [m] using hy'len)]
      simpa [C] using hy'true
    refine ⟨y', hy'len, ?_⟩
    have hlen : (x ++ y').length ≤ x.length + q.eval x.length := by
      simp only [List.length_append]
      simpa [m] using hy'len
    have hmono := timeBound_eval_monotone p hlen
    rw [← acceptsIn_eq_of_halted_within V (x ++ y') hmono (hhalt x y')]
    exact haccT
  · rintro ⟨y, hylen, hacc⟩
    refine ⟨y, ?_⟩
    have hCeval := npVerifierCircuit_eval_eq_acceptsIn V p q x y hylen
    change C.eval y = true
    rw [hCeval]
    have hlen : (x ++ y).length ≤ x.length + q.eval x.length := by
      simp only [List.length_append]
      omega
    have hmono := timeBound_eval_monotone p hlen
    rw [acceptsIn_eq_of_halted_within V (x ++ y) hmono (hhalt x y)]
    exact hacc

lemma npReductionFixed_mem_SAT_iff_accepts (V : TM) (p q : TimeBound) (x : Word)
    (hhalt : ∀ x y : Word,
      halted V (run V (p.eval (x ++ y).length) (init V (x ++ y))) = true) :
    npReductionFixed V p q x ∈ SAT ↔
      ∃ y : Word, y.length ≤ q.eval x.length ∧
        acceptsIn V (x ++ y) (p.eval (x ++ y).length) = true := by
  rw [npReductionFixed_mem_SAT_iff V p q x hhalt,
    npReduction_mem_SAT_iff V p q x hhalt]

/-- Polynomial-time word functions should be closed under composition.  This is
    a standard machine-composition fact; keeping it separate makes the reduction
    construction easier to organize. -/
def PolyTimeComputableClosedUnderComposition : Prop :=
  ∀ (f g : Word → Word), PolyTimeComputable f → PolyTimeComputable g →
    PolyTimeComputable (fun x => g (f x))

/-- The reduction can be assembled from two polynomial-time subroutines: one
    producing an intermediate encoding, and one turning that encoding into the
    fixed-length SAT instance. -/
def NPReductionSubroutineObligation : Prop :=
  ∀ (V : TM) (p q : TimeBound),
    ∃ (core aux : Word → Word),
      PolyTimeComputable core ∧ PolyTimeComputable aux ∧
      ∀ x : Word, aux (core x) = npReductionFixed V p q x

/-- The only missing step for a genuine Cook--Levin theorem: the explicit
    fixed-length semantic reduction must be computable by a polynomial-time TM.
    The fixed length is essential because `PolyTimeComputable` transducers have
    an output length determined only by `|x|`. -/
def NPSemanticReductionIsPolyTime : Prop :=
  ∀ (V : TM) (p q : TimeBound),
    (∀ x y : Word,
      halted V (run V (p.eval (x ++ y).length) (init V (x ++ y))) = true) →
    PolyTimeComputable (npReductionFixed V p q)

/-- The machine-realization obligation follows from composition closure plus
    the two subroutines above. -/
theorem NPSemanticReductionIsPolyTime_of_subroutines
    (hcomp : PolyTimeComputableClosedUnderComposition)
    (hsub : NPReductionSubroutineObligation) : NPSemanticReductionIsPolyTime := by
  intro V p q _hhalt
  rcases hsub V p q with ⟨core, aux, hcore, haux, hcorrect⟩
  have hfg : PolyTimeComputable (fun x => aux (core x)) := hcomp core aux hcore haux
  have heq : (fun x => aux (core x)) = npReductionFixed V p q := funext hcorrect
  simpa [heq] using hfg

/-- A bridge between the composable transducer model and the concrete TM model
    used by `Reducible`.  It is stated as an explicit proposition: the two
    models have different tape disciplines, and constructing the translation is
    a separate machine-construction obligation. -/
def DTMPolyTimeBridge : Prop :=
  ∀ f : Word → Word, DPolyTimeComputable f ↔ PolyTimeComputable f

/-- The fixed-length reduction can be assembled from two subroutines in the
    composable model.  The proved closure theorem then removes the composition
    obligation; only the two subroutine constructions and the bridge remain. -/
def NPReductionDTMSubroutineObligation : Prop :=
  ∀ (V : TM) (p q : TimeBound),
    ∃ (core aux : Word → Word),
      DPolyTimeComputable core ∧ DPolyTimeComputable aux ∧
      ∀ x : Word, aux (core x) = npReductionFixed V p q x

/-- Using the proved DTM composition theorem, the semantic reduction is
    polynomial-time in the concrete TM model whenever the DTM subroutines exist
    and the two models agree. -/
theorem NPSemanticReductionIsPolyTime_of_DTM
    (hbridge : DTMPolyTimeBridge) (hsub : NPReductionDTMSubroutineObligation) :
    NPSemanticReductionIsPolyTime := by
  intro V p q _hhalt
  rcases hsub V p q with ⟨core, aux, hcoreD, hauxD, hcorrect⟩
  have hfgD : DPolyTimeComputable (fun x => aux (core x)) :=
    DPolyTimeComputableClosedUnderComposition core aux hcoreD hauxD
  have hfgP : PolyTimeComputable (fun x => aux (core x)) := (hbridge _).1 hfgD
  have heq : (fun x => aux (core x)) = npReductionFixed V p q := funext hcorrect
  simpa [heq] using hfgP

/-- Cook--Levin, conditional only on the explicit machine-realization
    obligation above. -/
theorem semantic_cook_levin (hNP : NPSemanticReductionIsPolyTime) : NPHard SAT := by
  intro L hL
  rcases hL with ⟨V, p, q, hhalt, hmem⟩
  refine ⟨npReductionFixed V p q, hNP V p q hhalt, ?_⟩
  intro x
  rw [npReductionFixed_mem_SAT_iff_accepts V p q x hhalt]
  exact (hmem x).symm

/-- The semantic reduction alone is enough to transfer P/poly membership from
    SAT to every NP language; the SAT verifier obligation is not needed for
    this direction. -/
theorem NP_subset_PPoly_of_reduction_and_SAT_in_PPoly
    (hr : NPSemanticReductionIsPolyTime) (hSAT : InPPoly SAT) :
    ∀ L : Language, InNP L → InPPoly L := by
  intro L hL
  exact pPolyClosedUnderReductions L SAT hSAT ((semantic_cook_levin hr) L hL)

/-- Contrapositive: if some NP language is outside P/poly, then SAT is outside
    P/poly, assuming the semantic reduction is polytime. -/
theorem NPNotInPPoly_implies_SATNotInPPoly_of_reduction
    (hr : NPSemanticReductionIsPolyTime) :
    NPNotInPPoly → SATNotInPPoly := by
  intro hNP hSAT
  rcases hNP with ⟨L, hLNP, hLnot⟩
  exact hLnot (NP_subset_PPoly_of_reduction_and_SAT_in_PPoly hr hSAT L hLNP)

/-- Full Cook–Levin packaged as NP-completeness, conditional only on the two
    explicit machine-realization obligations. -/
theorem SATNPComplete_of_obligations
    (hv : SATVerifierTMExists) (hr : NPSemanticReductionIsPolyTime) : SATNPComplete := by
  exact ⟨SATVerifierTMExists_implies_SATVerifierExists hv, semantic_cook_levin hr⟩

/-- The complete 3b route, with every open result isolated as an explicit
    hypothesis. -/
theorem not_PEqualsNP_of_obligations
    (hv : SATVerifierTMExists) (hr : NPSemanticReductionIsPolyTime)
    (hlow : SATNotInPPoly) : ¬ PEqualsNP := by
  exact SATNPComplete_and_not_PPoly_implies_not_PEqualsNP
    (SATNPComplete_of_obligations hv hr) hlow

end PNP
