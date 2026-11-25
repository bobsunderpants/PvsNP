/-
  PNP/LambdaPositiveBondi.lean

  Mathlib version of the abstract AldS flux scaffold.

  This does NOT prove the open geomety/PDE theorem that there is an intrinsic
  news tensor on spacelike future infinity.  It proves the conditional logic:

    * vanishing flux  => charge conservation;
    * positive news-square representation of flux => charge monotonicity;
    * charge equality <=> vanishing flux integral;
    * the same calculus is instantiated in a finite toy model over ℝ.

  The genuinely open items are still represented as structures/definitions.
-/

module

import Mathlib

open MeasureTheory

namespace PNP.LambdaPositiveBondi

universe uP uB uC uV uT

/-- Abstract AldS flux calculus with real-valued charges and actual Bochner
    integrals over a measure on the 3-dimensional boundary region. -/
structure AldSFluxModel (P : Type uP) (B : Type uB) (C : Type uC)
    (V : Type uV) (T : Type uT) [MeasurableSpace P] where
  region : C → C → B
  future : C → C → Prop
  measure : C → C → Measure P
  D : V → P → T
  Tfield : P → T
  Nfield : P → T
  pair : T → T → ℝ
  charge : V → C → ℝ

  flux_balance :
    ∀ (ξ : V) (c₁ c₂ : C), future c₁ c₂ →
      charge ξ c₂ - charge ξ c₁ =
        - ∫ p, pair (Tfield p) (D ξ p) ∂measure c₁ c₂

  news_balance :
    ∀ (ξ : V) (c₁ c₂ : C), future c₁ c₂ →
      charge ξ c₂ - charge ξ c₁ =
        - ∫ p, pair (Nfield p) (Nfield p) ∂measure c₁ c₂

  nonneg_square : ∀ p : P, 0 ≤ pair (Nfield p) (Nfield p)

/-- A vector field whose associated flux density vanishes pointwise. -/
def FluxFreeVector
    [MeasurableSpace P]
    (M : AldSFluxModel P B C V T) (ξ : V) : Prop :=
  ∀ p : P, M.pair (M.Tfield p) (M.D ξ p) = 0

/-- If the flux density vanishes pointwise, the charge is conserved. -/
theorem conserved_of_flux_free
    [MeasurableSpace P]
    (M : AldSFluxModel P B C V T)
    (ξ : V)
    (hξ : FluxFreeVector M ξ)
    (c₁ c₂ : C) (hfut : M.future c₁ c₂) :
    M.charge ξ c₂ = M.charge ξ c₁ := by
  have hb := M.flux_balance ξ c₁ c₂ hfut
  have hfun :
      (fun p : P => M.pair (M.Tfield p) (M.D ξ p)) = (fun _ : P => 0) := by
    funext p
    exact hξ p
  rw [hfun] at hb
  simp at hb
  linarith

/-- If the charge drop is represented by the integral of a nonnegative news
    square, the charge is monotone nonincreasing. -/
theorem charge_nonincreasing
    [MeasurableSpace P]
    (M : AldSFluxModel P B C V T)
    (ξ : V)
    (c₁ c₂ : C) (hfut : M.future c₁ c₂) :
    M.charge ξ c₂ ≤ M.charge ξ c₁ := by
  have hb := M.news_balance ξ c₁ c₂ hfut
  have hI :
      0 ≤ ∫ p, M.pair (M.Nfield p) (M.Nfield p) ∂M.measure c₁ c₂ :=
    integral_nonneg M.nonneg_square
  linarith

/-- Charge equality is equivalent to vanishing flux integral. -/
theorem equal_charge_iff_zero_flux
    [MeasurableSpace P]
    (M : AldSFluxModel P B C V T)
    (ξ : V)
    (c₁ c₂ : C) (hfut : M.future c₁ c₂) :
    M.charge ξ c₂ = M.charge ξ c₁ ↔
      (∫ p, M.pair (M.Tfield p) (M.D ξ p) ∂M.measure c₁ c₂) = 0 := by
  have hb := M.flux_balance ξ c₁ c₂ hfut
  constructor
  · intro h
    linarith
  · intro hI
    linarith

/-- Desired rigidity target: vanishing integrated news square implies pointwise
    vanishing news.  This remains a research-level theorem, not a Lean theorem
    here. -/
def RigidityTarget [MeasurableSpace P] (M : AldSFluxModel P B C V T) : Prop :=
  ∀ c₁ c₂ : C, M.future c₁ c₂ →
    (∫ p, M.pair (M.Nfield p) (M.Nfield p) ∂M.measure c₁ c₂) = 0 ↔
      ∀ p : P, M.pair (M.Nfield p) (M.Nfield p) = 0

/-- The main missing mathematical input.  An instance of this structure would
    amount to constructing the desired intrinsic news tensor and proving its
    properties. -/
structure DesiredNewsConstruction (P : Type uP) (B : Type uB) (C : Type uC)
    (V : Type uV) (T : Type uT) [MeasurableSpace P] where
  model : AldSFluxModel P B C V T
  intrinsic : True
  recovers_bondi_news : True
  no_incoming_radiation : True
  peeling_statement : True
  lambda_to_zero_limit : True

/- Boundary data for the radiation criteria discussed in the literature.

   For Λ > 0 the conformal infinity is Riemannian.  The electric part of the
   rescaled Weyl tensor (equivalently the Fefferman-Graham third coefficient,
   up to the standard normalization) and the Cotton-York tensor of the
   boundary are symmetric 3 × 3 tensors.  The canonical asymptotic
   super-Poynting vector is, up to a nonzero Λ-dependent factor, the Hodge dual
   of their commutator.  Hence for Λ > 0 its vanishing is equivalent to the
   two tensors commuting.  This is a detector criterion, not yet a news tensor
   with a positive flux representation; that stronger statement is recorded
   below as a target. -/
namespace BoundaryRadiation

abbrev Index := Fin 3

/-- The Levi-Civita symbol in an oriented orthonormal boundary frame. -/
def leviCivita : Index → Index → Index → ℝ :=
  ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]],
    ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
    ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]]

/-- A symmetric rank-two tensor on the 3-dimensional conformal boundary. -/
structure SymTensor3 where
  a00 : ℝ
  a01 : ℝ
  a02 : ℝ
  a11 : ℝ
  a12 : ℝ
  a22 : ℝ

namespace SymTensor3

instance : Zero SymTensor3 where
  zero := { a00 := 0, a01 := 0, a02 := 0, a11 := 0, a12 := 0, a22 := 0 }

@[simp] lemma zero_a00 : (0 : SymTensor3).a00 = 0 := rfl
@[simp] lemma zero_a01 : (0 : SymTensor3).a01 = 0 := rfl
@[simp] lemma zero_a02 : (0 : SymTensor3).a02 = 0 := rfl
@[simp] lemma zero_a11 : (0 : SymTensor3).a11 = 0 := rfl
@[simp] lemma zero_a12 : (0 : SymTensor3).a12 = 0 := rfl
@[simp] lemma zero_a22 : (0 : SymTensor3).a22 = 0 := rfl

@[ext] theorem ext {A B : SymTensor3}
    (h00 : A.a00 = B.a00) (h01 : A.a01 = B.a01) (h02 : A.a02 = B.a02)
    (h11 : A.a11 = B.a11) (h12 : A.a12 = B.a12) (h22 : A.a22 = B.a22) :
    A = B := by
  cases A
  cases B
  simp_all

/-- Components in the oriented orthonormal frame. -/
def val (A : SymTensor3) : Index → Index → ℝ :=
  ![![A.a00, A.a01, A.a02],
    ![A.a01, A.a11, A.a12],
    ![A.a02, A.a12, A.a22]]

@[simp] lemma val_zero : val 0 = fun _ _ => (0 : ℝ) := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [val]

end SymTensor3

/-- The Cotton-York tensor of the spacelike conformal boundary. -/
abbrev Cotton := SymTensor3

/-- The holographic stress tensor, i.e. the rescaled Weyl electric part
     (Fefferman-Graham coefficient 3) up to conventional normalization. -/
abbrev Stress := SymTensor3

/-- Algebraic commutator [C,F]_{ij} = C_i{}^k F_{kj} - F_i{}^k C_{kj}. -/
def commutator (C : Cotton) (F : Stress) : Index → Index → ℝ :=
  fun i j => ∑ k : Index, (C.val i k * F.val k j - F.val i k * C.val k j)

/-- Scalar multiplication of a symmetric boundary tensor. -/
def scaleSym (r : ℝ) (A : SymTensor3) : SymTensor3 where
  a00 := r * A.a00
  a01 := r * A.a01
  a02 := r * A.a02
  a11 := r * A.a11
  a12 := r * A.a12
  a22 := r * A.a22

@[simp] lemma scaleSym_zero (r : ℝ) : scaleSym r 0 = 0 := by
  ext <;> simp [scaleSym]

/-- The algebraic commutator is bilinear.  Together with the zero background
    data of de Sitter this shows that the super-Poynting detector starts at
    second order under linear perturbations. -/
lemma commutator_scaleSym_scaleSym (r s : ℝ) (C : Cotton) (F : Stress) :
    commutator (scaleSym r C) (scaleSym s F) =
      fun i j => r * s * commutator C F i j := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [scaleSym, commutator, SymTensor3.val, Fin.sum_univ_three] <;> ring

/-- Canonical asymptotic super-Poynting vector, with the overall nonzero
     Λ-dependent constant suppressed. -/
def superPoynting (C : Cotton) (F : Stress) : Index → ℝ :=
  fun i => ∑ j : Index, ∑ k : Index, (leviCivita i j k * commutator C F j k)

/-- The detector is likewise bilinear in Cotton and stress. -/
lemma superPoynting_scaleSym_scaleSym (r s : ℝ) (C : Cotton) (F : Stress) :
    superPoynting (scaleSym r C) (scaleSym s F) =
      fun i => r * s * superPoynting C F i := by
  funext i
  simp only [superPoynting, commutator_scaleSym_scaleSym]
  fin_cases i <;> simp [leviCivita, Fin.sum_univ_three] <;> ring

/-- On a de Sitter background both Cotton and stress vanish.  A perturbation
    \(\varepsilon C^{(1)}, \varepsilon D^{(1)}\) therefore produces a detector
    proportional to \(\varepsilon^2\): the super-Poynting criterion has no
    linearized first-order part and cannot itself define linear news. -/
lemma linearized_superPoynting_is_quadratic (ε : ℝ) (C₁ : Cotton) (F₁ : Stress) :
    superPoynting (scaleSym ε C₁) (scaleSym ε F₁) =
      fun i => ε ^ 2 * superPoynting C₁ F₁ i := by
  rw [superPoynting_scaleSym_scaleSym]
  funext i
  ring

/-- Vanishing of the canonical super-Poynting vector relative to the unit
     normal to spacelike infinity.  For Λ > 0 this is the literature
     no-radiation detector. -/
def CanonicalSuperPoyntingZero (C : Cotton) (F : Stress) : Prop :=
  ∀ i : Index, superPoynting C F i = 0

/-- Vanishing of the algebraic commutator of Cotton-York and holographic
     stress. -/
def CommutatorZero (C : Cotton) (F : Stress) : Prop :=
  ∀ i j : Index, commutator C F i j = 0

/-- No-radiation criterion for Λ > 0, encoded in the canonical frame. -/
def NoRadiation (C : Cotton) (F : Stress) : Prop :=
  CanonicalSuperPoyntingZero C F

lemma commutator_skew (C : Cotton) (F : Stress) (i j : Index) :
    commutator C F j i = - commutator C F i j := by
  fin_cases i <;> fin_cases j <;>
    simp [commutator, SymTensor3.val, Fin.sum_univ_three] <;> ring

/-- In three dimensions the Hodge dual on skew symmetric tensors is injective,
     so the canonical super-Poynting vector vanishes iff the commutator does.
     This is the algebraic core of the Λ > 0 equivalence. -/
theorem canonicalSuperPoyntingZero_iff_commutatorZero (C : Cotton) (F : Stress) :
    CanonicalSuperPoyntingZero C F ↔ CommutatorZero C F := by
  constructor
  · intro h
    have h0 := h (0 : Index)
    have h1 := h (1 : Index)
    have h2 := h (2 : Index)
    simp [superPoynting, leviCivita, commutator, SymTensor3.val,
      Fin.sum_univ_three] at h0 h1 h2
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [commutator, SymTensor3.val, Fin.sum_univ_three] <;> nlinarith
  · intro h i
    simp only [superPoynting]
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro k hk
    rw [h j k]
    simp

/-- The equivalence stated in detector form. -/
theorem noRadiation_iff_commuting (C : Cotton) (F : Stress) :
    NoRadiation C F ↔ CommutatorZero C F :=
  canonicalSuperPoyntingZero_iff_commutatorZero C F

/-- For Λ < 0 the conformal boundary is Lorentzian and there is no canonical
     unit observer.  The no-radiation condition is that Cotton-York and
     holographic stress are functionally linearly dependent, i.e. proportional
     with at least one nonzero coefficient.  This is strictly stronger than
     commutation. -/
def Proportional (C : Cotton) (F : Stress) : Prop :=
  ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ i j : Index, a * C.val i j = b * F.val i j

/-- No-radiation detector for Λ < 0. -/
def NegativeNoRadiation (C : Cotton) (F : Stress) : Prop :=
  Proportional C F

/-- Proportionality implies commutation for any two matrices.  This is the
     easy direction of the sign-dependent comparison. -/
theorem proportional_implies_commutatorZero {C : Cotton} {F : Stress}
    (h : Proportional C F) : CommutatorZero C F := by
  rcases h with ⟨a, b, hne, hcomp⟩
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      rcases hne with hne | hne
      · exact (hne ha).elim
      · exact hne
    have hFzero : ∀ i j : Index, F.val i j = 0 := by
      intro i j
      have hij := hcomp i j
      rw [ha] at hij
      have : b * F.val i j = 0 := by simpa using hij.symm
      exact (mul_eq_zero.mp this).resolve_left hb
    intro i j
    simp [commutator, hFzero]
  · by_cases hb : b = 0
    · have hCzero : ∀ i j : Index, C.val i j = 0 := by
        intro i j
        have hij := hcomp i j
        rw [hb] at hij
        have : a * C.val i j = 0 := by simpa using hij
        exact (mul_eq_zero.mp this).resolve_left ha
      intro i j
      simp [commutator, hCzero]
    · have hCeq : ∀ i j : Index, C.val i j = (b / a) * F.val i j := by
        intro i j
        have hij := hcomp i j
        field_simp [ha] at hij ⊢
        linarith
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp only [commutator] <;>
        simp only [hCeq] <;>
        simp [SymTensor3.val, Fin.sum_univ_three] <;> ring

/-- Boundary data available in a candidate AldS news construction.  The fields
     are not assumed to satisfy any positivity or flux identity. -/
structure CandidateRadiationData (P : Type uP) (T : Type uT) where
  cotton : P → Cotton
  stress : P → Stress
  news : P → T

/-- Target: the candidate news vanishes exactly where the Λ > 0 radiation
     detector does.  A proof of this for a geometrically constructed news
     tensor is part of the open problem. -/
def DetectorNewsTarget [Zero T] (R : CandidateRadiationData P T) : Prop :=
  ∀ p : P, NoRadiation (R.cotton p) (R.stress p) ↔ R.news p = 0

/-- Target: the AldS charge flux is represented by the candidate news square. -/
def NewsRepresentationTarget
    [MeasurableSpace P]
    (M : AldSFluxModel P B C V T) (R : CandidateRadiationData P T) : Prop :=
  ∀ (ξ : V) (c₁ c₂ : C), M.future c₁ c₂ →
    M.charge ξ c₂ - M.charge ξ c₁ =
      - ∫ p, M.pair (R.news p) (R.news p) ∂M.measure c₁ c₂

/-- Target: the candidate news square is pointwise nonnegative. -/
def NewsPositivityTarget
    [MeasurableSpace P]
    (M : AldSFluxModel P B C V T) (R : CandidateRadiationData P T) : Prop :=
  ∀ p : P, 0 ≤ M.pair (R.news p) (R.news p)

/-- Conditional implication: if a candidate news tensor has the detector
     equivalence, vanishing candidate news implies no radiation. -/
theorem noRadiation_of_candidate_news_zero [Zero T]
    (R : CandidateRadiationData P T) (hR : DetectorNewsTarget R)
    (p : P) (hp : R.news p = 0) :
    NoRadiation (R.cotton p) (R.stress p) :=
  (hR p).2 hp

/-- The same implication in commutator form. -/
theorem commutatorZero_of_candidate_news_zero [Zero T]
    (R : CandidateRadiationData P T) (hR : DetectorNewsTarget R)
    (p : P) (hp : R.news p = 0) :
    CommutatorZero (R.cotton p) (R.stress p) :=
  (noRadiation_iff_commuting _ _).1 (noRadiation_of_candidate_news_zero R hR p hp)

/-- Conditional monotonicity from the candidate representation and positivity. -/
theorem charge_nonincreasing_of_candidate_news
    [MeasurableSpace P]
    (M : AldSFluxModel P B C V T) (R : CandidateRadiationData P T)
    (hrep : NewsRepresentationTarget M R) (hpos : NewsPositivityTarget M R)
    (ξ : V) (c₁ c₂ : C) (hfut : M.future c₁ c₂) :
    M.charge ξ c₂ ≤ M.charge ξ c₁ := by
  have hb := hrep ξ c₁ c₂ hfut
  have hI : 0 ≤ ∫ p, M.pair (R.news p) (R.news p) ∂M.measure c₁ c₂ :=
    integral_nonneg hpos
  linarith

/-- The full target.  An instance would supply a cut-wise news tensor for
     spacelike infinity whose vanishing is detected by the canonical
     super-Poynting vector, whose square represents the AldS charge flux, and
     which has the expected flat-space and structural properties.  No such
     instance is constructed here; doing so is the research problem. -/
structure DesiredCutNewsConstruction (P : Type uP) (B : Type uB) (C : Type uC)
    (V : Type uV) (T : Type uT) [MeasurableSpace P] [Zero T] where
  model : AldSFluxModel P B C V T
  radiationData : CandidateRadiationData P T
  detector : DetectorNewsTarget radiationData
  representation : NewsRepresentationTarget model radiationData
  positivity : NewsPositivityTarget model radiationData
  recovers_bondi_news : True
  no_incoming_radiation : True
  peeling_statement : True
  lambda_to_zero_limit : True

/- Small algebraic sanity checks: commuting diagonal boundary tensors are
   non-radiating by this detector, while a noncommuting pair is detected. -/
namespace Examples

def diagonal (a b c : ℝ) : SymTensor3 :=
  { a00 := a, a01 := 0, a02 := 0, a11 := b, a12 := 0, a22 := c }

def shear (s : ℝ) : SymTensor3 :=
  { a00 := 0, a01 := s, a02 := 0, a11 := 0, a12 := 0, a22 := 0 }

lemma diagonal_commutes (a b c d e f : ℝ) :
    CommutatorZero (diagonal a b c) (diagonal d e f) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [commutator, diagonal, SymTensor3.val, Fin.sum_univ_three] <;> ring

/-- Commuting trace-free pairs need not be proportional.  This is the algebraic
     reason why commutation is insufficient for Λ < 0. -/
lemma diagonal_commuting_not_proportional :
    CommutatorZero (diagonal 1 (-1) 0) (diagonal 2 1 (-3)) ∧
      ¬ Proportional (diagonal 1 (-1) 0) (diagonal 2 1 (-3)) := by
  constructor
  · simpa using diagonal_commutes 1 (-1) 0 2 1 (-3)
  · rintro ⟨a, b, hne, hcomp⟩
    have h00 := hcomp (0 : Index) (0 : Index)
    have h11 := hcomp (1 : Index) (1 : Index)
    simp [diagonal, SymTensor3.val] at h00 h11
    have ha0 : a = 0 := by nlinarith
    have hb0 : b = 0 := by nlinarith
    rcases hne with ha | hb
    · exact ha ha0
    · exact hb hb0

example : NoRadiation (diagonal 1 2 3) (diagonal 4 5 6) := by
  rw [noRadiation_iff_commuting]
  exact diagonal_commutes 1 2 3 4 5 6

example : ¬ NoRadiation (diagonal 1 2 3) (shear 1) := by
  intro h
  have h2 := h (2 : Index)
  norm_num [NoRadiation, CanonicalSuperPoyntingZero, superPoynting, leviCivita,
    commutator, diagonal, shear, SymTensor3.val, Fin.sum_univ_three] at h2

/- Boundary data of the Λ > 0 photon-rocket Robinson–Trautman family in the
   orthonormal frame of arXiv:2608.31129, eq. (35).  Only the σ = +1 case is
   encoded here.  The constants are normalized exactly as in the algebraic
   detector; overall nonzero Λ-dependent factors are irrelevant for zero sets. -/
def rocketStress (m p q : ℝ) : Stress :=
  { a00 := -2 * m, a01 := -q, a02 := 0,
    a11 := m + p, a12 := 0, a22 := m - p }

def rocketCotton (p q : ℝ) : Cotton :=
  { a00 := 0, a01 := 0, a02 := -q,
    a11 := 0, a12 := p, a22 := 0 }

/-- The first super-Poynting component in the rocket frame is a negative sum of
     squares, so its vanishing forces p = q = 0. -/
lemma rocket_superPoynting_zero (m p q : ℝ) :
    superPoynting (rocketCotton p q) (rocketStress m p q) (0 : Index)
      = -4 * p ^ 2 - 2 * q ^ 2 := by
  simp [superPoynting, leviCivita, commutator, rocketCotton, rocketStress,
    SymTensor3.val, Fin.sum_univ_three]
  ring

/-- In this family the canonical detector vanishes exactly for p = q = 0,
     i.e. precisely for the generalized Kinnersley non-radiating rockets. -/
lemma rocket_noRadiation_iff (m p q : ℝ) :
    NoRadiation (rocketCotton p q) (rocketStress m p q) ↔ p = 0 ∧ q = 0 := by
  constructor
  · intro h
    have h0 := h (0 : Index)
    simp [superPoynting, leviCivita, commutator, rocketCotton, rocketStress,
      SymTensor3.val, Fin.sum_univ_three] at h0
    have hp2 : p ^ 2 = 0 := by nlinarith [sq_nonneg p, sq_nonneg q]
    have hq2 : q ^ 2 = 0 := by nlinarith [sq_nonneg p, sq_nonneg q]
    exact ⟨sq_eq_zero_iff.mp hp2, sq_eq_zero_iff.mp hq2⟩
  · rintro ⟨hp, hq⟩
    subst p
    subst q
    rw [noRadiation_iff_commuting]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [commutator, rocketCotton, rocketStress, SymTensor3.val, Fin.sum_univ_three]

/- Algebraic form of the outgoing cut condition \(\mathcal Q_-^\mu=0\) from
   arXiv:2208.05436, eq. (80).  The tangential stress is the Hodge dual of the
   STF Cotton tensor and the normal-tangential stress is the Hodge dual of the
   Cotton one-form.  The normal-normal components \(c_0,f_0\) are the two
   Coulombian spectators and cancel out of the detector. -/
noncomputable def outgoingCotton (c0 c1 c2 a b : ℝ) : Cotton :=
  { a00 := c0, a01 := c1, a02 := c2,
    a11 := a - c0 / 2, a12 := b, a22 := -a - c0 / 2 }

noncomputable def outgoingStress (f0 c1 c2 a b : ℝ) : Stress :=
  { a00 := f0, a01 := c2, a02 := -c1,
    a11 := b - f0 / 2, a12 := -a, a22 := -b - f0 / 2 }

/-- The normal super-Poynting component is a negative sum of squares of the
    Cotton STF tensor and Cotton one-form, independently of the Coulombian
    components. -/
lemma outgoing_superPoynting_normal (c0 f0 c1 c2 a b : ℝ) :
    superPoynting (outgoingCotton c0 c1 c2 a b)
      (outgoingStress f0 c1 c2 a b) (0 : Index)
      = -2 * (2 * (a ^ 2 + b ^ 2) + (c1 ^ 2 + c2 ^ 2)) := by
  simp [superPoynting, leviCivita, commutator, outgoingCotton, outgoingStress,
    SymTensor3.val, Fin.sum_univ_three]
  ring

/-- Hence the outgoing detector vanishes exactly when the Cotton STF tensor and
    Cotton one-form vanish. -/
lemma outgoing_noRadiation_iff (c0 f0 c1 c2 a b : ℝ) :
    NoRadiation (outgoingCotton c0 c1 c2 a b)
      (outgoingStress f0 c1 c2 a b) ↔ a = 0 ∧ b = 0 ∧ c1 = 0 ∧ c2 = 0 := by
  constructor
  · intro h
    have hp0 := h (0 : Index)
    rw [outgoing_superPoynting_normal] at hp0
    have hsum : 2 * (a ^ 2 + b ^ 2) + (c1 ^ 2 + c2 ^ 2) = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c1, sq_nonneg c2]
    have hab : a ^ 2 + b ^ 2 = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c1, sq_nonneg c2]
    have hc : c1 ^ 2 + c2 ^ 2 = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c1, sq_nonneg c2]
    exact ⟨sq_eq_zero_iff.mp (by nlinarith : a ^ 2 = 0),
      sq_eq_zero_iff.mp (by nlinarith : b ^ 2 = 0),
      sq_eq_zero_iff.mp (by nlinarith : c1 ^ 2 = 0),
      sq_eq_zero_iff.mp (by nlinarith : c2 ^ 2 = 0)⟩
  · rintro ⟨ha, hb, hc1, hc2⟩
    rw [noRadiation_iff_commuting]
    subst a; subst b; subst c1; subst c2
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [commutator, outgoingCotton, outgoingStress, SymTensor3.val,
        Fin.sum_univ_three] <;> ring

end Examples

end BoundaryRadiation

/- A finite toy model over ℝ.  It is not a spacetime; it only instantiates the
   abstract flux calculus. -/
namespace Toy

abbrev P := Nat
abbrev B := Unit
abbrev C := Fin 3
abbrev V := Unit
abbrev T := ℝ

def future (c₁ c₂ : C) : Prop :=
  c₂.val = c₁.val + 1

noncomputable def toyMeasure (c₁ c₂ : C) : Measure P := by
  classical
  exact if future c₁ c₂ then Measure.dirac c₁.val else 0

def toyPair (a b : T) : ℝ :=
  a * b

def toyCharge (_ : V) (c : C) : ℝ :=
  - (c.val : ℝ)

lemma integral_one_toyMeasure (c₁ c₂ : C) (hfut : future c₁ c₂) :
    (∫ _ : P, (1 : ℝ) ∂toyMeasure c₁ c₂) = 1 := by
  simp [toyMeasure, hfut]

lemma integral_pair_one_toyMeasure (c₁ c₂ : C) (hfut : future c₁ c₂) :
    (∫ _ : P, toyPair 1 1 ∂toyMeasure c₁ c₂) = 1 := by
  simpa [toyPair] using integral_one_toyMeasure c₁ c₂ hfut

lemma charge_diff_of_future (c₁ c₂ : C) (hfut : future c₁ c₂) :
    toyCharge () c₂ - toyCharge () c₁ = -1 := by
  have hreal : (c₂.val : ℝ) = (c₁.val : ℝ) + 1 := by
    exact_mod_cast hfut
  rw [toyCharge, toyCharge, hreal]
  ring

noncomputable def toyModel : AldSFluxModel P B C V T where
  region _ _ := ()
  future := future
  measure := toyMeasure
  D _ _ := 1
  Tfield _ := 1
  Nfield _ := 1
  pair := toyPair
  charge := toyCharge

  flux_balance := by
    intro ξ c₁ c₂ hfut
    rw [charge_diff_of_future c₁ c₂ hfut]
    rw [integral_pair_one_toyMeasure c₁ c₂ hfut]

  news_balance := by
    intro ξ c₁ c₂ hfut
    rw [charge_diff_of_future c₁ c₂ hfut]
    rw [integral_pair_one_toyMeasure c₁ c₂ hfut]

  nonneg_square := by
    intro p
    simp [toyPair]

theorem toy_charge_nonincreasing
    (ξ : V) (c₁ c₂ : C) (hfut : future c₁ c₂) :
    toyModel.charge ξ c₂ ≤ toyModel.charge ξ c₁ :=
  charge_nonincreasing toyModel ξ c₁ c₂ hfut

end Toy

/- The outgoing-radiation condition \(Q_-^\mu=0\) of arXiv:2208.05436 gives a
   stronger statement than the bare detector: the component of the canonical
   super-Poynting vector normal to a compact cut is a negative sum of squares
   of intrinsic Cotton data.  This is encoded here as an abstract positive
   flux law; supplying the geometric types and proving `flux_eq` is part of the
   research program. -/
namespace OutgoingRadiation

universe uU

structure OutgoingCutData (P : Type uP) (T : Type uT) (U : Type uU) [Zero T] [Zero U] where
  normalFlux : P → ℝ
  stfCotton : P → T
  cottonOneForm : P → U
  pairT : T → T → ℝ
  pairU : U → U → ℝ
  nonnegT : ∀ x : T, 0 ≤ pairT x x
  nonnegU : ∀ x : U, 0 ≤ pairU x x
  eq_zeroT : ∀ x : T, pairT x x = 0 ↔ x = 0
  eq_zeroU : ∀ x : U, pairU x x = 0 ↔ x = 0
  flux_eq : ∀ p : P,
    normalFlux p = -2 * (pairT (stfCotton p) (stfCotton p) +
      pairU (cottonOneForm p) (cottonOneForm p))

theorem normalFlux_nonpos [Zero T] [Zero U]
    (M : OutgoingCutData P T U) (p : P) : M.normalFlux p ≤ 0 := by
  rw [M.flux_eq p]
  have hT := M.nonnegT (M.stfCotton p)
  have hU := M.nonnegU (M.cottonOneForm p)
  nlinarith

theorem normalFlux_eq_zero_iff [Zero T] [Zero U]
    (M : OutgoingCutData P T U) (p : P) :
    M.normalFlux p = 0 ↔ M.stfCotton p = 0 ∧ M.cottonOneForm p = 0 := by
  constructor
  · intro hp
    have h := M.flux_eq p
    have hTnon := M.nonnegT (M.stfCotton p)
    have hUnon := M.nonnegU (M.cottonOneForm p)
    have hTzero : M.pairT (M.stfCotton p) (M.stfCotton p) = 0 := by nlinarith
    have hUzero : M.pairU (M.cottonOneForm p) (M.cottonOneForm p) = 0 := by nlinarith
    exact ⟨(M.eq_zeroT _).1 hTzero, (M.eq_zeroU _).1 hUzero⟩
  · rintro ⟨hT, hU⟩
    rw [M.flux_eq p, hT, hU]
    have hzT : M.pairT 0 0 = 0 := (M.eq_zeroT 0).2 rfl
    have hzU : M.pairU 0 0 = 0 := (M.eq_zeroU 0).2 rfl
    simp [hzT, hzU]

end OutgoingRadiation

/- Logical skeleton of the cut-wise news program of arXiv:2208.05436,
   Proposition 1.  A real implementation must supply the geometric types and
   prove the Codazzi uniqueness theorem.  What is formalized here is only the
   conditional implication: uniqueness of the trace-free Codazzi solution plus
   a detector-zero criterion for the source imply that the constructed news
   vanishes exactly in the non-radiating cases. -/
namespace CutNews

universe uS uN uX

structure CutNewsCandidate (S : Type uS) (N : Type uN) (XOne : Type uX)
    [AddGroup N] [Zero XOne] where
  detectorZero : S → Prop
  V : S → N
  M : S → N
  source : S → XOne
  altD : N → XOne
  altD_zero : altD 0 = 0
  news_codazzi : ∀ s : S, altD (V s + M s) = source s
  unique_solution : ∀ (s : S) (m : N), altD (V s + m) = source s → m = M s
  source_zero_iff_detector : ∀ s : S, source s = 0 ↔ detectorZero s

/-- Uniqueness of the trace-free Codazzi solution makes the source vanish
    exactly when the cut news vanishes.  This is the logical content of the
    requirement stated just after eq. (70) of arXiv:2208.05436. -/
theorem source_zero_iff_news_zero {S : Type uS} {N : Type uN} {XOne : Type uX}
    [AddGroup N] [Zero XOne] (K : CutNewsCandidate S N XOne) (s : S) :
    K.source s = 0 ↔ K.V s + K.M s = 0 := by
  constructor
  · intro hsource
    have hm : -K.V s = K.M s := by
      apply K.unique_solution s (-K.V s)
      simp [K.altD_zero, hsource]
    rw [← hm]
    simp
  · intro hnews
    rw [← K.news_codazzi s, hnews, K.altD_zero]

/-- The conditional central equivalence for a cut-wise news candidate. -/
theorem news_zero_iff_detector_zero {S : Type uS} {N : Type uN} {XOne : Type uX}
    [AddGroup N] [Zero XOne] (K : CutNewsCandidate S N XOne) (s : S) :
    K.V s + K.M s = 0 ↔ K.detectorZero s := by
  rw [← source_zero_iff_news_zero K s]
  exact K.source_zero_iff_detector s

/-- Contrapositive: radiation is detected exactly when the candidate news is
    nonzero. -/
theorem news_nonzero_iff_radiation {S : Type uS} {N : Type uN} {XOne : Type uX}
    [AddGroup N] [Zero XOne] (K : CutNewsCandidate S N XOne) (s : S) :
    K.V s + K.M s ≠ 0 ↔ ¬ K.detectorZero s := by
  exact not_congr (news_zero_iff_detector_zero K s)

end CutNews

/- A consistency check on the usual simplified target statement.  If the charge
   flux is linear in the asymptotic symmetry generator ξ, then a single
   ξ-independent nonnegative density cannot represent the flux for all ξ unless
   the flux vanishes identically.  This does not affect the meaningful target
   for a fixed translation or for a ξ-dependent integrand; it only rules out the
   oversimplified “one scalar density represents every charge flux” reading. -/
namespace LinearFluxObstruction

variable {V : Type*} [AddCommMonoid V] [Module ℝ V]

structure Representation where
  flux : V → ℝ
  square : ℝ
  linear_smul : ∀ (a : ℝ) (ξ : V), flux (a • ξ) = a * flux ξ
  balance : ∀ ξ : V, flux ξ = square

theorem no_nonzero_constant_square (R : Representation (V := V)) {ξ : V}
    (hξ : R.flux ξ ≠ 0) : False := by
  have h1 := R.balance ξ
  have h2 := R.balance ((2 : ℝ) • ξ)
  rw [R.linear_smul (2 : ℝ) ξ] at h2
  have hzero : R.flux ξ = 0 := by linarith
  exact hξ hzero

end LinearFluxObstruction

/- Linearized Hamiltonian news: the flux is a phase-space pairing between a
   news object and the symmetry generator acting on trace-free metric data.
   This records only the exact ξ-linearity of that construction. -/
namespace HamiltonianNewsFlux

variable {Symmetry News Field : Type*} [AddCommGroup Symmetry] [Module ℝ Symmetry]
  [AddCommMonoid News] [Module ℝ News]
  [AddCommGroup Field] [Module ℝ Field]

structure Model where
  news : News
  action : Symmetry →ₗ[ℝ] Field
  pairing : News →ₗ[ℝ] Field →ₗ[ℝ] ℝ
  flux : Symmetry → ℝ
  flux_eq : ∀ ξ : Symmetry, flux ξ = pairing news (action ξ)

theorem flux_smul (M : Model (Symmetry := Symmetry) (News := News) (Field := Field))
    (a : ℝ) (ξ : Symmetry) : M.flux (a • ξ) = a * M.flux ξ := by
  rw [M.flux_eq, M.flux_eq]
  simp

theorem flux_add (M : Model (Symmetry := Symmetry) (News := News) (Field := Field))
    (ξ η : Symmetry) : M.flux (ξ + η) = M.flux ξ + M.flux η := by
  rw [M.flux_eq, M.flux_eq, M.flux_eq]
  simp

theorem flux_zero (M : Model (Symmetry := Symmetry) (News := News) (Field := Field)) :
    M.flux 0 = 0 := by
  rw [M.flux_eq]
  simp

end HamiltonianNewsFlux

/- Algebraic core of the CKV degeneracy of the simple volume flux law:
   a symmetric trace-free tensor has zero contraction with a derivative
   decomposed into pure trace plus antisymmetric part. -/
namespace CKVFluxDegeneracy

open BoundaryRadiation

def trace (T : SymTensor3) : ℝ := T.a00 + T.a11 + T.a22

def delta (i j : Index) : ℝ := if i = j then 1 else 0

def ckvDerivative (σ : ℝ) (A : Index → Index → ℝ) (i j : Index) : ℝ :=
  σ * delta i j + A i j

theorem contract_zero (T : SymTensor3) (hT : trace T = 0) (σ : ℝ)
    (A : Index → Index → ℝ) (hskew : ∀ i j, A j i = -A i j) :
    (∑ i : Index, ∑ j : Index, T.val i j * ckvDerivative σ A i j) = 0 := by
  have h00 : A 0 0 = 0 := by
    have h := hskew 0 0
    linarith
  have h11 : A 1 1 = 0 := by
    have h := hskew 1 1
    linarith
  have h22 : A 2 2 = 0 := by
    have h := hskew 2 2
    linarith
  have h10 : A 1 0 = -A 0 1 := by simpa using (hskew 0 1)
  have h20 : A 2 0 = -A 0 2 := by simpa using (hskew 0 2)
  have h21 : A 2 1 = -A 1 2 := by simpa using (hskew 1 2)
  simp [ckvDerivative, delta, Fin.sum_univ_three, SymTensor3.val,
        h00, h11, h22, h10, h20, h21, trace] at hT ⊢
  ring_nf at hT ⊢
  have hmul : (T.a00 + T.a11 + T.a22) * σ = 0 := by rw [hT]; ring
  ring_nf at hmul
  linarith

end CKVFluxDegeneracy

/- A small negative result about the simplest pointwise news-square ansatz.
   Under the outgoing condition the available cut data are a trace-free Cotton
   tensor and an independent Cotton one-form.  No *linear* combination of these
   can be a symmetric trace-free tensor whose pointwise square equals the sum of
   their separate squares: by polarization, the cross term would have to vanish
   for all independent inputs, which is impossible for a nonzero isometry. -/
namespace NewsSquareObstruction

abbrev E := Fin 2 → ℝ

theorem no_linear_pointwise_square (L K : E →ₗ[ℝ] E)
    (hLnorm : ∀ x : E, ‖L x‖ = ‖x‖)
    (hKnorm : ∀ x : E, ‖K x‖ = ‖x‖)
    (hsquare : ∀ x y : E, ‖L x + K y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2) :
    False := by
  classical
  have hLinj : Function.Injective L := by
    intro x y hxy
    have hzero : L (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hnorm : ‖x - y‖ = 0 := by
      rw [← hLnorm (x - y), hzero, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  have hLsurj : Function.Surjective L := LinearMap.injective_iff_surjective.mp hLinj
  let y : E := fun i => if i = (0 : Fin 2) then 1 else 0
  have hy : y ≠ 0 := by
    intro h
    have h0 := congrFun h (0 : Fin 2)
    simp [y] at h0
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hKy : K y ≠ 0 := by
    intro h
    have hn := hKnorm y
    rw [h, norm_zero] at hn
    exact hy (norm_eq_zero.mp hn.symm)
  obtain ⟨x, hx⟩ := hLsurj (K y)
  have hxnorm : ‖x‖ = ‖K y‖ := by
    rw [← hLnorm x, hx]
  have hsq := hsquare x y
  rw [hx] at hsq
  have htwice : K y + K y = (2 : ℝ) • K y := by
    ext i
    change K y i + K y i = 2 * K y i
    ring
  rw [htwice, norm_smul] at hsq
  have hKypos : 0 < ‖K y‖ := norm_pos_iff.mpr hKy
  simp at hsq
  rw [hxnorm, hKnorm y] at hsq
  nlinarith [sq_pos_of_pos hKypos]

end NewsSquareObstruction

/- Per harmonic mode, the detector pair has four scalar polarizations while a
   rank-two STF tensor has two.  SO(3)-equivariance makes this fibre dimension
   count exact even for nonlocal spectral multipliers. -/
namespace HarmonicDimensionObstruction

abbrev PairMode := Fin 4 → ℝ
abbrev TensorMode := Fin 2 → ℝ

theorem no_injective_pair_to_tensor (L : PairMode →ₗ[ℝ] TensorMode) :
    ¬ Function.Injective L := by
  intro hL
  have hle := LinearMap.finrank_le_finrank_of_injective hL
  norm_num at hle

end HarmonicDimensionObstruction

/- The linearized de Sitter energy flux provides a second obstruction to a
   positive news square.  In the TT-mode representation of Ashtekar--Bonga--
   Kesavan the energy is linear in the electric-mode boundary amplitude E and
   independent of B except through a linear coefficient, while E and B are
   independent phase-space coordinates.  Thus E ↦ -E with B fixed reverses the
   sign of the energy.  A nonnegative square cannot do this.  What is
   formalized here is the finite algebraic core: a sign-flippable energy that
   is everywhere a norm square must vanish identically. -/
namespace LinearizedFluxObstruction

variable {H : Type*} [Norm H]

structure SignFlipNewsModel where
  energy : H → ℝ
  flip : H → H
  news : H → H
  energy_flip : ∀ h : H, energy (flip h) = -energy h
  news_balance : ∀ h : H, energy h = ‖news h‖ ^ 2

theorem energy_zero_of_sign_flip_square
    (M : SignFlipNewsModel (H := H)) (h : H) :
    M.energy h = 0 := by
  have hE : 0 ≤ M.energy h := by
    rw [M.news_balance h]
    exact sq_nonneg _
  have hF : 0 ≤ M.energy (M.flip h) := by
    rw [M.news_balance (M.flip h)]
    exact sq_nonneg _
  rw [M.energy_flip h] at hF
  linarith

theorem no_sign_flip_square
    (M : SignFlipNewsModel (H := H)) {h : H} (hh : M.energy h ≠ 0) :
    False := by
  exact hh (energy_zero_of_sign_flip_square M h)

end LinearizedFluxObstruction

/- A rank-two news object is available only after strong equipment and a
   no-incoming condition.  Fernández-Álvarez--Senovilla define radiant news
   n^± = V + X^± on the cuts of a (strictly) equipped spacelike infinity and
   prove that the zero sets are the transverse radiant super-momenta Z^±.
   In the strongly equipped outgoing sector with S^2 leaves one can take
   X^+ = V, hence n^+ = 2V.  The finite algebraic core below records exactly
   this conditional identity and its zero-set consequence; it does not assert
   the geometric hypotheses. -/
namespace RadiantCutNews

structure StrongModel (N : Type*) [Zero N] [SMul ℝ N] where
  V : N
  nPlus : N
  nMinus : N
  Zplus : Prop
  Pzero : Prop
  Qminus : Prop
  nPlus_eq : nPlus = (2 : ℝ) • V
  nPlus_zero_iff_Zplus : nPlus = 0 ↔ Zplus
  Zplus_iff_Pzero : Zplus ↔ Pzero
  nMinus_zero_of_Qminus : Qminus → nMinus = 0
  two_smul_eq_zero_iff_V : ∀ v : N, (2 : ℝ) • v = 0 ↔ v = 0

theorem nPlus_zero_iff_V_zero [Zero N] [SMul ℝ N] (M : StrongModel N) :
    M.nPlus = 0 ↔ M.V = 0 := by
  rw [M.nPlus_eq]
  exact M.two_smul_eq_zero_iff_V M.V

theorem Zplus_iff_V_zero [Zero N] [SMul ℝ N] (M : StrongModel N) :
    M.Zplus ↔ M.V = 0 := by
  rw [← M.nPlus_zero_iff_Zplus]
  exact nPlus_zero_iff_V_zero M

theorem V_zero_iff_Pzero [Zero N] [SMul ℝ N] (M : StrongModel N) :
    M.V = 0 ↔ M.Pzero := by
  rw [← Zplus_iff_V_zero M]
  exact M.Zplus_iff_Pzero

theorem nMinus_zero_of_noIncoming [Zero N] [SMul ℝ N] (M : StrongModel N)
    (h : M.Qminus) : M.nMinus = 0 :=
  M.nMinus_zero_of_Qminus h

/- In the strongly equipped outgoing sector the rank-two news satisfies
   div n⁺ = S and n⁺ = 2V, so div V = (1/2)S.  This is the algebraic core of
   the round-cut inverse-elliptic formula; it does not assert the geometric
   hypotheses or the harmonic analysis. -/
namespace StrongOutgoingInversion

structure Model (News Source : Type*) [AddCommMonoid News] [Module ℝ News]
    [AddCommMonoid Source] [Module ℝ Source] where
  V : News
  nPlus : News
  source : Source
  div : News →ₗ[ℝ] Source
  nPlus_eq : nPlus = (2 : ℝ) • V
  div_nPlus : div nPlus = source

theorem div_V_eq_half_source [AddCommMonoid News] [Module ℝ News]
    [AddCommMonoid Source] [Module ℝ Source] (M : Model News Source) :
    M.div M.V = (1 / 2 : ℝ) • M.source := by
  have h2 : (2 : ℝ) • M.div M.V = M.source := by
    rw [← M.div_nPlus, M.nPlus_eq, map_smul]
  rw [← h2, smul_smul]
  norm_num

/- On a round cut the divergence of a symmetric trace-free tensor is injective,
   so the divergence equation determines n⁺ = 2V uniquely.  The conclusion is
   already an assumption of Model; this theorem records that it is forced by
   div n⁺ = S together with injectivity. -/
theorem nPlus_eq_twoV_of_div [AddCommMonoid News] [Module ℝ News]
    [AddCommMonoid Source] [Module ℝ Source] (M : Model News Source)
    (hinj : Function.Injective M.div) :
    M.nPlus = (2 : ℝ) • M.V := by
  apply hinj
  rw [M.div_nPlus, map_smul, div_V_eq_half_source M, smul_smul]
  norm_num

end StrongOutgoingInversion

end RadiantCutNews

/- Under the outgoing condition Q_-^μ = 0 Senovilla obtains
   p_m = -2(Ĉ_AB Ĉ^AB + C_A C^A).  This is exactly a square norm if the news
   object is allowed to live in STF ⊕ vector rather than only in STF tensors.
   The obstruction to a pointwise linear STF-tensor square is thereby evaded,
   at the price of leaving the rank-two tensor category. -/
namespace DetectorSquareNews

structure Pair (T2 T1 : Type*) where
  spin2 : T2
  vector : T1

structure Model (T2 T1 : Type*) [Zero T2] [Zero T1] where
  news : Pair T2 T1
  normalFlux : ℝ
  normSq : Pair T2 T1 → ℝ
  normSq_nonneg : ∀ p : Pair T2 T1, 0 ≤ normSq p
  normalFlux_eq : normalFlux = -2 * normSq news
  normSq_zero_iff : ∀ p : Pair T2 T1,
    normSq p = 0 ↔ p.spin2 = 0 ∧ p.vector = 0

theorem normalFlux_nonpos [Zero T2] [Zero T1] (M : Model T2 T1) :
    M.normalFlux ≤ 0 := by
  rw [M.normalFlux_eq]
  have h := M.normSq_nonneg M.news
  nlinarith

theorem normalFlux_zero_iff_news_zero [Zero T2] [Zero T1] (M : Model T2 T1) :
    M.normalFlux = 0 ↔ M.news.spin2 = 0 ∧ M.news.vector = 0 := by
  constructor
  · intro h
    have hs : M.normSq M.news = 0 := by
      rw [M.normalFlux_eq] at h
      nlinarith
    exact (M.normSq_zero_iff M.news).mp hs
  · intro h
    have hs : M.normSq M.news = 0 := (M.normSq_zero_iff M.news).mpr h
    rw [M.normalFlux_eq, hs]
    norm_num

end DetectorSquareNews

/- Conditional unification of the outgoing zero sets.  This records only the
   logical equivalences supplied by the geometry; it does not assert them. -/
namespace NewsZeroSetUnification

structure Model (State D R Q : Type*) where
  detector : State → D
  radiant : State → R
  charge : State → Q
  detectorZero : D → Prop
  radiantZero : R → Prop
  chargeZero : Q → Prop
  noRadiation : State → Prop
  detector_iff_charge : ∀ s, detectorZero (detector s) ↔ chargeZero (charge s)
  radiant_iff_charge : ∀ s, radiantZero (radiant s) ↔ chargeZero (charge s)
  charge_iff_noRadiation : ∀ s, chargeZero (charge s) ↔ noRadiation s

theorem detector_zero_iff_radiant_zero (M : Model State D R Q) (s : State) :
    M.detectorZero (M.detector s) ↔ M.radiantZero (M.radiant s) := by
  rw [M.detector_iff_charge s, M.radiant_iff_charge s]

theorem detector_zero_iff_no_radiation (M : Model State D R Q) (s : State) :
    M.detectorZero (M.detector s) ↔ M.noRadiation s := by
  rw [M.detector_iff_charge s, M.charge_iff_noRadiation s]

theorem radiant_zero_iff_no_radiation (M : Model State D R Q) (s : State) :
    M.radiantZero (M.radiant s) ↔ M.noRadiation s := by
  rw [M.radiant_iff_charge s, M.charge_iff_noRadiation s]

end NewsZeroSetUnification

/- Spectral magnitude obstruction.  The rank-two radiant news has the same zero
   set as the Cotton detector but can have arbitrarily smaller norm on high
   harmonics.  This records only the abstract consequence of arbitrarily small
   spectral ratios. -/
namespace SpectralNormMismatch

structure Model where
  detectorSq : ℕ → ℝ
  newsSq : ℕ → ℝ
  detectorSq_pos : ∀ n, 0 < detectorSq n
  small_ratio : ∀ ε : ℝ, 0 < ε → ∃ n, newsSq n < ε * detectorSq n

theorem no_uniform_lower_bound (M : Model) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n, c * M.detectorSq n ≤ M.newsSq n := by
  rintro ⟨c, hcpos, hbound⟩
  obtain ⟨n, hn⟩ := M.small_ratio c hcpos
  have hle := hbound n
  linarith

end SpectralNormMismatch

/- The round-cut operator J maps the vector detector component into a second
   STF tensor and preserves the L² norm on l ≥ 2.  Its algebraic core is an
   isometry, so a pair of STF tensors carries exactly the detector square. -/
namespace RankTwoTensorPairNews

structure VectorTensorIsometry (V T : Type*) [AddCommMonoid V] [Module ℝ V]
    [AddCommMonoid T] [Module ℝ T] where
  J : V →ₗ[ℝ] T
  sqV : V → ℝ
  sqT : T → ℝ
  sqV_nonneg : ∀ v : V, 0 ≤ sqV v
  sqT_nonneg : ∀ t : T, 0 ≤ sqT t
  sqV_zero_iff : ∀ v : V, sqV v = 0 ↔ v = 0
  sqT_zero_iff : ∀ t : T, sqT t = 0 ↔ t = 0
  J_isometry : ∀ v : V, sqT (J v) = sqV v

theorem J_zero_iff [AddCommMonoid V] [Module ℝ V] [AddCommMonoid T] [Module ℝ T]
    (I : VectorTensorIsometry V T) (v : V) :
    I.J v = 0 ↔ v = 0 := by
  rw [← I.sqT_zero_iff (I.J v), I.J_isometry v]
  exact I.sqV_zero_iff v

structure Model (T V : Type*) [AddCommMonoid T] [Module ℝ T]
    [AddCommMonoid V] [Module ℝ V] where
  I : VectorTensorIsometry V T
  hat : T
  vector : V
  normalFlux : ℝ
  flux_eq : normalFlux = -2 * (I.sqT hat + I.sqV vector)

theorem normalFlux_nonpos [AddCommMonoid T] [Module ℝ T]
    [AddCommMonoid V] [Module ℝ V] (M : Model T V) :
    M.normalFlux ≤ 0 := by
  rw [M.flux_eq]
  have hT := M.I.sqT_nonneg M.hat
  have hV := M.I.sqV_nonneg M.vector
  nlinarith

theorem normalFlux_zero_iff_news_zero [AddCommMonoid T] [Module ℝ T]
    [AddCommMonoid V] [Module ℝ V] (M : Model T V) :
    M.normalFlux = 0 ↔ M.hat = 0 ∧ M.vector = 0 := by
  constructor
  · intro hflux
    have hsum : M.I.sqT M.hat + M.I.sqV M.vector = 0 := by
      rw [M.flux_eq] at hflux
      nlinarith
    have hT0 : M.I.sqT M.hat = 0 := by
      have hT := M.I.sqT_nonneg M.hat
      have hV := M.I.sqV_nonneg M.vector
      nlinarith
    have hV0 : M.I.sqV M.vector = 0 := by
      have hT := M.I.sqT_nonneg M.hat
      have hV := M.I.sqV_nonneg M.vector
      nlinarith
    exact ⟨(M.I.sqT_zero_iff M.hat).mp hT0,
      (M.I.sqV_zero_iff M.vector).mp hV0⟩
  · intro h
    rcases h with ⟨hhat, hvec⟩
    rw [M.flux_eq]
    have hT0 : M.I.sqT M.hat = 0 := (M.I.sqT_zero_iff M.hat).mpr hhat
    have hV0 : M.I.sqV M.vector = 0 := (M.I.sqV_zero_iff M.vector).mpr hvec
    rw [hT0, hV0]
    norm_num

end RankTwoTensorPairNews

/- Conditional transport-square core: in the umbilical radiant sector the
   radiant superenergy density is the square of the equipment derivative of
   radiant news.  This records only the algebra of the FAS transport law. -/
namespace RadiantNewsTransport

structure Model (News : Type*) [Zero News] where
  nDot : News
  W : ℝ
  Nsq : ℝ
  sq : News → ℝ
  Nsq_pos : 0 < Nsq
  sq_nonneg : ∀ v : News, 0 ≤ sq v
  flux_eq : Nsq * W = sq nDot
  sq_zero_iff : ∀ v : News, sq v = 0 ↔ v = 0

theorem W_nonneg [Zero News] (M : Model News) : 0 ≤ M.W := by
  have hs := M.sq_nonneg M.nDot
  nlinarith [M.Nsq_pos, M.flux_eq]

theorem W_zero_iff_nDot_zero [Zero News] (M : Model News) :
    M.W = 0 ↔ M.nDot = 0 := by
  constructor
  · intro hW
    have hs : M.sq M.nDot = 0 := by
      rw [← M.flux_eq, hW]
      ring
    exact (M.sq_zero_iff M.nDot).mp hs
  · intro hn
    have hs : M.sq M.nDot = 0 := (M.sq_zero_iff M.nDot).mpr hn
    nlinarith [M.Nsq_pos, M.flux_eq]

end RadiantNewsTransport

/- First-jet radiant news.  FAS transport identifies the flux part with the
   trace-free Cotton detector and the inverse-divergence identifies the vector
   part; the round-cut isometry then turns the pair into two STF tensors with
   exactly the detector square.  This records the algebra only. -/
namespace RadiantJetNews

structure Model (State News V T : Type*) [AddCommMonoid V] [Module ℝ V]
    [AddCommMonoid T] [Module ℝ T] where
  I : RankTwoTensorPairNews.VectorTensorIsometry V T
  news : State → News
  detectorT : State → T
  detectorV : State → V
  fluxPart : News → T
  vectorPart : News → V
  normalFlux : State → ℝ
  fluxPart_sq : ∀ s : State, I.sqT (fluxPart (news s)) = I.sqT (detectorT s)
  vectorPart_eq : ∀ s : State, vectorPart (news s) = detectorV s
  normalFlux_eq : ∀ s : State,
    normalFlux s = -2 * (I.sqT (detectorT s) + I.sqV (detectorV s))

theorem jet_sq_eq_detector_sq {State News V T : Type*} [AddCommMonoid V] [Module ℝ V]
    [AddCommMonoid T] [Module ℝ T] (M : Model State News V T) (s : State) :
    M.I.sqT (M.fluxPart (M.news s))
      + M.I.sqT (M.I.J (M.vectorPart (M.news s)))
    =
    M.I.sqT (M.detectorT s) + M.I.sqV (M.detectorV s) := by
  rw [M.fluxPart_sq s, M.vectorPart_eq s, M.I.J_isometry]

theorem jet_sq_eq_neg_half_normalFlux {State News V T : Type*} [AddCommMonoid V] [Module ℝ V]
    [AddCommMonoid T] [Module ℝ T] (M : Model State News V T) (s : State) :
    M.I.sqT (M.fluxPart (M.news s))
      + M.I.sqT (M.I.J (M.vectorPart (M.news s)))
    =
    - M.normalFlux s / 2 := by
  rw [jet_sq_eq_detector_sq M s, M.normalFlux_eq s]
  ring

theorem jet_zero_iff_detector_zero {State News V T : Type*} [AddCommMonoid V] [Module ℝ V]
    [AddCommMonoid T] [Module ℝ T] (M : Model State News V T) (s : State) :
    (M.fluxPart (M.news s) = 0 ∧ M.I.J (M.vectorPart (M.news s)) = 0)
      ↔
    (M.detectorT s = 0 ∧ M.detectorV s = 0) := by
  constructor
  · rintro ⟨hF, hJ⟩
    refine ⟨?_, ?_⟩
    · have hF0 : M.I.sqT (M.fluxPart (M.news s)) = 0 := by
        rw [hF]
        exact (M.I.sqT_zero_iff 0).mpr rfl
      have hD0 : M.I.sqT (M.detectorT s) = 0 := by
        rw [← M.fluxPart_sq s]
        exact hF0
      exact (M.I.sqT_zero_iff (M.detectorT s)).mp hD0
    · have hv0 : M.vectorPart (M.news s) = 0 :=
        (RankTwoTensorPairNews.J_zero_iff M.I (M.vectorPart (M.news s))).mp hJ
      rw [← M.vectorPart_eq s]
      exact hv0
  · rintro ⟨hD, hV⟩
    refine ⟨?_, ?_⟩
    · have hF0 : M.I.sqT (M.fluxPart (M.news s)) = 0 := by
        rw [M.fluxPart_sq s, hD]
        exact (M.I.sqT_zero_iff 0).mpr rfl
      exact (M.I.sqT_zero_iff (M.fluxPart (M.news s))).mp hF0
    · have hv0 : M.vectorPart (M.news s) = 0 := by
        rw [M.vectorPart_eq s, hV]
      simp [hv0]

end RadiantJetNews

/- Finite charge fluxes are blind to part of the linearized news.  The model
   records only the logical consequence: vanishing news forces vanishing flux,
   but vanishing of every charge in a fixed finite family does not. -/
namespace ChargeFluxBlindness

structure Model (Phase News Charge : Type*) where
  news : Phase → News
  flux : Charge → Phase → ℝ
  newsZero : News → Prop
  news_zero_flux_zero : ∀ p : Phase, newsZero (news p) → ∀ c : Charge, flux c p = 0
  blindExample : ∃ p : Phase, (∀ c : Charge, flux c p = 0) ∧ ¬ newsZero (news p)

theorem news_zero_flux_zero {Phase News Charge : Type*} (M : Model Phase News Charge)
    (p : Phase) (hp : M.newsZero (M.news p)) (c : Charge) :
    M.flux c p = 0 :=
  M.news_zero_flux_zero p hp c

theorem not_flux_zero_imp_news_zero {Phase News Charge : Type*}
    (M : Model Phase News Charge) :
    ¬ ∀ p : Phase, (∀ c : Charge, M.flux c p = 0) → M.newsZero (M.news p) := by
  rintro h
  obtain ⟨p, hpflux, hpnews⟩ := M.blindExample
  exact hpnews (h p hpflux)

end ChargeFluxBlindness

/- Conformal weights force any rank-two realization of the first-jet news to
   use a nonlocal operator.  The detector tensor has lower weight -1 and the
   detector vector has lower weight -2; a rank-two tensor pair needs a map of
   weight +1.  Natural local tensor differential operators shift weight by an
   even integer, so this is impossible locally. -/
namespace ConformalWeightObstruction

def tensorDetectorWeight : ℤ := -1
def vectorDetectorWeight : ℤ := -2
def pmWeight : ℤ := -6

def lowerTensorSquareWeight (w : ℤ) : ℤ := 2 * w - 4
def lowerVectorSquareWeight (w : ℤ) : ℤ := 2 * w - 2

theorem tensor_square_weight :
    lowerTensorSquareWeight tensorDetectorWeight = pmWeight := by
  norm_num [lowerTensorSquareWeight, tensorDetectorWeight, pmWeight]

theorem vector_square_weight :
    lowerVectorSquareWeight vectorDetectorWeight = pmWeight := by
  norm_num [lowerVectorSquareWeight, vectorDetectorWeight, pmWeight]

def requiredMapShift : ℤ := tensorDetectorWeight - vectorDetectorWeight

theorem requiredMapShift_eq_one : requiredMapShift = 1 := by
  norm_num [requiredMapShift, tensorDetectorWeight, vectorDetectorWeight]

structure LocalTensorOperator where
  sourceWeight : ℤ
  targetWeight : ℤ
  halfShift : ℤ
  shift_eq : targetWeight - sourceWeight = 2 * halfShift

theorem no_local_rank_two_map (O : LocalTensorOperator)
    (hs : O.sourceWeight = vectorDetectorWeight)
    (ht : O.targetWeight = tensorDetectorWeight) : False := by
  have h := O.shift_eq
  rw [hs, ht] at h
  norm_num [tensorDetectorWeight, vectorDetectorWeight] at h
  omega

end ConformalWeightObstruction

/- Finite algebra for the arbitrary-cut polar-decomposition isometry.  This is
   the metric-dependent extension of the round-cut Hodge inverse; it does not
   assert conformal covariance. -/
namespace ArbitraryCutJetNews

structure PolarData (V T : Type*) [AddCommGroup V] [Module ℝ V]
    [AddCommGroup T] [Module ℝ T] where
  K : V →ₗ[ℝ] T
  S : V →ₗ[ℝ] V
  sqV : V → ℝ
  sqT : T → ℝ
  sqV_nonneg : ∀ v : V, 0 ≤ sqV v
  sqT_nonneg : ∀ t : T, 0 ≤ sqT t
  sqV_zero_iff : ∀ v : V, sqV v = 0 ↔ v = 0
  sqT_zero_iff : ∀ t : T, sqT t = 0 ↔ t = 0
  polar_isometry : ∀ v : V, sqT (K (S v)) = sqV v

def toIsometry {V T : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup T] [Module ℝ T]
    (P : PolarData V T) : RankTwoTensorPairNews.VectorTensorIsometry V T where
  J := P.K.comp P.S
  sqV := P.sqV
  sqT := P.sqT
  sqV_nonneg := P.sqV_nonneg
  sqT_nonneg := P.sqT_nonneg
  sqV_zero_iff := P.sqV_zero_iff
  sqT_zero_iff := P.sqT_zero_iff
  J_isometry := by
    intro v
    exact P.polar_isometry v

theorem J_zero_iff {V T : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup T] [Module ℝ T]
    (P : PolarData V T) (v : V) : P.K (P.S v) = 0 ↔ v = 0 := by
  rw [← P.sqT_zero_iff (P.K (P.S v)), P.polar_isometry v]
  exact P.sqV_zero_iff v

end ArbitraryCutJetNews

/- Finite scalar weight algebra for the conformally covariant weighted
   vector-to-tensor intertwiner.  This formalizes the Weyl bookkeeping only;
   elliptic invertibility and the round-sphere isometry are geometric inputs. -/
namespace ConformalJetIntertwiner

/- Scalar shadow of the weighted conformal-Killing intertwiner.  `A = μ^4 C`
   is the weight-two input, `S` is the weight-two STF output of
   `K P^{-1/2}`, and `T = μ^{-3} S` is the weight-minus-one final tensor. -/
structure Algebra where
  ω : ℝ
  μ : ℝ
  ω_ne : ω ≠ 0
  μ_ne : μ ≠ 0
  μ' : ℝ
  C : ℝ
  C' : ℝ
  A : ℝ
  A' : ℝ
  S : ℝ
  S' : ℝ
  T : ℝ
  T' : ℝ
  μ'_eq : μ' = ω * μ
  C'_eq : C' = (ω⁻¹)^2 * C
  A_eq : A = μ^4 * C
  A'_eq : A' = μ'^4 * C'
  Sinv_cov : S' = ω^2 * S
  T_eq : T = S / μ^3
  T'_eq : T' = S' / μ'^3

theorem input_weight (M : Algebra) : M.A' = M.ω^2 * M.A := by
  rw [M.A'_eq, M.A_eq, M.μ'_eq, M.C'_eq]
  field_simp [M.ω_ne]

theorem output_weight (M : Algebra) : M.T' = M.ω⁻¹ * M.T := by
  rw [M.T'_eq, M.Sinv_cov, M.μ'_eq, M.T_eq]
  field_simp [M.ω_ne, M.μ_ne]

structure NormAlgebra where
  ω : ℝ
  Csq : ℝ
  Csq' : ℝ
  Tsq : ℝ
  Tsq' : ℝ
  Csq'_eq : Csq' = (ω⁻¹)^4 * Csq
  Tsq'_eq : Tsq' = (ω⁻¹)^4 * Tsq
  base_isometry : Tsq = Csq

theorem jet_square_scaling (M : NormAlgebra) : M.Tsq' = M.Csq' := by
  rw [M.Tsq'_eq, M.Csq'_eq, M.base_isometry]

end ConformalJetIntertwiner

/- Algebraic core for the generalized (δ,γ) first-jet inversion.  R is the
   rotation acting on trace-free rank-two tensors. -/
namespace GeneralizedJetRotation

structure TensorRotation (T : Type*) [AddCommGroup T] [Module ℝ T] where
  R : T →ₗ[ℝ] T
  sq : T → ℝ
  sq_nonneg : ∀ x : T, 0 ≤ sq x
  sq_zero_iff : ∀ x : T, sq x = 0 ↔ x = 0
  sq_smul : ∀ a : ℝ, ∀ x : T, sq (a • x) = a ^ 2 * sq x
  sq_add_R : ∀ x y : T, sq (x + R y) = sq x + sq y
  R_sq : ∀ x : T, R (R x) = -x

theorem sq_inverse {T : Type*} [AddCommGroup T] [Module ℝ T]
    (M : TensorRotation T) {δ γ : ℝ} (hδγ : δ ^ 2 + γ ^ 2 ≠ 0) (x : T) :
    M.sq ((1 / (δ ^ 2 + γ ^ 2)) • (δ • x - γ • M.R x)) =
      M.sq x / (δ ^ 2 + γ ^ 2) := by
  have hsub : δ • x - γ • M.R x = δ • x + M.R ((-γ) • x) := by
    rw [sub_eq_add_neg]
    congr 1
    simp [map_smul]
  have hmain : M.sq (δ • x - γ • M.R x) = (δ ^ 2 + γ ^ 2) * M.sq x := by
    rw [hsub, M.sq_add_R, M.sq_smul, M.sq_smul]
    ring
  rw [M.sq_smul, hmain]
  field_simp [hδγ]

theorem inverse_zero_iff {T : Type*} [AddCommGroup T] [Module ℝ T]
    (M : TensorRotation T) {δ γ : ℝ} (hδγ : δ ^ 2 + γ ^ 2 ≠ 0) (x : T) :
    M.sq ((1 / (δ ^ 2 + γ ^ 2)) • (δ • x - γ • M.R x)) = 0 ↔ x = 0 := by
  rw [sq_inverse M hδγ x, div_eq_zero_iff]
  constructor
  · intro h
    rcases h with h | h
    · exact (M.sq_zero_iff x).mp h
    · exfalso
      exact hδγ h
  · intro hx
    left
    exact (M.sq_zero_iff x).mpr hx

end GeneralizedJetRotation

/- Conditional symplectic dual-news representation.  In the controlled linear
   sector the flux is a pairing of the news with a generator-dependent dual,
   not a universal news square.  The model records exactly that finite logic. -/
namespace SymplecticDualNews

structure Model (Phase News Charge : Type*) [Zero News] where
  news : Phase → News
  dual : Charge → News
  pair : News → News → ℝ
  flux : Charge → Phase → ℝ
  flux_eq_pair : ∀ ξ p, flux ξ p = pair (news p) (dual ξ)
  pair_zero_left : ∀ y : News, pair 0 y = 0
  pair_zero_right : ∀ x : News, pair x 0 = 0
  news_separates_dual : ∀ y : News, (∀ p : Phase, pair (news p) y = 0) → y = 0

theorem flux_zero_of_news_zero {Phase News Charge : Type*} [Zero News]
    (M : Model Phase News Charge)
    (ξ : Charge) (p : Phase) (hp : M.news p = 0) : M.flux ξ p = 0 := by
  rw [M.flux_eq_pair ξ p, hp, M.pair_zero_left]

theorem flux_zero_all_iff_dual_zero {Phase News Charge : Type*} [Zero News]
    (M : Model Phase News Charge) (ξ : Charge) :
    (∀ p : Phase, M.flux ξ p = 0) ↔ M.dual ξ = 0 := by
  constructor
  · intro h
    apply M.news_separates_dual (M.dual ξ)
    intro p
    rw [← M.flux_eq_pair ξ p]
    exact h p
  · intro hd p
    rw [M.flux_eq_pair ξ p, hd, M.pair_zero_right]

theorem not_square_of_sign_flip {Phase News Charge : Type*} [Zero News]
    (M : Model Phase News Charge)
    (flip : Phase → Phase) (sign : Charge → ℝ)
    (hflip : ∀ ξ p, M.flux ξ (flip p) = sign ξ * M.flux ξ p)
    (ξ : Charge) (hs : sign ξ ≠ 1) (p : Phase) (hflux : M.flux ξ p ≠ 0) :
    M.flux ξ (flip p) ≠ M.flux ξ p := by
  rw [hflip ξ p]
  intro h
  have : (sign ξ - 1) * M.flux ξ p = 0 := by linarith
  exact hs (sub_eq_zero.mp (mul_eq_zero.mp this |>.resolve_right hflux))

end SymplecticDualNews

/- Directional degeneracy in the FAS Λ→0 limit.  The omitted positive common
   factor is irrelevant to the zero-set implication formalized here. -/
namespace FlatLimitDirection

structure Model where
  B : ℝ
  qMinusLimit : ℝ
  qPlusLimit : ℝ
  Qflat : ℝ
  qMinus_eq : qMinusLimit = (1 - B) ^ 3 * Qflat
  qPlus_eq : qPlusLimit = (1 + B) ^ 3 * Qflat

theorem qMinus_zero_imp_Qflat_zero (M : Model) (hq : M.qMinusLimit = 0)
    (hB : M.B ≠ 1) : M.Qflat = 0 := by
  have h : (1 - M.B) ^ 3 * M.Qflat = 0 := by
    rw [← M.qMinus_eq]
    exact hq
  have hc : (1 - M.B) ^ 3 ≠ 0 := by
    exact pow_ne_zero 3 (sub_ne_zero.mpr (Ne.symm hB))
  exact (mul_eq_zero.mp h).resolve_left hc

theorem qPlus_zero_imp_Qflat_zero (M : Model) (hq : M.qPlusLimit = 0)
    (hB : M.B ≠ -1) : M.Qflat = 0 := by
  have h : (1 + M.B) ^ 3 * M.Qflat = 0 := by
    rw [← M.qPlus_eq]
    exact hq
  have hne : 1 + M.B ≠ 0 := by
    intro hzero
    apply hB
    linarith
  have hc : (1 + M.B) ^ 3 ≠ 0 := by
    exact pow_ne_zero 3 hne
  exact (mul_eq_zero.mp h).resolve_left hc

theorem qMinus_zero_Qflat_ne_zero_imp_B_one (M : Model) (hq : M.qMinusLimit = 0)
    (hQ : M.Qflat ≠ 0) : M.B = 1 := by
  by_contra hB
  exact hQ (qMinus_zero_imp_Qflat_zero M hq hB)

end FlatLimitDirection

/- Exact scaling algebra for the first-jet Λ→0 limit.  Here W and Z are the
   outgoing radiant densities, alpha=N²W and beta=N²Z are the coefficients of
   the rescaled supermomentum in the finite K± basis, and phiSq=W/8, vectorSq=Z/4
   after the no-incoming detector identification. -/
namespace FirstJetFlatScaling

structure Algebra where
  N : ℝ
  W : ℝ
  Z : ℝ
  alpha : ℝ
  beta : ℝ
  phiSq : ℝ
  vectorSq : ℝ
  jetSq : ℝ
  alpha_eq : alpha = N ^ 2 * W
  beta_eq : beta = N ^ 2 * Z
  phi_eq : phiSq = W / 4
  vector_eq : vectorSq = Z / 4
  jet_eq : jetSq = phiSq + vectorSq

theorem scaled_phi_eq (M : Algebra) : M.N ^ 2 * M.phiSq = M.alpha / 4 := by
  rw [M.phi_eq, M.alpha_eq]
  ring

theorem scaled_vector_eq (M : Algebra) : M.N ^ 2 * M.vectorSq = M.beta / 4 := by
  rw [M.vector_eq, M.beta_eq]
  ring

theorem scaled_jet_eq (M : Algebra) :
    M.N ^ 2 * M.jetSq = M.alpha / 4 + M.beta / 4 := by
  rw [M.jet_eq, mul_add, scaled_phi_eq M, scaled_vector_eq M]

theorem phi_sq_zero_iff (M : Algebra) : M.phiSq = 0 ↔ M.W = 0 := by
  rw [M.phi_eq, div_eq_zero_iff]
  norm_num

theorem tendsto_scaled_phi {ι : Type*} (l : Filter ι) (N W phiSq : ι → ℝ) (q : ℝ)
    (hphi : ∀ i, phiSq i = W i / 4)
    (hW : Filter.Tendsto (fun i => N i ^ 2 * W i) l (nhds q)) :
    Filter.Tendsto (fun i => N i ^ 2 * phiSq i) l (nhds (q / 4)) := by
  have hfun : (fun i => N i ^ 2 * phiSq i) = fun i => (N i ^ 2 * W i) / 4 := by
    funext i
    rw [hphi i]
    ring
  rw [hfun]
  have hc : Filter.Tendsto (fun _ : ι => (1 / 4 : ℝ)) l (nhds (1 / 4 : ℝ)) := tendsto_const_nhds
  simpa [div_eq_mul_inv] using hW.mul hc

theorem tendsto_scaled_vector {ι : Type*} (l : Filter ι) (N Z vectorSq : ι → ℝ) (q : ℝ)
    (hvec : ∀ i, vectorSq i = Z i / 4)
    (hZ : Filter.Tendsto (fun i => N i ^ 2 * Z i) l (nhds q)) :
    Filter.Tendsto (fun i => N i ^ 2 * vectorSq i) l (nhds (q / 4)) := by
  have hfun : (fun i => N i ^ 2 * vectorSq i) = fun i => (N i ^ 2 * Z i) / 4 := by
    funext i
    rw [hvec i]
    ring
  rw [hfun]
  have hc : Filter.Tendsto (fun _ : ι => (1 / 4 : ℝ)) l (nhds (1 / 4 : ℝ)) := tendsto_const_nhds
  simpa [div_eq_mul_inv] using hZ.mul hc

theorem tendsto_scaled_jet {ι : Type*} (l : Filter ι)
    (N W Z phiSq vectorSq jetSq : ι → ℝ) (qW qZ : ℝ)
    (hphi : ∀ i, phiSq i = W i / 4)
    (hvec : ∀ i, vectorSq i = Z i / 4)
    (hjet : ∀ i, jetSq i = phiSq i + vectorSq i)
    (hW : Filter.Tendsto (fun i => N i ^ 2 * W i) l (nhds qW))
    (hZ : Filter.Tendsto (fun i => N i ^ 2 * Z i) l (nhds qZ)) :
    Filter.Tendsto (fun i => N i ^ 2 * jetSq i) l (nhds (qW / 4 + qZ / 4)) := by
  have hfun : (fun i => N i ^ 2 * jetSq i) =
      fun i => N i ^ 2 * phiSq i + N i ^ 2 * vectorSq i := by
    funext i
    rw [hjet i, mul_add]
  rw [hfun]
  exact (tendsto_scaled_phi l N W phiSq qW hphi hW).add
    (tendsto_scaled_vector l N Z vectorSq qZ hvec hZ)

end FirstJetFlatScaling

/- Fernández--Álvarez--Senovilla's regular Λ→0 detector limit.  This encodes
   only the implication: regular metric limit + de Sitter no radiation implies
   flat news vanishes.  It does not assert the geometric hypotheses or give a
   flat limit of V or n⁺. -/
namespace FlatLimitConstraint

structure Model where
  RegularLimit : Prop
  NoRadiationLambda : Prop
  FlatSuperMomentumZero : Prop
  FlatNewsZero : Prop
  limit_noRad : RegularLimit → NoRadiationLambda → FlatSuperMomentumZero
  flat_superMomentum_zero_iff_news_zero : FlatSuperMomentumZero ↔ FlatNewsZero

theorem flat_news_zero (M : Model) (hreg : M.RegularLimit)
    (hnorad : M.NoRadiationLambda) : M.FlatNewsZero :=
  M.flat_superMomentum_zero_iff_news_zero.mp (M.limit_noRad hreg hnorad)

end FlatLimitConstraint

end PNP.LambdaPositiveBondi
