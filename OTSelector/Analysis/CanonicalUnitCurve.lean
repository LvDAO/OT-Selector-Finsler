import OTSelector.Analysis.ContractivePairCurve
import OTSelector.Analysis.ContractivePerturbationCurveBounds
import OTSelector.Analysis.ContractivePerturbationInverse
import OTSelector.Finite.LatticePairCoordinates
import OTSelector.Finite.LatticePairNormBounds
import OTSelector.MeasureTheory.MeasurableFieldReindex
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.CanonicalUnitPhaseCurve.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.CanonicalUnitPhaseCurve`; the selected original proof blocks follow. -/
section

/-!
# Analysis.CanonicalUnitCurve

Conditions: The explicit complete normed-space contraction assumptions; measurable statements add a measurable field, mobility and the stated Borel/countability instances.
Objects: The literal inverse at target zero after zero extension of the unit-clock mobility, and its finite-dimensional position/momentum pairing.
Proof detail: Zero-extend mobility, apply the same uniquely defined inverse, prove joint measurability by reindexing the measured inverse field, and identify prior existential curves by uniqueness to reuse all bounds.

## Mathematical sources

- Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (author version)*: Section 2.1, Theorem 2.1 (Contraction principle), pp. 35–36. https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=46
- D. H. Fremlin, *Measure Theory, Volume 4*: Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces. https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106
- OT-Selector project, *Empirical optimal transport selection on general Finsler manifolds, main.tex*: Lemma lem:highd-perturbed-traffic, proof paragraph defining F_r and its inverse trajectory; phase-tube and rescaling bounds. ../main.tex#L3688

Source relation: A canonical measurable packaging of the existing contractive inverse. The construction keeps the original clock/environment and proves contributor bounds for that same curve.
-/

/-! Literal canonical inverse curves on the original unit clock interval. -/
open Set Function MeasureTheory
open scoped Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Extend the actual unit-interval mobility by zero; no smallness away from
the original curve interval is required. -/
def unitPhaseMobility (R : ℝ → V →L[ℝ] V) : ℝ → V →L[ℝ] V := (Icc (0 : ℝ) 1).indicator R

theorem unitPhaseMobility_small (R : ℝ → V →L[ℝ] V) {L : ℝ}
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * L ≤ (1 / 2 : ℝ)) (r : ℝ) :
    ‖unitPhaseMobility R r‖ * L ≤ (1 / 2 : ℝ) := by
  by_cases hr : r ∈ Icc (0 : ℝ) 1
  · simpa only [unitPhaseMobility, indicator_of_mem hr] using hsmall r hr
  · simp only [unitPhaseMobility, indicator_of_notMem hr, norm_zero, zero_mul]
    norm_num

/-- The same unique inverse at target zero, with its full curve parameter retained. -/
def canonicalUnitPhasePosition (P : V → V) {L : ℝ}
    (hP : ∀ z y, ‖P z - P y‖ ≤ L * ‖z - y‖)
    (R : ℝ → V →L[ℝ] V)
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * L ≤ (1 / 2 : ℝ)) (r : ℝ) : V :=
  phaseInverseAt P hP (unitPhaseMobility R r) (unitPhaseMobility_small R hsmall r) 0

/-- Joint measurability keeps the complete original environment and actual clock parameter. -/
theorem measurable_canonicalUnitPhasePosition
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {Ω : Type*} [MeasurableSpace Ω] {P : Ω → V → V} {L : ℝ}
    (hP : Measurable (uncurry P))
    (hLip : ∀ ω z y, ‖P ω z - P ω y‖ ≤ L * ‖z - y‖)
    (R : ℝ → V →L[ℝ] V) (hR : Measurable R)
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * L ≤ (1 / 2 : ℝ)) :
    Measurable (fun a : Ω × ℝ ↦ canonicalUnitPhasePosition (P a.1) (hLip a.1) R hsmall a.2) := by
  have hfield := measurable_phaseField_reindex (P := P) hP
    (r := fun a : Ω × ℝ ↦ a.1) measurable_fst
  have hRext : Measurable (fun a : Ω × ℝ ↦ unitPhaseMobility R a.2) :=
    (hR.indicator measurableSet_Icc).comp measurable_snd
  have hi := measurable_phaseInverseAt hfield hRext (fun a ↦ hLip a.1)
    (fun a ↦ unitPhaseMobility_small R hsmall a.2)
  exact hi.comp (measurable_id.prodMk measurable_const)

variable {q : ℕ}

/-- The actual position-momentum curve associated with the canonical inverse. -/
def canonicalUnitPhasePair (P : (Fin q → ℝ) → Fin q → ℝ) {L : ℝ}
    (hP : ∀ z y, ‖P z - P y‖ ≤ L * ‖z - y‖)
    (R : ℝ → (Fin q → ℝ) →L[ℝ] (Fin q → ℝ))
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * L ≤ (1 / 2 : ℝ))
    (r : ℝ) : Fin (2 * q) → ℝ :=
  phasePairVector (canonicalUnitPhasePosition P hP R hsmall r)
    (P (canonicalUnitPhasePosition P hP R hsmall r))

theorem measurable_canonicalUnitPhasePair
    {Ω : Type*} [MeasurableSpace Ω] {P : Ω → (Fin q → ℝ) → Fin q → ℝ} {L : ℝ}
    (hP : Measurable (uncurry P))
    (hLip : ∀ ω z y, ‖P ω z - P ω y‖ ≤ L * ‖z - y‖)
    (R : ℝ → (Fin q → ℝ) →L[ℝ] (Fin q → ℝ)) (hR : Measurable R)
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * L ≤ (1 / 2 : ℝ)) :
    Measurable (fun a : Ω × ℝ ↦ canonicalUnitPhasePair (P a.1) (hLip a.1) R hsmall a.2) := by
  have hz := measurable_canonicalUnitPhasePosition hP hLip R hR hsmall
  have hp := measurable_phaseField_apply (P := P) hP measurable_fst hz
  apply measurable_pi_lambda
  intro i
  by_cases hi : (i : ℕ) < q
  · simp only [canonicalUnitPhasePair, phasePairVector, dite_eq_left hi]
    exact (measurable_pi_apply ⟨i, hi⟩).comp hz
  · simp only [canonicalUnitPhasePair, phasePairVector, dite_eq_right hi]
    exact (measurable_pi_apply ⟨(i : ℕ) - q, by omega⟩).comp hp

/-- A single original contributor lies in the fixed canonical phase tube,
using only its actual phase position and actual node approximation error. -/
theorem canonicalUnitPhasePair_contributor
    {P : (Fin q → ℝ) → Fin q → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hP : ∀ z y, ‖P z - P y‖ ≤ L * ‖z - y‖)
    (R : ℝ → (Fin q → ℝ) →L[ℝ] (Fin q → ℝ))
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * L ≤ (1 / 2 : ℝ))
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1)
    {ρ a b : ℝ} (hR : ‖R r‖ ≤ ρ) {x p : Fin q → ℝ}
    (hphysical : ‖x + R r p‖ ≤ a) (hrough : ‖p - P x‖ ≤ b) :
    ‖phasePairVector x p - canonicalUnitPhasePair P hP R hsmall r‖ ≤
      max (2 * (a + ρ * b)) (b + 2 * L * (a + ρ * b)) := by
  have hz : canonicalUnitPhasePosition P hP R hsmall r +
      R r (P (canonicalUnitPhasePosition P hP R hsmall r)) = 0 := by
    simpa only [canonicalUnitPhasePosition, unitPhaseMobility, indicator_of_mem hr] using
      phaseInverseAt_eq hP (unitPhaseMobility R r) (unitPhaseMobility_small R hsmall r) 0
  apply (norm_phasePairVector_sub_le _ _ _ _).trans
  apply max_le_max
  · exact norm_actual_phasePosition_sub_zero_le hP (hsmall r hr) hz hR hphysical hrough
  · exact norm_actual_phaseMomentum_sub_zero_le hL hP (hsmall r hr) hz hR hphysical hrough

/-- Existing contraction estimates apply to the literal canonical curve,
including every physical contributor; no new inverse-curve choice is made. -/
theorem canonicalUnitPhasePair_bounds
    {P : (Fin q → ℝ) → Fin q → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hP : ∀ z y, ‖P z - P y‖ ≤ L * ‖z - y‖)
    (R : ℝ → (Fin q → ℝ) →L[ℝ] (Fin q → ℝ))
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * L ≤ (1 / 2 : ℝ))
    {ρ A : ℝ} (hρ : 0 ≤ ρ) (hA : 0 ≤ A)
    (hR : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ ρ)
    (hRLip : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖R r - R s‖ ≤ A * |r - s|) :
    (∀ r ∈ Icc (0 : ℝ) 1,
      canonicalUnitPhasePosition P hP R hsmall r +
        R r (P (canonicalUnitPhasePosition P hP R hsmall r)) = 0) ∧
    (∀ r ∈ Icc (0 : ℝ) 1,
      ‖canonicalUnitPhasePair P hP R hsmall r‖ ≤ 2 * (ρ + 1) * ‖P 0‖) ∧
    (∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖canonicalUnitPhasePair P hP R hsmall r - canonicalUnitPhasePair P hP R hsmall s‖ ≤
        4 * (1 + L) * A * ‖P 0‖ * |r - s|) ∧
    ∀ r ∈ Icc (0 : ℝ) 1, ∀ x p : Fin q → ℝ, ∀ a b : ℝ,
      ‖x + R r p‖ ≤ a → ‖p - P x‖ ≤ b →
        ‖phasePairVector x p - canonicalUnitPhasePair P hP R hsmall r‖ ≤
          max (2 * (a + ρ * b)) (b + 2 * L * (a + ρ * b)) := by
  obtain ⟨z, γ, hz, hγ, hroot, hspeed, htube⟩ :=
    exists_contractive_phasePairCurve hL hP R hsmall hρ hA hR hRLip
  have hcanon (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      z r = canonicalUnitPhasePosition P hP R hsmall r := by
    apply phaseInverseAt_unique hP (unitPhaseMobility R r) (unitPhaseMobility_small R hsmall r)
    simpa only [unitPhaseMobility, indicator_of_mem hr] using hz r hr
  have hpair (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      γ r = canonicalUnitPhasePair P hP R hsmall r := by
    rw [hγ r, hcanon r hr]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    rw [← hcanon r hr]
    exact hz r hr
  · intro r hr
    rw [← hpair r hr]
    exact hroot r hr
  · intro r hr s hs
    rw [← hpair r hr, ← hpair s hs]
    exact hspeed r hr s hs
  · intro r hr x p a b hphysical hrough
    rw [← hpair r hr]
    exact htube r hr x p a b hphysical hrough

end OTSelector.Reconstruction

end
end
