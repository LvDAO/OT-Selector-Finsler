import OTSelector.Reconstruction.FinslerOriginalLegalClockOrderMoments

/-!
# Finite clock-marginal second moments from compact clock support

`FinslerOriginalLegalClockOrderMoments` reduced the unconditional nonemptiness of
the abstract bounded second-moment class to the finite second moments of the two
original clock marginals `α`, `β`.  Those clock laws are the height marginals of
the legal Poisson inputs; in the legal Poisson pipeline their supports are the
compact scalar windows used by the finite scalar bins (the same compact supports
`A`, `B` that appear as hypotheses of the reserve construction).

This file derives the finite second moments from that concrete compact support:

* `integrable_sq_of_compact_support`: a finite measure supported in a compact set
  has a finite square moment, since the square is bounded on the compact set.
* `exists_integral_sq_le_of_compact_support`: additionally an explicit nonnegative
  bound `R^2` on the square moment, where `R` bounds the compact support.
* `integrable_sq_clockLaws_of_compact_support`: both clock marginals of the legal
  matching have finite second moments.
* `nonempty_boundedSecondMomentClass_legal_compact`: the unconditional capstone;
  the abstract bounded second-moment class is nonempty for every legal stationary
  Poisson matching whose clock laws are probability laws supported in compact
  sets.
* `exists_nonnegative_bound_boundedSecondMomentClass_legal_compact`: the same with
  an explicit nonnegative bound `2 R_A^2 + 2 R_B^2` on the class.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology
  OTSelector.PointProcess OTSelector.Probability
open scoped Topology ENNReal BigOperators

noncomputable section

namespace OTSelector.Reconstruction

open OTSelector.PointProcess
open OTSelector.PointProcess.StationaryForwardMatching

variable {q : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-! ## Square moments from compact support -/

/-- A finite measure supported in a compact set has a finite square moment. -/
theorem integrable_sq_of_compact_support {μ : Measure ℝ} [IsFiniteMeasure μ]
    {A : Set ℝ} (hA : IsCompact A) (hμ : μ Aᶜ = 0) :
    Integrable (fun t : ℝ ↦ t ^ 2) μ := by
  obtain ⟨R, hR⟩ := hA.isBounded.exists_norm_le
  refine Integrable.of_bound
    (by fun_prop : Measurable fun t : ℝ ↦ t ^ 2).aestronglyMeasurable (R ^ 2) ?_
  filter_upwards [ae_iff.mpr hμ] with t ht
  have h := hR t ht
  rw [Real.norm_eq_abs] at h
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
  nlinarith [h, abs_nonneg t, sq_abs t]

/-- The square moment of a probability measure supported in a compact set is
bounded by the squared norm bound `R^2` of the support. -/
theorem exists_integral_sq_le_of_compact_support {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {A : Set ℝ} (hA : IsCompact A) (hμ : μ Aᶜ = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ Integrable (fun t : ℝ ↦ t ^ 2) μ ∧
      ∫ t : ℝ, t ^ 2 ∂μ ≤ C := by
  obtain ⟨R, hR⟩ := hA.isBounded.exists_norm_le
  have hInt := integrable_sq_of_compact_support hA hμ
  refine ⟨R ^ 2, sq_nonneg R, hInt, ?_⟩
  have hae : ∀ᵐ t ∂μ, (fun t : ℝ ↦ t ^ 2) t ≤ R ^ 2 := by
    filter_upwards [ae_iff.mpr hμ] with t ht
    have h := hR t ht
    rw [Real.norm_eq_abs] at h
    nlinarith [h, abs_nonneg t, sq_abs t]
  have hmono : ∫ t : ℝ, t ^ 2 ∂μ ≤ ∫ _ : ℝ, R ^ 2 ∂μ :=
    integral_mono_ae hInt (integrable_const (R ^ 2)) hae
  have hconst : (∫ _ : ℝ, R ^ 2 ∂μ) = R ^ 2 := by
    rw [integral_const, smul_eq_mul, Measure.real, measure_univ, ENNReal.toReal_one,
      one_mul]
  linarith

/-! ## The two clock marginals of the legal matching -/

/-- With probability clock laws supported in compact sets, both clock marginals of
the legal stationary Poisson matching have finite second moments. -/
theorem integrable_sq_clockLaws_of_compact_support
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {A Bs : Set ℝ} (hA : IsCompact A) (hBs : IsCompact Bs)
    (hα : α Aᶜ = 0) (hβ : β Bsᶜ = 0) :
    Integrable (fun t : ℝ ↦ t ^ 2) α ∧ Integrable (fun t : ℝ ↦ t ^ 2) β :=
  ⟨integrable_sq_of_compact_support hA hα,
    integrable_sq_of_compact_support hBs hβ⟩

/-! ## Unconditional nonemptiness of the abstract bounded class -/

/-- Unconditional capstone: for every legal stationary Poisson matching whose clock
laws are probability laws supported in compact sets, the abstract bounded
second-moment class of the recoded legal Palm is nonempty. -/
theorem nonempty_boundedSecondMomentClass_legal_compact
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {A Bs : Set ℝ} (hA : IsCompact A) (hBs : IsCompact Bs)
    (hα : α Aᶜ = 0) (hβ : β Bsᶜ = 0) :
    ∃ Bnd : ℝ,
      (boundedSecondMomentClass
        (α := (legalMarkedJointPalm q Q.law).map carrierRecodePair |>.map
          (fun p ↦ p.1.2))
        (β := (legalMarkedJointPalm q Q.law).map carrierRecodePair |>.map
          (fun p ↦ p.2.2)) Bnd).Nonempty :=
  nonempty_boundedSecondMomentClass_legal_unconditional Q
    (integrable_sq_of_compact_support hA hα)
    (integrable_sq_of_compact_support hBs hβ)

/-- Explicit-bound capstone: an explicit nonnegative bound `2 R_A^2 + 2 R_B^2`,
where `R_A`, `R_B` bound the compact clock supports, makes the abstract bounded
second-moment class of the recoded legal Palm nonempty. -/
theorem exists_nonnegative_bound_boundedSecondMomentClass_legal_compact
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {A Bs : Set ℝ} (hA : IsCompact A) (hBs : IsCompact Bs)
    (hα : α Aᶜ = 0) (hβ : β Bsᶜ = 0) :
    ∃ Bnd : ℝ, 0 ≤ Bnd ∧
      (boundedSecondMomentClass
        (α := (legalMarkedJointPalm q Q.law).map carrierRecodePair |>.map
          (fun p ↦ p.1.2))
        (β := (legalMarkedJointPalm q Q.law).map carrierRecodePair |>.map
          (fun p ↦ p.2.2)) Bnd).Nonempty := by
  obtain ⟨Cα, hCα0, hIntα, hleα⟩ :=
    exists_integral_sq_le_of_compact_support hA hα
  obtain ⟨Cβ, hCβ0, hIntβ, hleβ⟩ :=
    exists_integral_sq_le_of_compact_support hBs hβ
  refine ⟨2 * Cα + 2 * Cβ, by linarith, ?_⟩
  have hIntRec := integrable_edgeDisplacement_sq_carrierRecodedLegalPalm Q hIntα hIntβ
  have hkle := integral_clockDiff_sq_le Q hIntα hIntβ
  have hEq := integral_edgeDisplacement_sq_carrierRecodedLegalPalm Q
  have hB : ∫ p : MarkedCloudPoint × MarkedCloudPoint, edgeDisplacement p ^ 2
      ∂(carrierRecodedLegalPalm Q) ≤ 2 * Cα + 2 * Cβ := by
    rw [hEq]
    linarith [hkle, hleα, hleβ]
  exact nonempty_boundedSecondMomentClass_carrierRecodedLegalPalm Q
    (ae_carrierRecodedLegalPalm_forward Q) hIntRec hB

end OTSelector.Reconstruction

end
