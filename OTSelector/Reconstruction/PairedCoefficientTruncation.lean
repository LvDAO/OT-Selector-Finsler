import OTSelector.Reconstruction.OriginalSeedPairCoefficient
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform truncation of the original inverse coefficient

The original conditional moments control the first moment beyond any coefficient
cutoff, uniformly over all legal pairings of the same two conditional laws. The
cutoff depends on their fixed-root moments, not on the coupling.
-/

open Set Matrix Module Manifold MeasureTheory Filter
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Geometry ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

/-- On a norm tail, an exponent greater than one controls the first power. -/
theorem norm_le_rpow_div_on_tail {V : Type*} [NormedAddCommGroup V]
    (v : V) {r R : ℝ} (hr : 1 < r) (hR : 0 < R) (hv : R < ‖v‖) :
    ‖v‖ ≤ ‖v‖ ^ r / R ^ (r - 1) := by
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hR _)).mpr
  calc
    ‖v‖ * R ^ (r - 1) ≤ ‖v‖ * ‖v‖ ^ (r - 1) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hR.le hv.le (sub_pos.mpr hr).le)
        (norm_nonneg _)
    _ = ‖v‖ ^ (1 : ℝ) * ‖v‖ ^ (r - 1) := by rw [Real.rpow_one]
    _ = ‖v‖ ^ r := by
      rw [← Real.rpow_add (hR.trans hv)]
      congr 1
      ring

/-- A finite higher norm moment gives a quantitative first-moment tail bound. -/
theorem integral_norm_tail_le_rpow {Ω V : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    {μ : Measure Ω} {f : Ω → V} (hf : Measurable f)
    {r R : ℝ} (hr : 1 < r) (hR : 0 < R)
    (hm : Integrable (fun x ↦ ‖f x‖ ^ r) μ) :
    IntegrableOn (fun x ↦ ‖f x‖) {x | R < ‖f x‖} μ ∧
      (∫ x in {x | R < ‖f x‖}, ‖f x‖ ∂μ) ≤
        (∫ x, ‖f x‖ ^ r ∂μ) / R ^ (r - 1) := by
  have hs : MeasurableSet {x | R < ‖f x‖} := measurableSet_lt measurable_const hf.norm
  have hdom : ∀ᵐ x ∂μ.restrict {x | R < ‖f x‖},
      ‖f x‖ ≤ ‖f x‖ ^ r / R ^ (r - 1) := by
    filter_upwards [ae_restrict_mem hs] with x hx
    exact norm_le_rpow_div_on_tail (f x) hr hR hx
  have hi : IntegrableOn (fun x ↦ ‖f x‖) {x | R < ‖f x‖} μ :=
    (hm.div_const _).integrableOn.mono_nonneg hf.norm.aestronglyMeasurable.restrict
      (ae_of_all _ (fun x ↦ norm_nonneg _)) hdom
  refine ⟨hi, (integral_mono_ae hi (hm.div_const _).integrableOn hdom).trans ?_⟩
  calc
    (∫ x in {x | R < ‖f x‖}, ‖f x‖ ^ r / R ^ (r - 1) ∂μ) ≤
        ∫ x, ‖f x‖ ^ r / R ^ (r - 1) ∂μ :=
      setIntegral_le_integral (hm.div_const _) (ae_of_all _ (fun x ↦ by positivity))
    _ = _ := integral_div _ _

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The explicit pairing-independent bound supplied by the two original marginal moments. -/
def originalSeedMomentBound (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (μ ν : Measure ℝ) (root r : ℝ) : ℝ :=
  (2 : ℝ) ^ max (r - 1) 0 *
    ((∫ x, ‖∫ t in root..(x - S.level), originalSeedKernel S w t‖ ^ r ∂μ) +
      ∫ y, ‖∫ t in root..(y - S.level), originalSeedKernel S w t‖ ^ r ∂ν)

namespace OriginalSeedConditionalMoments

variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Every legal pairing obeys the same quantitative inverse-coefficient tail bound. -/
theorem paired_inverse_coefficient_tail_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {root : ℝ} (hroot : root ∈ Ioo D.lo D.hi)
    {π : Measure (ℝ × ℝ)} (hπ : Vlasov.IsCoupling π μ ν)
    (hforward : ∀ᵐ p ∂π, p.1 < p.2)
    {r R : ℝ} (hr : 1 < r) (hr2 : r < 2) (hR : 0 < R) :
    IntegrableOn (fun p ↦ ‖(originalSeedPairCoefficient S w p)⁻¹‖)
      {p | R < ‖(originalSeedPairCoefficient S w p)⁻¹‖} π ∧
      (∫ p in {p | R < ‖(originalSeedPairCoefficient S w p)⁻¹‖},
        ‖(originalSeedPairCoefficient S w p)⁻¹‖ ∂π) ≤
        originalSeedMomentBound S w μ ν root r / R ^ (r - 1) := by
  have hm := D.paired_inverse_coefficient_moments hF hw hroot hπ hforward
    (zero_lt_one.trans hr) hr2
  have hmeas := measurable_real_matrix_inverse.comp
    (measurable_originalSeedPairCoefficient S hF hw)
  have ht := integral_norm_tail_le_rpow hmeas hr hR hm.1
  exact ⟨ht.1, ht.2.trans (div_le_div_of_nonneg_right hm.2
    (Real.rpow_nonneg hR.le _))⟩

/-- A single cutoff makes inverse-coefficient tails small for all legal pairings. -/
theorem exists_uniform_inverse_coefficient_cutoff
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {root : ℝ} (hroot : root ∈ Ioo D.lo D.hi)
    {r ε : ℝ} (hr : 1 < r) (hr2 : r < 2) (hε : 0 < ε) :
    ∃ R > 0, ∀ π : Measure (ℝ × ℝ), Vlasov.IsCoupling π μ ν →
      (∀ᵐ p ∂π, p.1 < p.2) →
      (∫ p in {p | R < ‖(originalSeedPairCoefficient S w p)⁻¹‖},
        ‖(originalSeedPairCoefficient S w p)⁻¹‖ ∂π) < ε := by
  have hlim : Tendsto (fun R : ℝ ↦
      originalSeedMomentBound S w μ ν root r / R ^ (r - 1)) atTop (𝓝 0) := by
    have hneg := (tendsto_rpow_neg_atTop (sub_pos.mpr hr)).const_mul
      (originalSeedMomentBound S w μ ν root r)
    simp only [mul_zero] at hneg
    refine hneg.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [Real.rpow_neg hR.le, div_eq_mul_inv]
  obtain ⟨R, hR, hsmall⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (hlim.eventually (gt_mem_nhds hε))).exists
  refine ⟨R, hR, fun π hπ hforward ↦ ?_⟩
  exact (D.paired_inverse_coefficient_tail_bound hF hw hroot hπ hforward hr hr2 hR).2.trans_lt
    hsmall

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
