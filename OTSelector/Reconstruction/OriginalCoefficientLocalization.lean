import OTSelector.Reconstruction.PairedCoefficientTruncation

/-!
# Localization of the original inverse coefficient

Uniform higher moments give uniform absolute continuity of inverse-coefficient
integrals over all legal pairings. The removed measurable event may depend on the
pairing; no independent screening law is needed.
-/

open Set Matrix Module Manifold MeasureTheory Filter
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Geometry ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

/-- An arbitrary removed event is controlled by its mass and the common norm tail. -/
theorem setIntegral_norm_le_cutoff {Ω V : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → V} (hf : Measurable f)
    (hi : Integrable (fun x ↦ ‖f x‖) μ) {R : ℝ} (hR : 0 ≤ R)
    {s : Set Ω} (hs : MeasurableSet s) :
    (∫ x in s, ‖f x‖ ∂μ) ≤ R * μ.real s + ∫ x in {x | R < ‖f x‖}, ‖f x‖ ∂μ := by
  have ht : MeasurableSet {x | R < ‖f x‖} := measurableSet_lt measurable_const hf.norm
  have hpoint (x : Ω) : s.indicator (fun x ↦ ‖f x‖) x ≤
      s.indicator (fun _ ↦ R) x + {x | R < ‖f x‖}.indicator (fun x ↦ ‖f x‖) x := by
    by_cases hx : x ∈ s
    · by_cases hrx : R < ‖f x‖
      · simp only [indicator_of_mem hx,
          indicator_of_mem (show x ∈ {x | R < ‖f x‖} from hrx)]
        linarith
      · simpa only [indicator_of_mem hx,
          indicator_of_notMem (show x ∉ {x | R < ‖f x‖} from hrx), add_zero]
          using le_of_not_gt hrx
    · simp only [indicator_of_notMem hx, zero_add]
      exact Set.indicator_nonneg (fun x _ ↦ norm_nonneg _) x
  have hbound := integral_mono (hi.indicator hs)
    (((integrable_const R).indicator hs).add (hi.indicator ht)) hpoint
  simp only [Pi.add_apply] at hbound
  rw [integral_add ((integrable_const R).indicator hs) (hi.indicator ht),
    integral_indicator hs, integral_indicator hs, integral_indicator ht,
    setIntegral_const, smul_eq_mul, mul_comm (μ.real s) R] at hbound
  exact hbound

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

namespace OriginalSeedConditionalMoments

variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The actual inverse matrix coefficient is Bochner integrable for every legal pairing. -/
theorem integrable_inverse_pair_coefficient
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {root : ℝ} (hroot : root ∈ Ioo D.lo D.hi)
    {π : Measure (ℝ × ℝ)} (hπ : Vlasov.IsCoupling π μ ν)
    (hforward : ∀ᵐ p ∂π, p.1 < p.2) :
    Integrable (fun p ↦ (originalSeedPairCoefficient S w p)⁻¹) π := by
  have hm := (D.paired_inverse_coefficient_moments hF hw hroot hπ hforward
    (r := 1) zero_lt_one (by norm_num)).1
  have hi : Integrable (fun p ↦ ‖(originalSeedPairCoefficient S w p)⁻¹‖) π := by
    simpa only [Real.rpow_one] using hm
  exact (integrable_norm_iff (measurable_real_matrix_inverse.comp
    (measurable_originalSeedPairCoefficient S hF hw)).aestronglyMeasurable).mp hi

/-- Small removed mass gives small inverse-coefficient integral uniformly over every legal
pairing, including a removed event chosen after the pairing is known. -/
theorem uniform_integral_inverse_coefficient_on_small_sets
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {root : ℝ} (hroot : root ∈ Ioo D.lo D.hi)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ π : Measure (ℝ × ℝ), Vlasov.IsCoupling π μ ν →
      (∀ᵐ p ∂π, p.1 < p.2) → ∀ s : Set (ℝ × ℝ), MeasurableSet s → π.real s ≤ δ →
      (∫ p in s, ‖(originalSeedPairCoefficient S w p)⁻¹‖ ∂π) < ε := by
  obtain ⟨R, hR, htail⟩ := D.exists_uniform_inverse_coefficient_cutoff hF hw hroot
    (r := 3 / 2) (by norm_num) (by norm_num) (half_pos hε)
  refine ⟨ε / (2 * R), by positivity, fun π hπ hforward s hs hmass ↦ ?_⟩
  have : IsProbabilityMeasure (π.map Prod.fst) := hπ.1.symm ▸ D.support.source.probability
  have : IsProbabilityMeasure π := Measure.isProbabilityMeasure_of_map Prod.fst
  have hmeas := measurable_real_matrix_inverse.comp
    (measurable_originalSeedPairCoefficient S hF hw)
  have hi := D.integrable_inverse_pair_coefficient hF hw hroot hπ hforward
  have hb := setIntegral_norm_le_cutoff hmeas hi.norm hR.le hs
  simp only [Function.comp_def] at hb
  have hm : R * π.real s ≤ ε / 2 := by
    calc
      R * π.real s ≤ R * (ε / (2 * R)) := mul_le_mul_of_nonneg_left hmass hR.le
      _ = ε / 2 := by field_simp
  linarith [htail π hπ hforward]

/-- Retaining any measurable core of sufficiently large mass preserves the integral of
the actual inverse coefficient, uniformly across legal original conditional pairings. -/
theorem uniform_inverse_coefficient_core_error
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {root : ℝ} (hroot : root ∈ Ioo D.lo D.hi)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ π : Measure (ℝ × ℝ), Vlasov.IsCoupling π μ ν →
      (∀ᵐ p ∂π, p.1 < p.2) → ∀ s : Set (ℝ × ℝ), MeasurableSet s → π.real sᶜ ≤ δ →
      ‖(∫ p, (originalSeedPairCoefficient S w p)⁻¹ ∂π) -
        ∫ p in s, (originalSeedPairCoefficient S w p)⁻¹ ∂π‖ < ε := by
  obtain ⟨δ, hδ, hsmall⟩ := D.uniform_integral_inverse_coefficient_on_small_sets hF hw hroot hε
  refine ⟨δ, hδ, fun π hπ hforward s hs hmass ↦ ?_⟩
  have hi := D.integrable_inverse_pair_coefficient hF hw hroot hπ hforward
  have heq : (∫ p, (originalSeedPairCoefficient S w p)⁻¹ ∂π) -
      ∫ p in s, (originalSeedPairCoefficient S w p)⁻¹ ∂π =
      ∫ p in sᶜ, (originalSeedPairCoefficient S w p)⁻¹ ∂π := by
    rw [← integral_add_compl hs hi, add_sub_cancel_left]
  rw [heq]
  exact (norm_integral_le_integral_norm _).trans_lt (hsmall π hπ hforward sᶜ hs.compl hmass)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
