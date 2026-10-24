import OTSelector.Reconstruction.FinslerFiniteCoefficientCores
import OTSelector.Reconstruction.PairedCoefficientTruncation
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Measurable original root moment envelopes

A fixed scalar reference inside the original support span gives a Borel primitive
of the original Hessian inverse. Its two conditional marginal moments bound every
legal paired law, without making a measurable choice of the comparison witness.
-/

open Set Function MeasureTheory ProbabilityTheory Matrix Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace Z]

/-- The original compliance primitive uses a fixed scalar reference, retaining the
actual seed level in both integration endpoints. -/
def populationSeedRootPrimitive (S : F.CalibratedLevelSeedPatch u) (a : M → Z)
    (root : ℝ) (q : Z × ℝ) :
    Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ :=
  ∫ t in (root - S.level)..(q.2 - S.level),
    populationSeedRootKernel S a (Module.finBasis ℝ S.covector.ker) (q.1, t)

/-- This finite real envelope is computed from the same two original conditional
laws; on an actual support window it bounds every legal inverse-coefficient moment. -/
def populationSeedRootMomentEnvelope (S : F.CalibratedLevelSeedPatch u) (a : M → Z)
    (μ ν : Kernel Z ℝ) (root r : ℝ) (z : Z) : ℝ :=
  (2 : ℝ) ^ max (r - 1) 0 *
    ((∫ x, ‖populationSeedRootPrimitive S a root (z, x)‖ ^ r ∂μ z) +
      ∫ x, ‖populationSeedRootPrimitive S a root (z, x)‖ ^ r ∂ν z)

variable [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z]
  (S : F.CalibratedLevelSeedPatch u) (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instMomentEnvelopeMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  {a : M → Z} (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- The fixed-reference primitive is jointly Borel in the actual root and scalar time. -/
theorem measurable_populationSeedRootPrimitive (root : ℝ) :
    Measurable (populationSeedRootPrimitive S a root) := by
  have hK := (measurable_populationSeedRootKernel S hF hcomplete hu ha hinj
    (Module.finBasis ℝ S.covector.ker)).stronglyMeasurable
  exact (stronglyMeasurable_intervalIntegral_comp hK measurable_fst measurable_const
    (measurable_snd.sub_const (S.level : ℝ))).measurable

/-- At an actual seed label the root primitive is exactly the literal original integral. -/
theorem populationSeedRootPrimitive_at_label (w : S.labels) (root x : ℝ) :
    populationSeedRootPrimitive S a root (a (S.curve w 0), x) =
      ∫ t in (root - S.level)..(x - S.level), originalSeedKernel S w t := by
  apply intervalIntegral.integral_congr
  intro t _
  exact populationSeedRootKernel_at_label S hF hcomplete hu ha hinj
    (Module.finBasis ℝ S.covector.ker) w t

/-- Kernel integration makes the original marginal moment envelope measurable,
without selecting conditional span endpoints or comparison families. -/
theorem measurable_populationSeedRootMomentEnvelope
    (μ ν : Kernel Z ℝ) [IsSFiniteKernel μ] [IsSFiniteKernel ν] (root r : ℝ) :
    Measurable (populationSeedRootMomentEnvelope S a μ ν root r) := by
  have hm := ((measurable_populationSeedRootPrimitive S hF hcomplete hu ha hinj root).norm.pow_const r).stronglyMeasurable
  exact ((hm.integral_kernel_prod_right' (κ := μ)).measurable.add
    (hm.integral_kernel_prod_right' (κ := ν)).measurable).const_mul _

/-- The measurable root envelope agrees with the earlier actual-seed moment bound. -/
theorem populationSeedRootMomentEnvelope_at_label
    (μ ν : Kernel Z ℝ) (w : S.labels) (root r : ℝ) :
    populationSeedRootMomentEnvelope S a μ ν root r (a (S.curve w 0)) =
      originalSeedMomentBound S w (μ (a (S.curve w 0))) (ν (a (S.curve w 0)))
        (root - S.level) r := by
  simp only [populationSeedRootMomentEnvelope, originalSeedMomentBound,
    populationSeedRootPrimitive_at_label S hF hcomplete hu ha hinj]

/-- All legal conditional pairings are controlled by the same explicit measurable
root envelope supplied by the two original marginal moments. -/
theorem HasOriginalSeedPairWindow.inverse_moments_le_rootEnvelope
    {μ ν : Kernel Z ℝ} {l h z} (hz : HasOriginalSeedPairWindow S a μ ν l h z)
    {π : Measure (ℝ × ℝ)} (hπ : Vlasov.IsCoupling π (μ z) (ν z))
    (hforward : ∀ᵐ p ∂π, p.1 < p.2) {r : ℝ} (hr0 : 0 < r) (hr2 : r < 2) :
    Integrable (fun p ↦ ‖(populationSeedRootCoefficient S a
      (Module.finBasis ℝ S.covector.ker) (z, p))⁻¹‖ ^ r) π ∧
      (∫ p, ‖(populationSeedRootCoefficient S a
        (Module.finBasis ℝ S.covector.ker) (z, p))⁻¹‖ ^ r ∂π) ≤
        populationSeedRootMomentEnvelope S a μ ν l r z := by
  obtain ⟨w, hwz, D, hl, _⟩ := hz
  have hcoeff (p : ℝ × ℝ) : populationSeedRootCoefficient S a
      (Module.finBasis ℝ S.covector.ker) (z, p) = originalSeedPairCoefficient S w p := by
    rw [← hwz]
    exact populationSeedRootCoefficient_at_label S hF hcomplete hu ha hinj
      (Module.finBasis ℝ S.covector.ker) w p.1 p.2
  have henv : populationSeedRootMomentEnvelope S a μ ν l r z =
      originalSeedMomentBound S w (μ z) (ν z) (l - S.level) r := by
    rw [← hwz, populationSeedRootMomentEnvelope_at_label S hF hcomplete hu ha hinj]
  simpa only [hcoeff, henv, originalSeedMomentBound] using
    D.paired_inverse_coefficient_moments hF w.property hl hπ hforward hr0 hr2

/-- Every actual original support window has the quantitative inverse-coefficient
tail bound given by the same measurable marginal envelope. -/
theorem HasOriginalSeedPairWindow.inverse_tail_le_rootEnvelope
    {μ ν : Kernel Z ℝ} {l h z} (hz : HasOriginalSeedPairWindow S a μ ν l h z)
    {π : Measure (ℝ × ℝ)} (hπ : Vlasov.IsCoupling π (μ z) (ν z))
    (hforward : ∀ᵐ p ∂π, p.1 < p.2) {r R : ℝ}
    (hr : 1 < r) (hr2 : r < 2) (hR : 0 < R) :
    IntegrableOn (fun p ↦ ‖(populationSeedRootCoefficient S a
      (Module.finBasis ℝ S.covector.ker) (z, p))⁻¹‖)
      {p | R < ‖(populationSeedRootCoefficient S a
        (Module.finBasis ℝ S.covector.ker) (z, p))⁻¹‖} π ∧
      (∫ p in {p | R < ‖(populationSeedRootCoefficient S a
        (Module.finBasis ℝ S.covector.ker) (z, p))⁻¹‖},
        ‖(populationSeedRootCoefficient S a
          (Module.finBasis ℝ S.covector.ker) (z, p))⁻¹‖ ∂π) ≤
        populationSeedRootMomentEnvelope S a μ ν l r z / R ^ (r - 1) := by
  have hm := hz.inverse_moments_le_rootEnvelope S hF hcomplete hu ha hinj hπ hforward
    (zero_lt_one.trans hr) hr2
  have hmeas := ContinuousFinslerNorm.measurable_real_matrix_inverse.comp
    ((measurable_populationSeedRootCoefficient S hF hcomplete hu ha hinj
      (Module.finBasis ℝ S.covector.ker)).comp ((measurable_const (a := z)).prodMk measurable_id))
  have ht := integral_norm_tail_le_rpow hmeas hr hR hm.1
  exact ⟨ht.1, ht.2.trans (div_le_div_of_nonneg_right hm.2
    (Real.rpow_nonneg hR.le _))⟩

/-- On an arbitrarily large compact subset, the actual marginal envelope has one
finite bound common to all roots and hence all their legal conditional pairings. -/
theorem exists_compact_rootMomentEnvelope_bound
    [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
    (μ ν : Kernel Z ℝ) [IsSFiniteKernel μ] [IsSFiniteKernel ν]
    (root r : ℝ) {lambda : Measure Z} {s : Set Z}
    (hs : MeasurableSet s) (hfinite : lambda s ≠ (∞ : ℝ≥0∞))
    {Good : Z → Prop} (hgood : ∀ᵐ z ∂lambda.restrict s, Good z)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ s, IsCompact K ∧ lambda (s \ K) < ε ∧
      ∃ L ≥ 0, ∀ z ∈ K, Good z ∧ populationSeedRootMomentEnvelope S a μ ν root r z ≤ L := by
  obtain ⟨K, hsub, hK, hsmall, hcont, hGood⟩ :=
    exists_lusin_compact_core_with_ae_property hs hfinite
      (measurable_populationSeedRootMomentEnvelope S hF hcomplete hu ha hinj μ ν root r)
      hgood hε
  obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨K, hsub, hK, hsmall, max L 0, le_max_right _ _, fun z hz ↦
    ⟨hGood z hz, ?_⟩⟩
  exact (le_abs_self _).trans ((hL z hz).trans (le_max_left _ _))

end OTSelector.Reconstruction
