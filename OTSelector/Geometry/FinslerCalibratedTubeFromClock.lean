import OTSelector.Geometry.FinslerCalibratedTubeData
import OTSelector.Geometry.Finsler.CalibratedCompleteCylinder
import OTSelector.Geometry.Finsler.Geodesic.MetricMinimizerEnergy

/-!
# Calibrated tube data from the original potential clock

A complete central unit-speed curve with the original calibrated clock supplies
minimization and saturation on every inner interval. Its two-sided calibrated
interior also supplies differentiability of the original potential at the first
endpoint, completing the geometric tube data without additional assumptions.
-/

open Set Metric Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- The original calibrated clock on a larger interval constructs the actual
calibrated-tube data on an inner interval, retaining the supplied smooth tube. -/
def calibratedTubeOfClock (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {Y : OpenPartialHomeomorph (ℝ × W) M} {Λ : W → ℝ → M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target)
    (heq : (Y : ℝ × W → M) = fun q ↦ Λ q.2 q.1)
    (hhalf : ∀ q ∈ Y.source,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2)
    (t₀ : ℝ)
    (hbound : ∀ y ∈ Y.target, ∀ z : TangentSpace 𝓘(ℝ, E) y,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 t₀) y z)
        (F.toFun ⟨y, z⟩ : ℝ))
    {a b : ℝ} (hab : a < b)
    (hstay : ∀ t ∈ Icc a b, (t, (0 : W)) ∈ Y.source)
    (hEL : F.IsEulerLagrangeOn (Λ 0) univ)
    (hunit : ∀ t : ℝ,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ 0) ⟨t, (1 : ℝ)⟩) = 1)
    {δ c : ℝ} (hδ : 0 < δ) (ha : a ∈ Ioo (-δ) δ) (hb : b ∈ Ioo (-δ) δ)
    (hclock : ∀ t ∈ Icc (-δ) δ, u (Λ 0 t) = c + t) :
    F.CalibratedTube Λ a b u := by
  letI : MetricSpace M := F.metricSpace
  have hca := hclock a ⟨ha.1.le, ha.2.le⟩
  have hcb := hclock b ⟨hb.1.le, hb.2.le⟩
  have hinner := hF.calibrated_window_of_complete_unit_endpoints hu hEL hunit hca hcb
  have houter := hF.calibrated_window_of_complete_unit_endpoints hu hEL hunit
    (hclock (-δ) ⟨le_rfl, neg_le_self hδ.le⟩)
    (hclock δ ⟨neg_le_self hδ.le, le_rfl⟩)
  have hdist : dist (Λ 0 a) (Λ 0 b) = b - a := by
    simpa only [Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hab.le), neg_sub] using
      hinner.2.1.dist_eq ⟨a, left_mem_Icc.mpr hab.le⟩ ⟨b, right_mem_Icc.mpr hab.le⟩
  refine
    { toOpenPartialHomeomorph := Y
      smooth := hY
      smooth_symm := hi
      coe_eq := heq
      energy_eq := hhalf
      timeOrigin := t₀
      covector_le := hbound
      ordered := hab
      stay := hstay
      minimizing := hF.lengthEDist_eq_pathELength_of_isometric_interval hab.le hinner.2.1
      saturation := ?_
      differentiable := hF.mdifferentiableAt_of_mem_calibratedInterior
        hcomplete hu (houter.2.2 a ha) }
  rw [hca, hcb, hdist]
  ring

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
