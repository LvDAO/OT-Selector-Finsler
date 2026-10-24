import OTSelector.Reconstruction.MarkedStationaryValueLegalPressureRegularity
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.UniformConvergence

/-! The actual real-scale legal pressure converges uniformly on every compact
tilt set as soon as its actual pointwise limit has been produced. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Mathlib's compact equicontinuity theorem applies to the actual legal
pressure at all real scales, retaining the original forward-only bounds. -/
theorem tendstoUniformlyOn_legalMarkedScalePressure (q : ℕ)
    {sourceClock : A → ℝ} {targetClock : B → ℝ}
    (hs : Measurable sourceClock) (ht : Measurable targetClock)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b, sourceClock a < targetClock b → ∀ v,
      |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, sourceClock a < targetClock b → |probe a b| ≤ G)
    {p : ℝ → ℝ}
    (hpt : ∀ t, Tendsto (fun R : ℝ ↦
      legalMarkedScalePressure q sourceClock targetClock α β kin probe R t) atTop (𝓝 (p t)))
    {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun R : ℝ ↦
      legalMarkedScalePressure q sourceClock targetClock α β kin probe R) p atTop K := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : ℝ → K → ℝ := fun R t ↦
    legalMarkedScalePressure q sourceClock targetClock α β kin probe R t
  have hlip (R : ℝ) : LipschitzWith G.toNNReal (F R) := by
    apply LipschitzWith.of_dist_le_mul
    intro t u
    simpa only [F, Real.dist_eq, Subtype.dist_eq, Real.coe_toNNReal _ hG] using
      legalMarkedScalePressure_lipschitz q hs ht α β hC hG hk hkb hp hpb R t u
  have hEqui : Equicontinuous F :=
    (LipschitzWith.uniformEquicontinuous F G.toNNReal hlip).equicontinuous
  have hpoint : Tendsto F atTop (𝓝 (fun t : K ↦ p t)) :=
    tendsto_pi_nhds.mpr (fun t ↦ hpt t)
  have hunif := (hEqui.tendsto_uniformFun_iff_pi atTop (fun t : K ↦ p t)).mpr hpoint
  apply tendstoUniformlyOn_iff_restrict.mpr
  exact UniformFun.tendsto_iff_tendstoUniformly.mp hunif

end OTSelector.Reconstruction
