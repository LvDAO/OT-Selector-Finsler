import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalIntrinsicClockRigidity
import OTSelector.Geometry.FinslerQuadraticCostDifferenceAmbientDistinct
import OTSelector.Reconstruction.FinslerOriginalClockCoefficientInjectivity
import OTSelector.Transport.CyclicMonotonicity.MeasureSupport

/-!
# Original coefficient geometry throughout its calibrated clock interior

The same original phase jet and physical Jacobian are already defined at every
interior calibrated time. Their actual regularity therefore applies to any
compact clock window inside that interior, independently of the auxiliary
conditional support window used to construct a finite population core.
-/

open Set Function Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
include D
local notation "Point" => ((Fin (finrank ℝ S.covector.ker) → ℝ) × ℝ)

/-- Original clock geometry and ambient source-volume AC imply equality of
the unchanged ambient plans once they are carried by the actual intrinsic
clock domain and their full average has the produced AE two-cycle inequality.
No single auxiliary coefficient window has to carry both complete plans.
Distinct target clocks distinguish original inverse-compliance matrices, so the
occupied spatial projection need not be injective. -/
theorem ambient_plans_eq_of_calibrationInterior_ae_twoCycle_countable_targets
    (hF : F.IsSmoothStronglyConvex)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hw : w ∈ S.labels) (hdim : 0 < finrank ℝ S.covector.ker)
    {ρ : Measure Point}
    (hρ : ρ ≪ (volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod
      (volume : Measure ℝ))
    {T : Set Point} (hT : T.Countable)
    (θ : Measure Point) (hθ : ∀ᵐ y ∂θ, y ∈ T)
    (π₀ π₁ : Measure (Point × Point)) [SFinite π₀] [SFinite π₁]
    (hsource₀ : π₀.map Prod.fst = ρ) (hsource₁ : π₁.map Prod.fst = ρ)
    (htarget₀ : π₀.map Prod.snd = θ) (htarget₁ : π₁.map Prod.snd = θ)
    (hlegal₀ : ∀ᵐ p ∂π₀, p ∈ physicalSceneOriginalIntrinsicClockDomain S w)
    (hlegal₁ : ∀ᵐ p ∂π₁, p ∈ physicalSceneOriginalIntrinsicClockDomain S w)
    (hcycle : ∀ᵐ p ∂(((2 : ℝ≥0∞)⁻¹ • (π₀ + π₁)).prod
        ((2 : ℝ≥0∞)⁻¹ • (π₀ + π₁))),
      p.1.1.2 < p.1.2.2 → p.2.1.2 < p.2.2.2 →
      p.1.1.2 < p.2.2.2 → p.2.1.2 < p.1.2.2 →
      physicalSceneOriginalIntrinsicClockCost S w p.1.1 p.1.2 +
          physicalSceneOriginalIntrinsicClockCost S w p.2.1 p.2.2 ≤
        physicalSceneOriginalIntrinsicClockCost S w p.1.1 p.2.2 +
          physicalSceneOriginalIntrinsicClockCost S w p.2.1 p.1.2) : π₀ = π₁ := by
  let c := physicalSceneOriginalIntrinsicClockCost S w
  let legal := physicalSceneOriginalIntrinsicClockDomain S w
  have hD : IsOpen legal := isOpen_physicalSceneOriginalIntrinsicClockDomain
  have hc : ContinuousOn (Function.uncurry c) legal := by
    exact D.continuousOn_quadratic_cost_calibrationInterior hF hu hw
  have hsupport := isTwoCycleMonotoneOn_support_of_ae
    ((2 : ℝ≥0∞)⁻¹ • (π₀ + π₁)) c hD hc (by
      filter_upwards [hcycle] with p hp h₀ h₁ h₂ h₃
      exact hp h₀.2.2 h₁.2.2 h₂.2.2 h₃.2.2)
  apply ambient_quadratic_plans_eq_of_countable_distinct_rows volume volume hρ
    (fun s t ↦ originalSeedPairCoefficient S w (s, t))
    (fun t ↦ (measurable_originalSeedPairCoefficient S hF hw).comp
      (measurable_id.prodMk measurable_const))
    hT θ hθ π₀ π₁ hsource₀ hsource₁ htarget₀ htarget₁ legal hD.measurableSet
    ?_ ?_ hlegal₀ hlegal₁ hsupport
  · intro p hp
    exact (D.pair_compliance_posDef_calibrationInterior hF hu hw hp.1 hp.2.1 hp.2.2).2
  · intro y _ z _ hyz x hx
    by_cases hsp : y.1 = z.1
    · right
      apply D.pair_coefficient_right_injective_calibrationInterior hF hu hw hdim
        hx.1.1 hx.1.2.1 hx.2.2.1 hx.1.2.2 hx.2.2.2
      intro hc
      exact hyz (Prod.ext hsp hc)
    · exact Or.inl hsp

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
