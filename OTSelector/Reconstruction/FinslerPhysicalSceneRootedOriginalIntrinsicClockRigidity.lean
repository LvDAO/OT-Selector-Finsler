import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalIntrinsicClockCoefficient
import OTSelector.Geometry.FinslerQuadraticCostDifferenceAmbient
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

/-- The original coefficient cost in the actual original seed basis. It uses
the literal original inverse length compliance, with its actual clock pair. -/
def physicalSceneOriginalIntrinsicClockCost
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (x y : (Fin (finrank ℝ S.covector.ker) → ℝ) × ℝ) : ℝ :=
  matrixQuadratic (originalSeedPairCoefficient S w (x.2, y.2)) (y.1 - x.1)

/-- The actual open clock domain is the whole calibrated interior of this same
original complete curve, restricted to strictly forward edges. -/
def physicalSceneOriginalIntrinsicClockDomain
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker) :
    Set (((Fin (finrank ℝ S.covector.ker) → ℝ) × ℝ) ×
      ((Fin (finrank ℝ S.covector.ker) → ℝ) × ℝ)) :=
  {p | p.1.2 - S.level ∈ interior (S.calibrationTimes w) ∧
    p.2.2 - S.level ∈ interior (S.calibrationTimes w) ∧ p.1.2 < p.2.2}

/-- Openness uses only the actual interior clock set. -/
theorem isOpen_physicalSceneOriginalIntrinsicClockDomain :
    IsOpen (physicalSceneOriginalIntrinsicClockDomain S w) := by
  let X := (Fin (finrank ℝ S.covector.ker) → ℝ) × ℝ
  have h₀ : Continuous (fun p : X × X ↦ p.1.2 - S.level) :=
    (continuous_snd.comp continuous_fst).sub continuous_const
  have h₁ : Continuous (fun p : X × X ↦ p.2.2 - S.level) :=
    (continuous_snd.comp continuous_snd).sub continuous_const
  exact (isOpen_interior.preimage h₀).inter
    ((isOpen_interior.preimage h₁).inter
      (isOpen_lt (continuous_snd.comp continuous_fst) (continuous_snd.comp continuous_snd)))

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
include D
local notation "Point" => ((Fin (finrank ℝ S.covector.ker) → ℝ) × ℝ)

/-- Original clock geometry and ambient source-volume AC imply equality of
the unchanged ambient plans once they are carried by the actual intrinsic
clock domain and their full average has the produced AE two-cycle inequality.
No single auxiliary coefficient window has to carry both complete plans. -/
theorem ambient_plans_eq_of_calibrationInterior_ae_twoCycle
    (hF : F.IsSmoothStronglyConvex)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hw : w ∈ S.labels)
    {ρ : Measure Point}
    (hρ : ρ ≪ (volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod
      (volume : Measure ℝ))
    {T : Set Point} (hT : T.Countable) (hTinj : InjOn Prod.fst T)
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
  apply ambient_quadratic_plans_eq_of_countable_spatial_cloud volume volume hρ
    (fun s t ↦ originalSeedPairCoefficient S w (s, t))
    (fun t ↦ (measurable_originalSeedPairCoefficient S hF hw).comp
      (measurable_id.prodMk measurable_const))
    hT hTinj θ hθ π₀ π₁ hsource₀ hsource₁ htarget₀ htarget₁ legal hD.measurableSet
    ?_ hlegal₀ hlegal₁ hsupport
  intro p hp
  exact (D.pair_compliance_posDef_calibrationInterior hF hu hw hp.1 hp.2.1 hp.2.2).2

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
