import OTSelector.Probability.CavitySemidiscreteLocalPlan
import OTSelector.MeasureTheory.PairWeakCycleSupport
import OTSelector.Probability.CavitySemidiscretePlanAverage
import OTSelector.Probability.CavitySemidiscreteSpatialWitnessLimit

/-!
# The common actual rooted two-plan scene

Both signs use the same original target cloud, masses and root. Almost sure
feasibility suffices for the measurable diffuse scene; its average is exactly the
rooted average allocation on the original good event.
-/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped BigOperators ENNReal Classical

noncomputable section
namespace OTSelector.Probability

variable {ι A B Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
  [MeasurableSpace A] [MeasurableSpace B]

omit [Fintype ι] in
/-- A finite feasible allocation remains finite under its actual spatial rooting. -/
theorem IsSemidiscreteAllocation.isFiniteMeasure_cavitySpatialRootedPlan {m : ℕ}
    {μ : Measure ((ι → ℝ) × A)} [IsFiniteMeasure μ]
    {p : Fin (m + 1) → ℝ} {a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a)
    (Y : Fin (m + 1) → ((ι → ℝ) × B)) (N : ℝ) (z : ι → ℝ) :
    IsFiniteMeasure (cavitySpatialRootedPlan μ a Y N z) := by
  have := ha.isFiniteMeasure_allocationMeasure
  constructor
  simp only [cavitySpatialRootedPlan, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

omit [Fintype ι] in
/-- Mass scaling and the common root preserve the actual averaging identity. -/
theorem cavitySpatialRootedPlan_average {m : ℕ}
    (μ : Measure ((ι → ℝ) × A)) (p : Fin (m + 1) → ℝ)
    (a b : ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (ha : IsSemidiscreteAllocation μ p a) (hb : IsSemidiscreteAllocation μ p b)
    (ham : ∀ j, Measurable (fun s ↦ a s j))
    (hbm : ∀ j, Measurable (fun s ↦ b s j))
    (Y : Fin (m + 1) → ((ι → ℝ) × B)) (N : ℝ) (z : ι → ℝ) :
    cavitySpatialRootedPlan μ (fun s j ↦ (a s j + b s j) / 2) Y N z =
      (2 : ℝ≥0∞)⁻¹ • (cavitySpatialRootedPlan μ a Y N z +
        cavitySpatialRootedPlan μ b Y N z) := by
  have hm : Measurable (Prod.map (cavitySpatialTranslate z)
      (fun j ↦ cavitySpatialTranslate z (Y j))) :=
    (show Measurable (cavitySpatialTranslate z : ((ι → ℝ) × A) → ((ι → ℝ) × A)) from
      measurable_cavitySpatialTranslate.comp
        (measurable_const.prodMk measurable_id)).prodMap (measurable_of_finite _)
  simp only [cavitySpatialRootedPlan, semidiscreteAllocationMeasure_average μ p a b ha hb ham hbm,
    Measure.map_smul, Measure.map_add _ _ hm, smul_add, smul_smul]
  rw [mul_comm (ENNReal.ofReal N) ((2 : ℝ≥0∞)⁻¹)]

variable [TopologicalSpace A] [BorelSpace A]
  [T2Space A] [LocallyCompactSpace A] [PseudoMetrizableSpace A]
  [SigmaCompactSpace A] [SecondCountableTopology A]
  [TopologicalSpace B] [BorelSpace B]
  [T2Space B] [LocallyCompactSpace B] [PseudoMetrizableSpace B]
  [SigmaCompactSpace B] [SecondCountableTopology B]

/-- The two actual plans, on the common environment and root, in the vague carrier. -/
def cavityRootedLocalScene {m : ℕ}
    (μ : Measure ((ι → ℝ) × A))
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B)) (N : ℝ) (v : Ω × (ι → ℝ)) :
    CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B) :=
  (finitePlanLocalVersion
    (fun v ↦ cavitySpatialRootedPlan μ (fun s ↦ aplus (v.1, s)) (Y v.1) N v.2) v,
   finitePlanLocalVersion
    (fun v ↦ cavitySpatialRootedPlan μ (fun s ↦ aminus (v.1, s)) (Y v.1) N v.2) v)

/-- The complete actual two-sign scene is jointly measurable without an all-environment
feasibility or optimality hypothesis. -/
theorem measurable_cavityRootedLocalScene {m : ℕ}
    (μ : Measure ((ι → ℝ) × A)) [SFinite μ]
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hplus : ∀ j, Measurable (fun v ↦ aplus v j))
    (hminus : ∀ j, Measurable (fun v ↦ aminus v j))
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j)) (N : ℝ) :
    Measurable (cavityRootedLocalScene μ aplus aminus Y N) :=
  (measurable_finitePlanLocalVersion _
    (measurable_joint_cavitySpatialRootedPlan μ aplus hplus Y hY N)).prodMk
    (measurable_finitePlanLocalVersion _
      (measurable_joint_cavitySpatialRootedPlan μ aminus hminus Y hY N))

omit [T2Space A] [LocallyCompactSpace A] [T2Space B] [LocallyCompactSpace B] in
/-- On the original feasible event, the actual scene average is exactly the full
rooted average allocation measure used in the phase estimate. -/
theorem cavityRootedLocalScene_average {m : ℕ}
    (μ : Measure ((ι → ℝ) × A)) [IsFiniteMeasure μ]
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hplusm : ∀ j, Measurable (fun v ↦ aplus v j))
    (hminusm : ∀ j, Measurable (fun v ↦ aminus v j))
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B)) (N : ℝ)
    (ω : Ω) (p : Fin (m + 1) → ℝ)
    (hplus : IsSemidiscreteAllocation μ p (fun s ↦ aplus (ω, s)))
    (hminus : IsSemidiscreteAllocation μ p (fun s ↦ aminus (ω, s))) (z : ι → ℝ) :
    (LocalFiniteMeasure.cavityAverage (cavityRootedLocalScene μ aplus aminus Y N (ω, z)) :
      Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) =
      cavitySpatialRootedPlan μ (fun s j ↦ (aplus (ω, s) j + aminus (ω, s) j) / 2)
        (Y ω) N z := by
  have := hplus.isFiniteMeasure_cavitySpatialRootedPlan (Y ω) N z
  have := hminus.isFiniteMeasure_cavitySpatialRootedPlan (Y ω) N z
  rw [LocalFiniteMeasure.coe_cavityAverage]
  simp only [cavityRootedLocalScene, coe_finitePlanLocalVersion,
    ite_eq_left (measure_lt_top (cavitySpatialRootedPlan μ (fun s ↦ aplus (ω, s)) (Y ω) N z) univ),
    ite_eq_left (measure_lt_top (cavitySpatialRootedPlan μ (fun s ↦ aminus (ω, s)) (Y ω) N z) univ)]
  exact (cavitySpatialRootedPlan_average μ p _ _ hplus hminus
    (fun j ↦ (hplusm j).comp (measurable_const.prodMk measurable_id))
    (fun j ↦ (hminusm j).comp (measurable_const.prodMk measurable_id)) (Y ω) N z).symm

/-- The original environment and independent uniform spatial root give the common
law of both actual plans. The target cloud and masses are shared, not resampled. -/
def cavityRootedLocalSceneLaw {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [SFinite μ]
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hplus : ∀ j, Measurable (fun v ↦ aplus v j))
    (hminus : ∀ j, Measurable (fun v ↦ aminus v j))
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j))
    (N : ℝ) (hN : 0 < N) (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal N) :
    ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B)) := by
  have := isProbabilityMeasure_cavityRootMeasure volume D N hN hD
  exact ⟨(P.prod (cavityRootMeasure volume D N)).map
    (cavityRootedLocalScene μ aplus aminus Y N),
    Measure.isProbabilityMeasure_map
      (measurable_cavityRootedLocalScene μ aplus aminus hplus hminus Y hY N).aemeasurable⟩

end OTSelector.Probability
