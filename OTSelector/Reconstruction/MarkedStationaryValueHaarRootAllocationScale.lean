import OTSelector.Reconstruction.MarkedStationaryValueHaarRootAllocation
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootScale

/-! The original sample count chooses the actual macroscopic Haar cube and
physical root scale. All cube mass, positivity and divergence inputs of the
conditional stationarity producer are discharged from that count. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]
variable (base : (ι → ℝ) × ℝ)
local instance markedStationaryValueHaarRootAllocationScaleLocalInst1 : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance markedStationaryValueHaarRootAllocationScaleLocalInst2 : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance markedStationaryValueHaarRootAllocationScaleLocalInst3 : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance markedStationaryValueHaarRootAllocationScaleLocalInst4 : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance markedStationaryValueHaarRootAllocationScaleLocalInst5 : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueHaarRootAllocationScaleLocalInst6 : Nonempty
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := ⟨⟨0, inferInstance⟩⟩

/-- The actual original sample count supplies a Haar cube of exactly that
mass. A weak limit of the actual macro-rooted allocation experiment then has
stationary conditional physical scenes at almost every retained original root. -/
theorem ae_conditional_actualAllocationReroot_of_massCube_tendsto
    (hq : 0 < Fintype.card ι)
    {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (m : ℕ → ℕ) (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (hm : Tendsto (fun k ↦ (m k : ℝ) + 1) atTop atTop)
    (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : ∀ k, Ω k → M → Fin (m k + 1) → ℝ)
    (hplus : ∀ k j, Measurable (fun z : Ω k × M ↦ aplus k z.1 z.2 j))
    (hminus : ∀ k j, Measurable (fun z : Ω k × M ↦ aminus k z.1 z.2 j))
    (Y : ∀ k, Ω k → Fin (m k + 1) → M)
    (hY : ∀ k j, Measurable (fun w ↦ Y k w j))
    (H : ℕ → Set M) (hH : ∀ k, MeasurableSet (H k))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ k, Measurable (coord k))
    (u : M → ℝ) (hu : Measurable u)
    {ν : ProbabilityMeasure ((ι → ℝ) ×
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base))}
    (hlim : Tendsto (fun k ↦ actualAllocationRootedMacroscopicSceneLaw base (P k) μ
      (aplus k) (aminus k) (hplus k) (hminus k) (Y k) (hY k)
      (H k) (hH k) (coord k) (hcoord k) u hu
      (((m k : ℝ) + 1) ^ (1 / (Fintype.card ι : ℝ)))
      (haarRootCube ι (haarRootRadius (Fintype.card ι) ((m k : ℝ) + 1)))
      (volume_haarRootCube_radius ι hq (by positivity))) atTop (𝓝 ν)) :
    let νpair := ν.map (f := fun s ↦ (s.1, s.2.1))
      (measurable_fst.prodMk measurable_snd.fst).aemeasurable
    ∀ᵐ w ∂(νpair : Measure ((ι → ℝ) ×
        CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))).fst, ∀ v : ι → ℝ,
      MeasurePreserving (physicalSceneReroot v)
        ((νpair : Measure ((ι → ℝ) × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))).condKernel w)
        ((νpair : Measure ((ι → ℝ) × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))).condKernel w) := by
  have hpos (k : ℕ) : (0 : ℝ) < (m k : ℝ) + 1 := by positivity
  exact ae_conditional_actualAllocationReroot_of_macroRooted_tendsto base m P μ
    aplus aminus hplus hminus Y hY H hH coord hcoord u hu
    (fun k ↦ haarRootRadius (Fintype.card ι) ((m k : ℝ) + 1))
    (fun k ↦ ((m k : ℝ) + 1) ^ (1 / (Fintype.card ι : ℝ)))
    (fun k ↦ haarRootRadius_pos _ (hpos k)) (tendsto_haarRootRadius _ hq hm)
    ((tendsto_rpow_atTop (one_div_pos.mpr (by exact_mod_cast hq))).comp hm)
    (fun k ↦ volume_haarRootCube_radius ι hq (hpos k)) hlim

end OTSelector.Reconstruction
