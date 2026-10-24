import OTSelector.Reconstruction.MarkedStationaryValueHaarRootConditionalPhysical
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMacroscopic

/-!
# Original allocation macro-root limits are conditionally stationary

The integer target carrier is forgotten only by its canonical projection. The
original global allocation plans, their original source restriction, clocks and
macroscopic root are retained. The exact original joint law supplies every
finite-root/cocycle input of conditional stationarity.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]
variable (base : (ι → ℝ) × ℝ)
local instance markedStationaryValueHaarRootAllocationLocalInst1 : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance markedStationaryValueHaarRootAllocationLocalInst2 : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance markedStationaryValueHaarRootAllocationLocalInst3 : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance markedStationaryValueHaarRootAllocationLocalInst4 : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance markedStationaryValueHaarRootAllocationLocalInst5 : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

local instance markedStationaryValueHaarRootAllocationLocalInst6 : Nonempty
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := ⟨⟨0, inferInstance⟩⟩

/-- Actual macro-tagged global allocation weak limits have conditionally
stationary original physical plan pairs on one common full-measure root set. -/
theorem ae_conditional_actualAllocationReroot_of_macroRooted_tendsto
    {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (m : ℕ → ℕ) (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : ∀ k, Ω k → M → Fin (m k + 1) → ℝ)
    (hplus : ∀ k j, Measurable (fun z : Ω k × M ↦ aplus k z.1 z.2 j))
    (hminus : ∀ k j, Measurable (fun z : Ω k × M ↦ aminus k z.1 z.2 j))
    (Y : ∀ k, Ω k → Fin (m k + 1) → M)
    (hY : ∀ k j, Measurable (fun w ↦ Y k w j))
    (H : ℕ → Set M) (hH : ∀ k, MeasurableSet (H k))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ k, Measurable (coord k))
    (u : M → ℝ) (hu : Measurable u) (R scale : ℕ → ℝ)
    (hR : ∀ k, 0 < R k) (hlarge : Tendsto R atTop atTop)
    (hscale : Tendsto scale atTop atTop)
    (hD : ∀ k, volume (haarRootCube ι (R k)) = ENNReal.ofReal ((m k : ℝ) + 1))
    {ν : ProbabilityMeasure ((ι → ℝ) ×
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base))}
    (hlim : Tendsto (fun k ↦ actualAllocationRootedMacroscopicSceneLaw base (P k) μ
      (aplus k) (aminus k) (hplus k) (hminus k) (Y k) (hY k)
      (H k) (hH k) (coord k) (hcoord k) u hu (scale k) (haarRootCube ι (R k)) (hD k))
        atTop (𝓝 ν)) :
    let νpair := ν.map (f := fun s ↦ (s.1, s.2.1))
      (measurable_fst.prodMk measurable_snd.fst).aemeasurable
    ∀ᵐ w ∂(νpair : Measure ((ι → ℝ) × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))).fst, ∀ v : ι → ℝ,
      MeasurePreserving (physicalSceneReroot v)
        ((νpair : Measure ((ι → ℝ) × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))).condKernel w) ((νpair : Measure ((ι → ℝ) × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))).condKernel w) := by
  let νpair := ν.map (f := fun s ↦ (s.1, s.2.1))
    (measurable_fst.prodMk measurable_snd.fst).aemeasurable
  let Γplus (k : ℕ) (w : Ω k) :=
    (physicalSceneGlobalAllocationFamily μ (aplus k) (Y k) w).restrict (H k ×ˢ univ)
  let Γminus (k : ℕ) (w : Ω k) :=
    (physicalSceneGlobalAllocationFamily μ (aminus k) (Y k) w).restrict (H k ×ˢ univ)
  have hΓplus (k) : Measurable (Γplus k) :=
    measurable_physicalPlan_sourceRestriction _
      (measurable_physicalSceneGlobalAllocationFamily μ (aplus k) (hplus k) (Y k) (hY k))
        (H k) (hH k)
  have hΓminus (k) : Measurable (Γminus k) :=
    measurable_physicalPlan_sourceRestriction _
      (measurable_physicalSceneGlobalAllocationFamily μ (aminus k) (hminus k) (Y k) (hY k))
        (H k) (hH k)
  let μpair (k : ℕ) :=
    (actualAllocationRootedMacroscopicSceneLaw base (P k) μ (aplus k) (aminus k)
      (hplus k) (hminus k) (Y k) (hY k) (H k) (hH k) (coord k) (hcoord k)
      u hu (scale k) (haarRootCube ι (R k)) (hD k)).map
        (f := fun s ↦ (s.1, s.2.1)) (measurable_fst.prodMk measurable_snd.fst).aemeasurable
  have hweak : Tendsto μpair atTop (𝓝 νpair) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlim
      (continuous_fst.prodMk continuous_snd.fst)
  have hmass (k : ℕ) : (m k : ℝ) + 1 = (2 * R k) ^ Fintype.card ι := by
    have hpow : 0 ≤ (2 * R k) ^ Fintype.card ι := pow_nonneg (by linarith [hR k]) _
    have h := congrArg ENNReal.toReal (hD k)
    simpa only [volume_haarRootCube ι (hR k).le,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ (m k : ℝ) + 1), ENNReal.toReal_ofReal hpow] using h.symm
  have hlaw (k : ℕ) : (μpair k : Measure ((ι → ℝ) × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) = haarCubeAverageLaw (P k)
      (fun p ↦ ((fun i ↦ p.2 i / scale k), physicalSceneRootedLocalScene
        (Γplus k) (Γminus k) (coord k) u ((m k : ℝ) + 1) p)) (R k) := by
    rw [coe_map_actualAllocationRootedMacroscopicSceneLaw_pair base (P k) μ
      (aplus k) (aminus k) (hplus k) (hminus k) (Y k) (hY k)
      (H k) (hH k) (coord k) (hcoord k) u hu (scale k) (haarRootCube ι (R k)) (hD k)]
    change ((P k).prod (cavityRootMeasure volume (haarRootCube ι (R k)) ((m k : ℝ) + 1))).map _ =
      ((P k).prod (cavityRootMeasure volume (haarRootCube ι (R k))
        ((2 * R k) ^ Fintype.card ι))).map _
    rw [hmass k]
    rfl
  exact ae_conditional_physicalSceneReroot_of_macroRooted_tendsto P Γplus Γminus
    hΓplus hΓminus coord hcoord u hu (fun k ↦ (m k : ℝ) + 1) R scale
    hR hlarge hscale μpair hlaw hweak

end OTSelector.Reconstruction
