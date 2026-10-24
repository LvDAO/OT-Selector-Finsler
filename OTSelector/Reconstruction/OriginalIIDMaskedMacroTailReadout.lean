import OTSelector.Reconstruction.OriginalIIDMaskedBipartiteMacroScene
import OTSelector.MeasureTheory.LocalFiniteMeasureKernel
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# Actual masked macro-scene plan readouts

Pushforward and product lower-integral inequalities bound actual macro-law
partner-window masses by their original nested iid-array and Haar-root masses.
The projected plan is finite almost surely, as it is the same observed finite
original optimizer.
-/
open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {M ι : Type*} [MeasurableSpace M] [Fintype ι]
variable (base : (ι → ℝ) × ℝ)
local instance maskedMacroTailReadoutStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance maskedMacroTailReadoutConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance maskedMacroTailReadoutConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance maskedMacroTailReadoutConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance maskedMacroTailReadoutPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
set_option quotPrecheck false
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)
local notation "Macro" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local instance maskedMacroTailReadoutPairMeasurable : MeasurableSpace PairScene := inferInstance
local instance maskedMacroTailReadoutMacroMeasurable : MeasurableSpace Macro := inferInstance
local instance maskedMacroTailReadoutJointMeasurable : MeasurableSpace (Macro × Macro) := inferInstance

/-- The actual common finite optimizer retained in the first macro record. -/
def originalIIDMaskedMacroPlan (s : Macro × Macro) :
    LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) := s.1.2.1.1

/-- Projecting the unchanged optimizer is continuous in the actual macro carrier. -/
theorem continuous_originalIIDMaskedMacroPlan :
    Continuous (originalIIDMaskedMacroPlan base) := continuous_fst.snd.fst.fst

/-- The actual plan projection is measurable for the vague Borel carrier. -/
theorem measurable_originalIIDMaskedMacroPlan :
    Measurable (originalIIDMaskedMacroPlan base) := measurable_fst.snd.fst.fst

/-- The projected locally finite measure is literally the rooted original
source-restricted optimizer, with its unchanged full-array matching. -/
@[simp]
theorem coe_originalIIDMaskedMacroPlan_observation
    (cost : M → M → ℝ) (k : ℝ) (n : ℕ) (H : Set M)
    (coord : M → (ι → ℝ)) (u : M → ℝ) (scale : ℝ)
    (w : ((Fin (n + 1) → M) × (Fin (n + 1) → M)) × (ι → ℝ)) :
    (originalIIDMaskedMacroPlan base
      (originalIIDMaskedBipartiteMacroObservation base cost k n H coord u scale w) :
        Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) =
      physicalSceneRootedPlan
        ((originalIIDOptimalPhysicalPlan cost k w.1).restrict (H ×ˢ univ))
        coord u ((n : ℝ) + 1) w.2 := rfl

/-- Every nonnegative set-mass readout of the actual projected optimizer is
bounded by the same original nested iid-array and Haar-root readout. No
measurability assumption on the queried set is needed for this upper bound. -/
theorem lintegral_originalIIDMaskedMacroPlan_measure_le
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι)
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (k : ℝ) (n : ℕ) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u)
    (E : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :
    (∫⁻ s : Macro × Macro, (originalIIDMaskedMacroPlan base s :
      Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) E
      ∂(originalIIDMaskedBipartiteMacroLaw base μ ν hq cost hcost k n H hH
        coord hcoord u hu : Measure (Macro × Macro))) ≤
      ∫⁻ w, ∫⁻ z, physicalSceneRootedPlan
        ((originalIIDOptimalPhysicalPlan cost k w).restrict (H ×ˢ univ))
        coord u ((n : ℝ) + 1) z E
        ∂cavityRootMeasure volume
          (haarRootCube ι (haarRootRadius (Fintype.card ι) ((n : ℝ) + 1)))
          ((n : ℝ) + 1)
        ∂(Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n + 1) ↦ ν)) := by
  let P := (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
    (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
  let R := haarRootRadius (Fintype.card ι) ((n : ℝ) + 1)
  let ρ := cavityRootMeasure volume (haarRootCube ι R) ((n : ℝ) + 1)
  let obs := originalIIDMaskedBipartiteMacroObservation base cost k n H coord u (2 * R)
  let read := fun s : Macro × Macro ↦ (originalIIDMaskedMacroPlan base s :
    Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) E
  change (∫⁻ s, read s ∂(P.prod ρ).map obs) ≤ _
  exact (lintegral_map_le read obs).trans (lintegral_prod_le (fun w ↦ read (obs w)))

/-- The optimizer projection is finite almost surely under the unchanged
masked macro law, inherited from every actual finite original optimizer. -/
theorem ae_originalIIDMaskedMacroPlan_isFiniteMeasure
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι)
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (k : ℝ) (n : ℕ) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) :
    ∀ᵐ s ∂(originalIIDMaskedBipartiteMacroLaw base μ ν hq cost hcost k n H hH
      coord hcoord u hu : Measure (Macro × Macro)),
      IsFiniteMeasure (originalIIDMaskedMacroPlan base s :
        Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := by
  let P := (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
    (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
  let R := haarRootRadius (Fintype.card ι) ((n : ℝ) + 1)
  let ρ := cavityRootMeasure volume (haarRootCube ι R) ((n : ℝ) + 1)
  let obs := originalIIDMaskedBipartiteMacroObservation base cost k n H coord u (2 * R)
  have hobs : Measurable obs :=
    measurable_originalIIDMaskedBipartiteMacroObservation base cost hcost k n H hH
      coord hcoord u hu (2 * R)
  have hset : MeasurableSet {s : Macro × Macro |
      IsFiniteMeasure (originalIIDMaskedMacroPlan base s :
        Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))} :=
    FiniteMeasure.measurableSet_isFiniteMeasure.preimage
      (measurable_localFiniteMeasure_coe.comp (measurable_originalIIDMaskedMacroPlan base))
  change ∀ᵐ s ∂(P.prod ρ).map obs,
    IsFiniteMeasure (originalIIDMaskedMacroPlan base s :
      Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
  apply (ae_map_iff hobs.aemeasurable hset).mpr
  exact ae_of_all _ fun w ↦ isFiniteMeasure_physicalSceneRootedPlan
    ((originalIIDOptimalPhysicalPlan cost k w.1).restrict (H ×ˢ univ))
    coord u ((n : ℝ) + 1) w.2

end OTSelector.Reconstruction


