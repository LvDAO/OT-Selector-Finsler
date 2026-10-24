import OTSelector.Reconstruction.OriginalIIDRootedCountingLimit
import OTSelector.Reconstruction.OriginalIIDMaskedBipartiteMacroScene

/-! Integer edge multiplicities in the unchanged seed-masked joint experiment.
The input coordinates are retained while the same optimizer plan passes to its
actual joint weak limit. -/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability PointProcess
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
variable {M ι : Type*} [MeasurableSpace M] [Fintype ι]
variable (base : (ι → ℝ) × ℝ)
local instance iidMaskedCountingPointStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) :=
  inferInstance
local instance iidMaskedCountingPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance iidMaskedCountingConfigTopology : TopologicalSpace (LocalConfiguration base) :=
  LocalConfiguration.vagueTopology base
local instance iidMaskedCountingConfigBorel : BorelSpace (LocalConfiguration base) :=
  LocalConfiguration.vagueBorelSpace
local instance iidMaskedCountingConfigPolish : PolishSpace (LocalConfiguration base) :=
  LocalConfiguration.vaguePolishSpace
set_option quotPrecheck false
local notation "Macro" => (ι → ℝ) ×
  (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)
local instance iidMaskedCountingMacroPolish : PolishSpace (Macro × Macro) := inferInstance
local instance iidMaskedCountingMacroBorel : BorelSpace (Macro × Macro) := inferInstance

/-- The literal seed-masked input/optimizer experiment retains integer plan
atoms at the original sample-size prefactor. -/
theorem ae_isLegalCountingMeasure_originalIIDMaskedBipartiteMacroLaw
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι)
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (k : ℝ) (n : ℕ) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) :
    ∀ᵐ s ∂(originalIIDMaskedBipartiteMacroLaw base μ ν hq cost hcost k n H hH
      coord hcoord u hu : Measure (Macro × Macro)),
      IsLegalCountingMeasure 0 s.1.2.1.1 := by
  have hK : MeasurableSet {s : Macro × Macro | IsLegalCountingMeasure 0 s.1.2.1.1} :=
    ((isClosed_isLegalCountingMeasure
      (0 : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))).preimage
      continuous_fst.snd.fst.fst).measurableSet
  apply (ae_map_iff (measurable_originalIIDMaskedBipartiteMacroObservation base
    cost hcost k n H hH coord hcoord u hu
    (2 * haarRootRadius (Fintype.card ι) ((n : ℝ) + 1))).aemeasurable hK).mpr
  exact Eventually.of_forall fun w ↦
    (isLegalCountingMeasure_originalIIDBipartiteMacroObservation base
      cost k n H hH coord hcoord u hu
        (2 * haarRootRadius (Fintype.card ι) ((n : ℝ) + 1)) w).1

/-- Any actual joint weak limit keeps the same integer edge carrier together
with both original masked input colors and the original macro tag. -/
theorem ae_isLegalCountingMeasure_of_originalIIDMaskedBipartiteMacroLaw_tendsto
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (H : ℕ → Set M) (hH : ∀ n, MeasurableSet (H n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u) (m : ℕ → ℕ)
    (Q : ProbabilityMeasure (Macro × Macro))
    (hweak : Tendsto (fun n ↦ originalIIDMaskedBipartiteMacroLaw base μ ν hq
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) (H (m n)) (hH (m n))
      (coord (m n)) (hcoord (m n)) u hu) atTop (𝓝 Q)) :
    ∀ᵐ s ∂(Q : Measure (Macro × Macro)), IsLegalCountingMeasure 0 s.1.2.1.1 :=
  ae_isLegalCountingMeasure_of_continuous_readout_tendsto 0
    (fun s : Macro × Macro ↦ s.1.2.1.1) continuous_fst.snd.fst.fst _ Q hweak
    (fun n ↦ ae_isLegalCountingMeasure_originalIIDMaskedBipartiteMacroLaw base μ ν hq
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) (H (m n)) (hH (m n))
      (coord (m n)) (hcoord (m n)) u hu)

end OTSelector.Reconstruction
