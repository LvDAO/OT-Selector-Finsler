import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMacroscopic
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedAverageScreenedPacking

/-!
# Actual macro-tagged average cycle witnesses

Open macro windows and open pair rectangles define lower semicontinuous
witnesses of the true arithmetic mean of the two actual plans. Their law
readout is exactly the original environment and actual normalized root integral.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω]
variable (base : (ι → ℝ) × ℝ)
local instance macroscopicWitnessStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance macroscopicWitnessConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance macroscopicWitnessConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance macroscopicWitnessConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance macroscopicWitnessPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace

/-- A capped two-rectangle witness of the actual arithmetic mean, localized
only by the retained original macroscopic root. -/
def physicalSceneMacroscopicAverageWitness
    (E : Set (ι → ℝ)) (T₀ T₁ : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
    (s : (ι → ℝ) × (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)) : ℝ≥0∞ :=
  (Prod.fst ⁻¹' E).indicator (fun s ↦ min 1
    (min ((LocalFiniteMeasure.cavityAverage s.2.1 : Measure _) T₀)
      ((LocalFiniteMeasure.cavityAverage s.2.1 : Measure _) T₁))) s

/-- Open actual root windows and open observed rectangles give a lower
semicontinuous witness on the original jointly tagged vague scene carrier. -/
theorem lowerSemicontinuous_physicalSceneMacroscopicAverageWitness
    {E : Set (ι → ℝ)} (hE : IsOpen E)
    {T₀ T₁ : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))}
    (hT₀ : IsOpen T₀) (hT₁ : IsOpen T₁) :
    LowerSemicontinuous (physicalSceneMacroscopicAverageWitness base E T₀ T₁) :=
  lowerSemicontinuous_open_indicator_ennreal (hE.preimage continuous_fst)
    (lowerSemicontinuous_const.inf
      (((lowerSemicontinuous_cavityAverage_open hT₀).comp continuous_snd.fst).inf
        ((lowerSemicontinuous_cavityAverage_open hT₁).comp continuous_snd.fst)))

/-- Every measurable readout of the actual macro-tagged allocation law is its
unchanged original experiment and Haar root integral. -/
theorem lintegral_actualAllocationRootedMacroscopicSceneLaw {n : ℕ}
    (Penv : Measure Ω) [IsProbabilityMeasure Penv] (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : Ω → M → Fin (n + 1) → ℝ)
    (hplus : ∀ j, Measurable (fun z : Ω × M ↦ aplus z.1 z.2 j))
    (hminus : ∀ j, Measurable (fun z : Ω × M ↦ aminus z.1 z.2 j))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (scale : ℝ)
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1))
    (W : ((ι → ℝ) × (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)) → ℝ≥0∞)
    (hW : Measurable W) :
    (∫⁻ s, W s ∂(actualAllocationRootedMacroscopicSceneLaw base Penv μ aplus aminus
      hplus hminus Y hY H hH coord hcoord u hu scale D hD : Measure _)) =
      ∫⁻ w, ∫⁻ z, W (physicalSceneRootedMacroscopicObservation base
        (fun w ↦ (physicalSceneGlobalAllocationFamily μ aplus Y w).restrict (H ×ˢ univ))
        (fun w ↦ (physicalSceneGlobalAllocationFamily μ aminus Y w).restrict (H ×ˢ univ))
        coord u ((n : ℝ) + 1) scale Y (w, z))
        ∂cavityRootMeasure volume D ((n : ℝ) + 1) ∂Penv := by
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have := isProbabilityMeasure_cavityRootMeasure volume D ((n : ℝ) + 1) hN hD
  have hObs := measurable_physicalSceneRootedMacroscopicObservation base
    (fun w ↦ (physicalSceneGlobalAllocationFamily μ aplus Y w).restrict (H ×ˢ univ))
    (fun w ↦ (physicalSceneGlobalAllocationFamily μ aminus Y w).restrict (H ×ˢ univ))
    (measurable_physicalPlan_sourceRestriction _
      (measurable_physicalSceneGlobalAllocationFamily μ aplus hplus Y hY) H hH)
    (measurable_physicalPlan_sourceRestriction _
      (measurable_physicalSceneGlobalAllocationFamily μ aminus hminus Y hY) H hH)
    coord hcoord u hu ((n : ℝ) + 1) scale Y hY
  change (∫⁻ s, W s ∂(Penv.prod (cavityRootMeasure volume D ((n : ℝ) + 1))).map _) = _
  rw [lintegral_map hW hObs]
  exact lintegral_prod _ (hW.comp hObs).aemeasurable

/-- The actual tagged average witness is exactly the root-screened witness of
both same physical plans, with no imposed equality of their restricted columns. -/
theorem physicalSceneMacroscopicAverageWitness_observation {n : ℕ}
    (Γp Γm : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γp w)] [∀ w, IsFiniteMeasure (Γm w)]
    (coord : M → (ι → ℝ)) (u : M → ℝ) (N scale : ℝ)
    (Y : Ω → Fin (n + 1) → M) (E : Set (ι → ℝ))
    (T₀ T₁ : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) (w : Ω) (z : ι → ℝ) :
    physicalSceneMacroscopicAverageWitness base E T₀ T₁
      (physicalSceneRootedMacroscopicObservation base Γp Γm coord u N scale Y (w, z)) =
      (physicalSceneMacroscopicRoot scale ⁻¹' E).indicator
        (fun z ↦ min 1 (min
          (((2 : ℝ≥0∞)⁻¹ • (physicalSceneRootedPlan (Γp w) coord u N z +
            physicalSceneRootedPlan (Γm w) coord u N z)) T₀)
          (((2 : ℝ≥0∞)⁻¹ • (physicalSceneRootedPlan (Γp w) coord u N z +
            physicalSceneRootedPlan (Γm w) coord u N z)) T₁))) z := by
  unfold physicalSceneMacroscopicAverageWitness
  by_cases hz : physicalSceneMacroscopicRoot scale z ∈ E
  · rw [Set.indicator_of_mem (show physicalSceneRootedMacroscopicObservation base Γp Γm
      coord u N scale Y (w, z) ∈ Prod.fst ⁻¹' E from hz)]
    rw [Set.indicator_of_mem (show z ∈ physicalSceneMacroscopicRoot scale ⁻¹' E from hz)]
    rfl
  · rw [Set.indicator_of_notMem (show physicalSceneRootedMacroscopicObservation base Γp Γm
      coord u N scale Y (w, z) ∉ Prod.fst ⁻¹' E from hz)]
    rw [Set.indicator_of_notMem (show z ∉ physicalSceneMacroscopicRoot scale ⁻¹' E from hz)]

end OTSelector.Reconstruction
