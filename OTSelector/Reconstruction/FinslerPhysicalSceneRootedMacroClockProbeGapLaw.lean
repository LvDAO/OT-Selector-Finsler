import OTSelector.Reconstruction.FinslerPhysicalSceneMacroClockProbeCutoffGapExpectation
import OTSelector.Reconstruction.FinslerPhysicalSceneMacroClockCompactKernel
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicWitness

/-!
# The original uncut probe gap uses the same full scene law

Cutting the two actual finite physical plans produces the literal joint compact
readout on their unchanged macro-tagged law. Only the two actual cutoff errors
remain in the original environment and normalized root expectation.
-/
open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω]
variable (base : (ι → ℝ) × ℝ)
local instance macroClockGapLawStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance macroClockGapLawConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance macroClockGapLawConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance macroClockGapLawConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance macroClockGapLawPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
local notation "V" => (ι → ℝ)
local notation "Point" => (V × ℝ)
local notation "Edge" => (Point × Point)
local notation "MacroScene" => V × (CavityLocalScene Point Point × LocalConfiguration base)

/-- The actual uncut original full probe gap is controlled by the compact gap
on the SAME original full law and the two original cutoff errors. -/
theorem lintegral_actual_full_macro_clock_probe_gap_le_compact_gap_add_errors {n : ℕ}
    (Penv : Measure Ω) [IsProbabilityMeasure Penv] (μ : Measure M) [IsFiniteMeasure μ]
    (ap am : Ω → M → Fin (n + 1) → ℝ)
    (hpm : ∀ k, Measurable (fun z : Ω × M ↦ ap z.1 z.2 k))
    (hmm : ∀ k, Measurable (fun z : Ω × M ↦ am z.1 z.2 k))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ k, Measurable (fun w ↦ Y w k))
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → V) (hcoord : Measurable coord) (u : M → ℝ) (hu : Measurable u)
    (scale : ℝ) (rootDomain : Set V)
    (hrootDomain : volume rootDomain = ENNReal.ofReal ((n : ℝ) + 1))
    (η : C_c(V, ℝ)) (g : C_c(V × (ℝ × ℝ), ℝ))
    (χ : C_c(Point, ℝ)) (hχ : ∀ y, χ y ∈ Icc 0 1) :
    let Γp := fun w ↦ (physicalSceneGlobalAllocationFamily μ ap Y w).restrict (H ×ˢ univ)
    let Γm := fun w ↦ (physicalSceneGlobalAllocationFamily μ am Y w).restrict (H ×ˢ univ)
    let πp := fun w z ↦ physicalSceneRootedPlan (Γp w) coord u ((n : ℝ) + 1) z
    let πm := fun w z ↦ physicalSceneRootedPlan (Γm w) coord u ((n : ℝ) + 1) z
    let f := fun (z : V) (e : Edge) ↦ η e.1.1 * g (physicalSceneMacroscopicRoot scale z, (e.1.2, e.2.2))
    let G := physicalSceneMacroClockCompactKernel η g χ
    (∫⁻ w, ∫⁻ z, ENNReal.ofReal |(∫ e, f z e ∂πp w z) - (∫ e, f z e ∂πm w z)|
      ∂cavityRootMeasure volume rootDomain ((n : ℝ) + 1) ∂Penv) ≤
      (∫⁻ s, ENNReal.ofReal |physicalSceneFullParameterizedCompactReadout base G true s -
        physicalSceneFullParameterizedCompactReadout base G false s|
        ∂(actualAllocationRootedMacroscopicSceneLaw base Penv μ ap am hpm hmm Y hY H hH
          coord hcoord u hu scale rootDomain hrootDomain : Measure MacroScene)) +
      (∫⁻ w, ∫⁻ z, ∫⁻ e, ENNReal.ofReal |f z e - f z e * χ e.2|
        ∂πp w z ∂cavityRootMeasure volume rootDomain ((n : ℝ) + 1) ∂Penv) +
      (∫⁻ w, ∫⁻ z, ∫⁻ e, ENNReal.ofReal |f z e - f z e * χ e.2|
        ∂πm w z ∂cavityRootMeasure volume rootDomain ((n : ℝ) + 1) ∂Penv) := by
  intro Γp Γm πp πm f G
  have hN : 0 < (n : ℝ) + 1 := by positivity
  let rootMeasure := cavityRootMeasure volume rootDomain ((n : ℝ) + 1)
  have : IsProbabilityMeasure rootMeasure :=
    isProbabilityMeasure_cavityRootMeasure volume rootDomain ((n : ℝ) + 1) hN hrootDomain
  have hΓp : Measurable Γp := measurable_physicalPlan_sourceRestriction _
    (measurable_physicalSceneGlobalAllocationFamily μ ap hpm Y hY) H hH
  have hΓm : Measurable Γm := measurable_physicalPlan_sourceRestriction _
    (measurable_physicalSceneGlobalAllocationFamily μ am hmm Y hY) H hH
  let πplus : Ω × V → Measure Edge := fun v ↦ πp v.1 v.2
  let πminus : Ω × V → Measure Edge := fun v ↦ πm v.1 v.2
  let tag : Ω × V → V := fun v ↦ physicalSceneMacroscopicRoot scale v.2
  let _instP (v : Ω × V) : IsFiniteMeasure (πplus v) :=
    isFiniteMeasure_physicalSceneRootedPlan (Γp v.1) coord u ((n : ℝ) + 1) v.2
  let _instM (v : Ω × V) : IsFiniteMeasure (πminus v) :=
    isFiniteMeasure_physicalSceneRootedPlan (Γm v.1) coord u ((n : ℝ) + 1) v.2
  have hp : Measurable πplus := measurable_joint_physicalSceneRootedPlan Γp hΓp coord hcoord u hu _
  have hm : Measurable πminus := measurable_joint_physicalSceneRootedPlan Γm hΓm coord hcoord u hu _
  have ht : Measurable tag := (continuous_physicalSceneMacroscopicRoot scale).measurable.comp measurable_snd
  have hcomparison := lintegral_ofReal_abs_macro_clock_probe_gap_le_cutoff_gap_add_errors
    (Penv.prod rootMeasure) πplus πminus hp hm tag ht η g χ hχ
  have hraw := measurable_ofReal_abs_macro_clock_probe_gap πplus πminus hp hm tag ht η g
  have hcut := measurable_ofReal_abs_macro_clock_probe_cutoff_gap πplus πminus hp hm tag ht η g χ hχ
  have hep := measurable_lintegral_macro_clock_probe_cutoff_error πplus hp tag ht η g χ
  have hem := measurable_lintegral_macro_clock_probe_cutoff_error πminus hm tag ht η g χ
  rw [lintegral_prod _ hraw.aemeasurable, lintegral_prod _ hcut.aemeasurable,
    lintegral_prod _ hep.aemeasurable, lintegral_prod _ hem.aemeasurable] at hcomparison
  let W : MacroScene → ℝ≥0∞ := fun s ↦ ENNReal.ofReal
    |physicalSceneFullParameterizedCompactReadout base G true s -
      physicalSceneFullParameterizedCompactReadout base G false s|
  have hW : Measurable W :=
    ((continuous_physicalSceneFullParameterizedCompactReadout base G true).sub
      (continuous_physicalSceneFullParameterizedCompactReadout base G false)).abs.measurable.ennreal_ofReal
  have hlaw : (∫⁻ s, W s ∂(actualAllocationRootedMacroscopicSceneLaw base Penv μ ap am
        hpm hmm Y hY H hH coord hcoord u hu scale rootDomain hrootDomain : Measure MacroScene)) =
      ∫⁻ w, ∫⁻ z, W (physicalSceneRootedMacroscopicObservation base Γp Γm coord u
        ((n : ℝ) + 1) scale Y (w, z)) ∂rootMeasure ∂Penv :=
    lintegral_actualAllocationRootedMacroscopicSceneLaw base Penv μ ap am hpm hmm
      Y hY H hH coord hcoord u hu scale rootDomain hrootDomain W hW
  have hobs (w : Ω) (z : V) :
      W (physicalSceneRootedMacroscopicObservation base Γp Γm coord u ((n : ℝ) + 1) scale Y (w, z)) =
        ENNReal.ofReal |(∫ e, f z e * χ e.2 ∂πp w z) -
          ∫ e, f z e * χ e.2 ∂πm w z| := by
    dsimp only [W, G]
    rw [physicalSceneFullParameterizedCompactReadout_macroClockCompactKernel_eq,
      physicalSceneFullParameterizedCompactReadout_macroClockCompactKernel_eq]
    rfl
  simp_rw [hobs] at hlaw
  rw [← hlaw] at hcomparison
  exact hcomparison

end OTSelector.Reconstruction
