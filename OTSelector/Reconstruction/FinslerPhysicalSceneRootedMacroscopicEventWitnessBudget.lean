import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicWitness
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalIIDMaskedPacking
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedCoreWitnessLocalizedEvent

/-!
# Actual physical cycle packing with a localized retained edge event

A physical four-edge certificate is used only on retained endpoint cores.
The same original iid-times-Dirichlet allocation law bounds the full
macro-localized arithmetic-average witness using actual exceptional edge mass.
The selected coefficient core need not have a small population complement.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
  OTSelector.Probability TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {ι E M : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M} {n : ℕ}
variable (base : (ι → ℝ) × ℝ)
local instance macroscopicEventBudgetStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance macroscopicEventBudgetConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance macroscopicEventBudgetConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance macroscopicEventBudgetConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance macroscopicEventBudgetPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace

/-- The unchanged original joint law satisfies a genuine full-scene cycle-witness
budget, derived from physical optimality, a core gap and actual exceptional mass. -/
theorem lintegral_original_iid_finsler_macroscopic_average_cycle_witness_le_event_mass
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 2 ≤ Module.finrank ℝ E) (m : Measure E) [m.IsAddHaarMeasure]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A : Set M} (hA : IsCompact A) (hμA : ∀ᵐ x ∂μ, x ∈ A)
    (pot : M → ℝ)
    (hpot : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 pot)
    (scale : ℝ) (hscale : scale ≠ 0)
    (probe : M → M → ℝ) (hprobe : Measurable (Function.uncurry probe))
    (G : ℝ≥0) (hprobe_bound : ∀ x y, |probe x y| ≤ G) (t : ℝ) (ht : 0 ≤ t)
    (ap am : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hpm : ∀ j, Measurable (fun v :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ ap v.1 v.2 j))
    (hmm : ∀ j, Measurable (fun v :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ am v.1 v.2 j))
    (hp : ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsOptimalSemidiscreteAllocation μ w.2 (fun x j ↦
        scale * ((F.lengthEDist x (w.1 j)).toReal - pot (w.1 j) + pot x) +
          t * probe x (w.1 j)) (ap w))
    (hm : ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsOptimalSemidiscreteAllocation μ w.2 (fun x j ↦
        scale * ((F.lengthEDist x (w.1 j)).toReal - pot (w.1 j) + pot x) +
          (-t) * probe x (w.1 j)) (am w))
    (H Ks Kt : Set M) (hH : MeasurableSet H)
    (hKs : MeasurableSet Ks) (hKt : MeasurableSet Kt)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (A₀ A₁ B₀ B₁ : Set ((ι → ℝ) × ℝ))
    (hA₀ : IsOpen A₀) (hA₁ : IsOpen A₁)
    (hB₀ : IsOpen B₀) (hB₁ : IsOpen B₁) (hdisj : Disjoint A₀ A₁)
    (K : ℝ) (hK : 0 < K) (offset : ι → ℝ)
    (hbox : ∀ s ∈ A₀ ∪ A₁, s.1 - offset ∈ cavityGridPhaseCell ι K)
    (Emacro : Set (ι → ℝ)) (hEmacro : IsOpen Emacro) (macroScale : ℝ)
    (U : Set (ι → ℝ)) (hU : MeasurableSet U) (hUf : volume U ≠ ⊤)
    (hA₀U : ∀ s ∈ A₀, s.1 ∈ U) (hA₁U : ∀ s ∈ A₁, s.1 ∈ U)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hgap : ∀ᵐ Y ∂Measure.pi (fun _ : Fin (n + 1) ↦ ν),
      ∀ z ∈ physicalSceneMacroscopicRoot macroScale ⁻¹' Emacro, ∀ x ∈ H ∩ Ks, ∀ x' ∈ H ∩ Ks,
        (coord x - z, pot x) ∈ A₀ → (coord x' - z, pot x') ∈ A₁ →
        ∀ j, Y j ∈ Kt → (coord (Y j) - z, pot (Y j)) ∈ B₀ →
        ∀ l, Y l ∈ Kt → (coord (Y l) - z, pot (Y l)) ∈ B₁ →
          ε ≤ scale * ((F.lengthEDist x (Y j)).toReal - pot (Y j) + pot x) +
            scale * ((F.lengthEDist x' (Y l)).toReal - pot (Y l) + pot x') -
            scale * ((F.lengthEDist x (Y l)).toReal - pot (Y l) + pot x) -
            scale * ((F.lengthEDist x' (Y j)).toReal - pot (Y j) + pot x'))
    (Egood : Set (M × M)) (hEgood : MeasurableSet Egood) (C : ℝ≥0∞)
    (hCp : (∫⁻ w, physicalSceneGlobalAllocationFamily μ ap (fun w ↦ w.1) w Egoodᶜ
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C)
    (hCm : (∫⁻ w, physicalSceneGlobalAllocationFamily μ am (fun w ↦ w.1) w Egoodᶜ
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C)
    (hinc : ∀ z ∈ physicalSceneMacroscopicRoot macroScale ⁻¹' Emacro,
      ∀ e ∈ Egood ∩ (H ×ˢ univ),
        physicalSceneRootedObservation coord pot z e ∈ (A₀ ×ˢ B₀) ∪ (A₁ ×ˢ B₁) →
          e ∈ Ks ×ˢ Kt)
    (D : Set (ι → ℝ))
    (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1)) :
    (∫⁻ s, ENNReal.ofReal ε * physicalSceneMacroscopicAverageWitness base Emacro
        (A₀ ×ˢ B₀) (A₁ ×ˢ B₁) s
      ∂(actualAllocationRootedMacroscopicSceneLaw base
        ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ ap am hpm hmm
        (fun w ↦ w.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
        H hH coord hcoord pot (by
          let _inst : MetricSpace M := F.metricSpace
          exact hpot.continuous.measurable) macroScale D hD : Measure _)) ≤
      ENNReal.ofReal (t * G) * ENNReal.ofReal K ^ Fintype.card ι +
        ENNReal.ofReal ε * (volume U * C) := by
  let _inst : MetricSpace M := F.metricSpace
  have hN : 0 < (n : ℝ) + 1 := by positivity
  let Ω := (Fin (n + 1) → M) × (Fin (n + 1) → ℝ)
  let Penv : Measure Ω := (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  let Eroot := physicalSceneMacroscopicRoot macroScale ⁻¹' Emacro
  have hEroot : MeasurableSet Eroot :=
    hEmacro.measurableSet.preimage (continuous_physicalSceneMacroscopicRoot macroScale).measurable
  have hY (j : Fin (n + 1)) : Measurable (fun w : Ω ↦ w.1 j) :=
    (measurable_pi_apply j).comp measurable_fst
  have hpotm : Measurable pot := hpot.continuous.measurable
  have hpack := lintegral_original_iid_finsler_rooted_average_screened_masked_rectangle_witness_le
    hF hcomplete hdim m μ ν hμchart hνchart hA hμA pot hpot scale hscale
    probe hprobe G hprobe_bound t ht ap am hpm hmm hp hm H Ks Kt hH hKs hKt
    coord hcoord A₀ A₁ B₀ B₁ hA₀.measurableSet hA₁.measurableSet hB₀.measurableSet
    hB₁.measurableSet hdisj K hK offset hbox Eroot hEroot ε hε hgap D ((n : ℝ) + 1) hN
  have hcore := lintegral_physicalSceneRooted_average_screened_witness_le_local_core_and_event_loss
    Penv (physicalSceneGlobalAllocationFamily μ ap (fun w ↦ w.1))
    (physicalSceneGlobalAllocationFamily μ am (fun w ↦ w.1))
    (measurable_physicalSceneGlobalAllocationFamily μ ap hpm _ hY)
    (measurable_physicalSceneGlobalAllocationFamily μ am hmm _ hY)
    Egood (Ks ×ˢ Kt) hEgood H hH coord hcoord pot hpotm ((n : ℝ) + 1) hN
    D U hD hU hUf C hCp hCm (A₀ ×ˢ B₀) (A₁ ×ˢ B₁)
    (hA₀.measurableSet.prod hB₀.measurableSet) (hA₁.measurableSet.prod hB₁.measurableSet)
    (fun e he ↦ hA₀U e.1 he.1) (fun e he ↦ hA₁U e.1 he.1) Eroot hinc
  have hmask : (Ks ×ˢ Kt) ∩ (H ×ˢ (univ : Set M)) = (H ∩ Ks) ×ˢ Kt := by
    ext e
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true]
    tauto
  simp only [hmask] at hcore
  dsimp only at hpack hcore
  simp_rw [Set.indicator_const_mul, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hpack
  have hweighted := mul_le_mul_right hcore (ENNReal.ofReal ε)
  rw [mul_add] at hweighted
  have hbudget := hweighted.trans (add_le_add_left hpack _)
  have hW := (lowerSemicontinuous_physicalSceneMacroscopicAverageWitness base hEmacro
    (hA₀.prod hB₀) (hA₁.prod hB₁)).measurable
  rw [lintegral_actualAllocationRootedMacroscopicSceneLaw base Penv μ ap am hpm hmm
    (fun w ↦ w.1) hY H hH coord hcoord pot hpotm macroScale D hD
    (fun s ↦ ENNReal.ofReal ε * physicalSceneMacroscopicAverageWitness base Emacro
      (A₀ ×ˢ B₀) (A₁ ×ˢ B₁) s) (hW.const_mul _)]
  simp_rw [physicalSceneMacroscopicAverageWitness_observation,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact hbudget

end OTSelector.Reconstruction
