import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedLossLimit
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMaskedJoint
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicWitness
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalIIDMaskedPacking
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedCoreWitnessLocalizedEvent

/-!
# Retained actual physical cycles have a pure original packing budget

All restrictions are observed jointly with the unchanged full original scene.
The actual retained plans pay only the opposite-tilt packing term. Population
loss belongs solely to the separately recorded discarded pair.
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
local instance retainedMaskedPackingStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance retainedMaskedPackingConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance retainedMaskedPackingConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance retainedMaskedPackingConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance retainedMaskedPackingPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace

local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- The capped rectangle witness of the actual retained pair, screened by the
original macro root, on its joint extension of the unchanged full scene. -/
def physicalSceneMaskedRetainedAverageWitness
    (Emacro : Set (ι → ℝ))
    (T₀ T₁ : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) (s : JointScene) : ℝ≥0∞ :=
  Emacro.indicator (fun _ ↦ min 1
    (min ((LocalFiniteMeasure.cavityAverage s.2.1 : Measure _) T₀)
      ((LocalFiniteMeasure.cavityAverage s.2.1 : Measure _) T₁))) s.1.1

/-- Open tests give a lower semicontinuous actual retained witness. -/
theorem lowerSemicontinuous_physicalSceneMaskedRetainedAverageWitness
    {Emacro : Set (ι → ℝ)} (hEmacro : IsOpen Emacro)
    {T₀ T₁ : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))}
    (hT₀ : IsOpen T₀) (hT₁ : IsOpen T₁) :
    LowerSemicontinuous (physicalSceneMaskedRetainedAverageWitness base Emacro T₀ T₁) :=
  lowerSemicontinuous_open_indicator_ennreal (hEmacro.preimage continuous_fst.fst)
    (lowerSemicontinuous_const.inf
      (((lowerSemicontinuous_cavityAverage_open hT₀).comp continuous_snd.fst).inf
        ((lowerSemicontinuous_cavityAverage_open hT₁).comp continuous_snd.fst)))

/-- Original global opposite optimality gives a pure packing budget for the
actual retained pair. The actual lost mass is recorded separately. -/
theorem lintegral_original_iid_finsler_masked_retained_macroscopic_witness_le
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
    (Egood : Set (M × M)) (hEgood : MeasurableSet Egood)
    (hinc : ∀ z ∈ physicalSceneMacroscopicRoot macroScale ⁻¹' Emacro,
      ∀ e ∈ Egood ∩ (H ×ˢ univ),
        physicalSceneRootedObservation coord pot z e ∈ (A₀ ×ˢ B₀) ∪ (A₁ ×ˢ B₁) →
          e ∈ Ks ×ˢ Kt)
    (D : Set (ι → ℝ))
    (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1)) :
    (∫⁻ s, ENNReal.ofReal ε * physicalSceneMaskedRetainedAverageWitness base Emacro
        (A₀ ×ˢ B₀) (A₁ ×ˢ B₁) s
      ∂(actualAllocationRootedMaskedMacroscopicSceneLaw base
        ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ ap am hpm hmm
        (fun w ↦ w.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
        H hH Egood hEgood coord hcoord pot (by
          let _inst : MetricSpace M := F.metricSpace
          exact hpot.continuous.measurable) macroScale D hD : Measure _)) ≤
      ENNReal.ofReal (t * G) * ENNReal.ofReal K ^ Fintype.card ι := by
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
  let Γp := physicalSceneGlobalAllocationFamily μ ap (fun w : Ω ↦ w.1)
  let Γm := physicalSceneGlobalAllocationFamily μ am (fun w : Ω ↦ w.1)
  have hΓp : Measurable Γp := measurable_physicalSceneGlobalAllocationFamily μ ap hpm _ hY
  have hΓm : Measurable Γm := measurable_physicalSceneGlobalAllocationFamily μ am hmm _ hY
  have hpack := lintegral_original_iid_finsler_rooted_average_screened_masked_rectangle_witness_le
    hF hcomplete hdim m μ ν hμchart hνchart hA hμA pot hpot scale hscale
    probe hprobe G hprobe_bound t ht ap am hpm hmm hp hm H Ks Kt hH hKs hKt
    coord hcoord A₀ A₁ B₀ B₁ hA₀.measurableSet hA₁.measurableSet hB₀.measurableSet
    hB₁.measurableSet hdisj K hK offset hbox Eroot hEroot ε hε hgap D ((n : ℝ) + 1) hN
  change (∫⁻ s, ENNReal.ofReal ε * physicalSceneMaskedRetainedAverageWitness base Emacro
    (A₀ ×ˢ B₀) (A₁ ×ˢ B₁) s ∂(physicalSceneRootedMaskedMacroscopicSceneLaw base Penv Γp Γm
      hΓp hΓm H hH Egood hEgood coord hcoord pot hpotm macroScale (fun w ↦ w.1) hY D hD :
      Measure JointScene)) ≤ _
  rw [lintegral_physicalSceneRootedMaskedMacroscopicSceneLaw base Penv Γp Γm hΓp hΓm
    H hH Egood hEgood coord hcoord pot hpotm macroScale (fun w ↦ w.1) hY D hD _
    ((lowerSemicontinuous_physicalSceneMaskedRetainedAverageWitness base hEmacro
      (hA₀.prod hB₀) (hA₁.prod hB₁)).measurable.const_mul _)]
  apply le_trans _ hpack
  apply lintegral_mono
  intro w
  apply lintegral_mono
  intro z
  by_cases hz : z ∈ Eroot
  · have hm : physicalSceneMacroscopicRoot macroScale z ∈ Emacro := hz
    simp only [physicalSceneMaskedRetainedAverageWitness,
      physicalSceneRootedMaskedMacroscopicObservation, physicalSceneRootedMacroscopicObservation,
      Set.indicator_of_mem hm, Set.indicator_of_mem hz, physicalSceneRootedLocalScene,
      LocalFiniteMeasure.coe_cavityAverage, coe_physicalSceneRootedLocalPlan]
    apply mul_le_mul_right
    apply min_le_min_left 1
    have hb (T : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) (hT : MeasurableSet T)
        (hsub : T ⊆ (A₀ ×ˢ B₀) ∪ (A₁ ×ˢ B₁)) :
        ((2 : ℝ≥0∞)⁻¹ •
          (physicalSceneRootedPlan (((Γp w).restrict Egood).restrict (H ×ˢ univ))
            coord pot ((n : ℝ) + 1) z +
           physicalSceneRootedPlan (((Γm w).restrict Egood).restrict (H ×ˢ univ))
            coord pot ((n : ℝ) + 1) z)) T ≤
        ((2 : ℝ≥0∞)⁻¹ •
          (physicalSceneRootedPlan ((Γp w).restrict ((H ∩ Ks) ×ˢ Kt))
            coord pot ((n : ℝ) + 1) z +
           physicalSceneRootedPlan ((Γm w).restrict ((H ∩ Ks) ×ˢ Kt))
            coord pot ((n : ℝ) + 1) z)) T := by
      have hr (Γ : Measure (M × M)) :
          (Γ.restrict Egood).restrict (H ×ˢ univ) =
            Γ.restrict (Egood ∩ (H ×ˢ univ)) := by
        rw [Measure.restrict_restrict (hH.prod MeasurableSet.univ), inter_comm]
      simp only [hr]
      change (2 : ℝ≥0∞)⁻¹ * (_ + _) ≤ (2 : ℝ≥0∞)⁻¹ * (_ + _)
      apply mul_le_mul_right
      apply add_le_add
      all_goals
        apply physicalSceneRootedPlan_restrict_le_of_observed_event_inclusion _ coord hcoord
          pot hpotm ((n : ℝ) + 1) z _ _ T hT
        intro e he ht
        have hf := hinc z hz e he (hsub ht)
        exact ⟨⟨he.2.1, hf.1⟩, hf.2⟩
    exact min_le_min (hb _ (hA₀.measurableSet.prod hB₀.measurableSet) subset_union_left)
      (hb _ (hA₁.measurableSet.prod hB₁.measurableSet) subset_union_right)
  · have hm : physicalSceneMacroscopicRoot macroScale z ∉ Emacro := hz
    simp only [physicalSceneMaskedRetainedAverageWitness,
      physicalSceneRootedMaskedMacroscopicObservation, physicalSceneRootedMacroscopicObservation,
      Set.indicator_of_notMem hm, Set.indicator_of_notMem hz, mul_zero, le_refl]

end OTSelector.Reconstruction
