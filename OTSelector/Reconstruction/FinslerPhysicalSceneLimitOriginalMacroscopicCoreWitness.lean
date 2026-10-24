import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicWitnessBudget
import OTSelector.Reconstruction.FinslerPhysicalSceneLimitIteratedWeightedCoreWitness

/-!
# Original physical packing survives both limits and auxiliary core exhaustion

The original iid target and Dirichlet allocation experiment is fixed throughout.
Retained endpoint cores supply physical cycle certificates only as estimates.
Their population losses are removed after the sample and tilt limits, even when
the positive physical cycle margin depends on the auxiliary core.
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
  {F : ContinuousFinslerNorm E M}
variable (base : (ι → ℝ) × ℝ)
local instance originalCoreWitnessStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalCoreWitnessConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance originalCoreWitnessConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalCoreWitnessConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalCoreWitnessPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
local notation "MacroScene" => (ι → ℝ) × (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)

/-- Original physical four-edge certificates on arbitrary-accuracy auxiliary cores
force the complete actual macro-tagged average witness to vanish in the SAME
outer scene law. The original two indices are retained until their stated limits. -/
theorem ae_original_iid_macroscopic_average_cycle_witness_zero_of_core_certificates
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
    (costScale : ℕ → ℝ) (hcostScale : ∀ n, costScale n ≠ 0)
    (probe : M → M → ℝ) (hprobe : Measurable (Function.uncurry probe))
    (G : ℝ≥0) (hprobe_bound : ∀ x y, |probe x y| ≤ G)
    (t : ℕ → ℝ) (ht : ∀ ℓ, 0 ≤ t ℓ) (ht0 : Tendsto t atTop (𝓝 0))
    (ap am : ∀ (_ℓ n : ℕ),
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hpm : ∀ ℓ n j, Measurable (fun v :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ ap ℓ n v.1 v.2 j))
    (hmm : ∀ ℓ n j, Measurable (fun v :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ am ℓ n v.1 v.2 j))
    (hp : ∀ ℓ n,
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsOptimalSemidiscreteAllocation μ w.2 (fun x j ↦
          costScale n * ((F.lengthEDist x (w.1 j)).toReal - pot (w.1 j) + pot x) +
            t ℓ * probe x (w.1 j)) (ap ℓ n w))
    (hm : ∀ ℓ n,
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsOptimalSemidiscreteAllocation μ w.2 (fun x j ↦
          costScale n * ((F.lengthEDist x (w.1 j)).toReal - pot (w.1 j) + pot x) +
            (-t ℓ) * probe x (w.1 j)) (am ℓ n w))
    (H : Set M) (hH : MeasurableSet H)
    (Ks Kt : ℕ → Set M) (hKs : ∀ r, MeasurableSet (Ks r))
    (hKt : ∀ r, MeasurableSet (Kt r))
    (hcoreLoss : Tendsto (fun r ↦ μ (Ks r)ᶜ + ν (Kt r)ᶜ) atTop (𝓝 0))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (A₀ A₁ B₀ B₁ : Set ((ι → ℝ) × ℝ))
    (hA₀ : IsOpen A₀) (hA₁ : IsOpen A₁) (hB₀ : IsOpen B₀) (hB₁ : IsOpen B₁)
    (hdisj : Disjoint A₀ A₁) (K : ℝ) (hK : 0 < K) (offset : ι → ℝ)
    (hbox : ∀ s ∈ A₀ ∪ A₁, s.1 - offset ∈ cavityGridPhaseCell ι K)
    (Emacro : Set (ι → ℝ)) (hEmacro : IsOpen Emacro) (macroScale : ℕ → ℝ)
    (U : Set (ι → ℝ)) (hU : MeasurableSet U) (hUf : volume U ≠ ⊤)
    (hA₀U : ∀ s ∈ A₀, s.1 ∈ U) (hA₁U : ∀ s ∈ A₁, s.1 ∈ U)
    (ε : ℕ → ℝ) (hε : ∀ r, 0 < ε r)
    (hgap : ∀ r : ℕ, ∀ᶠ (_ℓ : ℕ) in atTop, ∀ᶠ (n : ℕ) in atTop,
      ∀ᵐ Y ∂Measure.pi (fun _ : Fin (n + 1) ↦ ν),
        ∀ z ∈ physicalSceneMacroscopicRoot (macroScale n) ⁻¹' Emacro,
        ∀ x ∈ H ∩ Ks r, ∀ x' ∈ H ∩ Ks r,
          (coord n x - z, pot x) ∈ A₀ → (coord n x' - z, pot x') ∈ A₁ →
          ∀ j, Y j ∈ Kt r → (coord n (Y j) - z, pot (Y j)) ∈ B₀ →
          ∀ l, Y l ∈ Kt r → (coord n (Y l) - z, pot (Y l)) ∈ B₁ →
            ε r ≤ costScale n * ((F.lengthEDist x (Y j)).toReal - pot (Y j) + pot x) +
              costScale n * ((F.lengthEDist x' (Y l)).toReal - pot (Y l) + pot x') -
              costScale n * ((F.lengthEDist x (Y l)).toReal - pot (Y l) + pot x) -
              costScale n * ((F.lengthEDist x' (Y j)).toReal - pot (Y j) + pot x'))
    (D : ℕ → Set (ι → ℝ))
    (hD : ∀ n, volume (D n) = ENNReal.ofReal ((n : ℝ) + 1)) :
    let laws := fun ℓ n ↦ actualAllocationRootedMacroscopicSceneLaw base
      ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ
      (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n)
      (fun w ↦ w.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
      H hH (coord n) (hcoord n) pot (by
        let _inst : MetricSpace M := F.metricSpace
        exact hpot.continuous.measurable) (macroScale n) (D n) (hD n)
    ∀ (Q : ℕ → ProbabilityMeasure MacroScene) (R : ProbabilityMeasure MacroScene)
      (φ : ℕ → ℕ → ℕ), (∀ ℓ, Tendsto (φ ℓ) atTop atTop) →
      ∀ ψ : ℕ → ℕ, Tendsto ψ atTop atTop →
      (∀ ℓ, Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ))) →
      Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R) →
      ∀ᵐ s ∂(R : Measure MacroScene),
        physicalSceneMacroscopicAverageWitness base Emacro (A₀ ×ˢ B₀) (A₁ ×ˢ B₁) s = 0 := by
  let _inst : MetricSpace M := F.metricSpace
  dsimp only
  intro Q R φ hφ ψ hψ hinner houter
  have hpotm : Measurable pot := hpot.continuous.measurable
  let laws := fun ℓ n ↦ actualAllocationRootedMacroscopicSceneLaw base
    ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ
    (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n)
    (fun w ↦ w.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
    H hH (coord n) (hcoord n) pot hpotm (macroScale n) (D n) (hD n)
  have hacc : Tendsto (fun r ↦ volume U * (μ (Ks r)ᶜ + ν (Kt r)ᶜ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hcoreLoss (Or.inr hUf)
  apply ae_eq_zero_of_iterated_weak_lsc_weighted_core_accuracy_bounds
    laws Q R φ hφ ψ hψ hinner houter
    (physicalSceneMacroscopicAverageWitness base Emacro (A₀ ×ˢ B₀) (A₁ ×ˢ B₁))
    (lowerSemicontinuous_physicalSceneMacroscopicAverageWitness base hEmacro
      (hA₀.prod hB₀) (hA₁.prod hB₁))
    (fun r ↦ volume U * (μ (Ks r)ᶜ + ν (Kt r)ᶜ)) hacc
    (fun r ↦ ENNReal.ofReal (ε r)) (fun r ↦ (ENNReal.ofReal_pos.mpr (hε r)).ne')
    (fun _ ↦ ENNReal.ofReal_ne_top)
  intro r
  refine ⟨fun ℓ ↦ ENNReal.ofReal (t ℓ * G) * ENNReal.ofReal K ^ Fintype.card ι, ?_, ?_⟩
  · have htg : Tendsto (fun ℓ ↦ ENNReal.ofReal (t ℓ * G)) atTop (𝓝 0) := by
      simpa only [zero_mul, ENNReal.ofReal_zero, Function.comp_def] using
        (ENNReal.continuous_ofReal.tendsto (0 * (G : ℝ))).comp (ht0.mul_const (G : ℝ))
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const htg
      (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
  · filter_upwards [hgap r] with ℓ hℓ
    filter_upwards [hℓ] with n hn
    have hb := lintegral_original_iid_finsler_macroscopic_average_cycle_witness_le base
      hF hcomplete hdim m μ ν hμchart hνchart hA hμA pot hpot
      (costScale n) (hcostScale n) probe hprobe G hprobe_bound (t ℓ) (ht ℓ)
      (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n) (hp ℓ n) (hm ℓ n)
      H (Ks r) (Kt r) hH (hKs r) (hKt r) (coord n) (hcoord n)
      A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁ hdisj K hK offset hbox
      Emacro hEmacro (macroScale n) U hU hUf hA₀U hA₁U (ε r) (hε r).le hn (D n) (hD n)
    simpa only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] using hb

end OTSelector.Reconstruction
