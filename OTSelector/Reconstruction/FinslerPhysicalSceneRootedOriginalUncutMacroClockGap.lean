import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroClockProbeGapLaw
import OTSelector.Topology.CurriedAccuracyApproximation
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalFixedSeedProbeCutoffAccuracy
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalParameterizedCompactGapExpectation

/-!
# The same original uncut macro-clock readout gap vanishes

Each accuracy chooses one actual compact target cutoff. The same original full
weak scene laws give its compact expected absolute gap limit. Original global
fixed-seed cutoff errors then vanish in sample size, with accuracy last and no
diagonal replacement of the prescribed sample-before-tilt limits.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

local instance originalUncutMacroClockGapStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalUncutMacroClockGapConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance originalUncutMacroClockGapConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalUncutMacroClockGapConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalUncutMacroClockGapPlanPolish {ι : Type*} [Fintype ι] :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}


variable (j : ℕ)
set_option quotPrecheck false
local notation "Edge" => (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))
variable (base : (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "Point" => ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "PairScene" => CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "MacroScene" => (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- The uncut actual original macro-clock probe has vanishing expected absolute
opposite-tilt gap on the sample-before-tilt curried filter. -/
theorem tendsto_original_full_macro_clock_probe_abs_gap_curry_zero_of_face
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hdim : 2 ≤ Module.finrank ℝ E) (m : Measure E) [m.IsAddHaarMeasure]
    (hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A B : Set M}
    (nearRadius : ℝ)
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n) (hscale : Tendsto scale atTop atTop)
    (hnormalization : ∀ n, scale n ^ finrank ℝ (P j).seed.covector.ker = (n : ℝ) + 1)
    (probe : M → M → ℝ) (hprobe : Measurable (Function.uncurry probe))
    (G : ℝ≥0) (hprobeBound : ∀ x y, |probe x y| ≤ G)
    (t : ℕ → ℝ) (ht0 : ∀ ℓ, 0 ≤ t ℓ) (ht0lim : Tendsto t atTop (𝓝 0))
    (ap am : ∀ (_ℓ n : ℕ),
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hpm : ∀ ℓ n j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ ap ℓ n z.1 z.2 j))
    (hmm : ∀ ℓ n j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ am ℓ n z.1 z.2 j))
    (hp : ∀ ℓ n,
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsOptimalSemidiscreteAllocation μ w.2 (fun x j ↦
          scale n ^ 2 * ((F.lengthEDist x (w.1 j)).toReal - u (w.1 j) + u x) +
            t ℓ * probe x (w.1 j)) (ap ℓ n w))
    (hm : ∀ ℓ n,
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsOptimalSemidiscreteAllocation μ w.2 (fun x j ↦
          scale n ^ 2 * ((F.lengthEDist x (w.1 j)).toReal - u (w.1 j) + u x) +
            (-t ℓ) * probe x (w.1 j)) (am ℓ n w))
    (rootDomain : ℕ → Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
    (hrootDomain : ∀ n, volume (rootDomain n) = ENNReal.ofReal ((n : ℝ) + 1))
    (hμlaw : PopulationConditionalWindowLaw P a κ (μ.map a) μ ρ₀ v)
    (hνlaw : PopulationConditionalWindowLaw P a κ (μ.map a) ν ρ₁ v)
    (hAsupport : IsCompact A) (hBsupport : IsCompact B) (hAB : Disjoint A B)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hκ : ∀ j, (κ j).IsAddHaarMeasure) (hbalance : μ.map a = ν.map a)
    (hcore : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    (hμA : μ Aᶜ = 0) (hνB : ν Bᶜ = 0)
    (hnearRadius : 0 < nearRadius)
    (Energy : ℝ≥0∞) (hEnergy : Energy ≠ ⊤)
    (hEp : ∀ ℓ n,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (scale n ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ (ap ℓ n) (fun w ↦ w.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ Energy)
    (hEm : ∀ ℓ n,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (scale n ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ (am ℓ n) (fun w ↦ w.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ Energy)
    (rootCarrier : Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
    (hrootCarrier : IsCompact rootCarrier)
    (hrootIn : ∀ n z, z ∈ rootDomain n → physicalSceneMacroscopicRoot (scale n) z ∈ rootCarrier)
    (η : C_c(Fin (finrank ℝ (P j).seed.covector.ker) → ℝ, ℝ))
    (g : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ)) :
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let laws : ℕ → ℕ → ProbabilityMeasure MacroScene := fun ℓ n ↦
      actualAllocationRootedMacroscopicSceneLaw base
        ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ
        (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n)
        (fun w ↦ w.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst)
        H (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j)
        (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n))
        (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale n))
        u (by
          let _inst : MetricSpace M := F.metricSpace
          exact hu.continuous.measurable) (scale n) (rootDomain n) (hrootDomain n)
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
    let Γp := fun ℓ n ↦ physicalSceneGlobalAllocationFamily μ (ap ℓ n) (fun w ↦ w.1)
    let Γm := fun ℓ n ↦ physicalSceneGlobalAllocationFamily μ (am ℓ n) (fun w ↦ w.1)
    let gap := fun ℓ n ↦ ∫⁻ w, ∫⁻ z, ENNReal.ofReal
      |(∫ e, η e.1.1 * g (physicalSceneMacroscopicRoot (scale n) z, (e.1.2, e.2.2))
          ∂physicalSceneRootedPlan ((Γp ℓ n w).restrict (H ×ˢ univ))
            (coord n) u ((n : ℝ) + 1) z) -
        ∫ e, η e.1.1 * g (physicalSceneMacroscopicRoot (scale n) z, (e.1.2, e.2.2))
          ∂physicalSceneRootedPlan ((Γm ℓ n w).restrict (H ×ˢ univ))
            (coord n) u ((n : ℝ) + 1) z|
      ∂cavityRootMeasure volume (rootDomain n) ((n : ℝ) + 1)
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))
    ∀ (Qfull : ℕ → ProbabilityMeasure MacroScene) (Rfull : ProbabilityMeasure MacroScene)
      (φ : ℕ → ℕ → ℕ), (∀ ℓ, StrictMono (φ ℓ)) →
      ∀ ψ : ℕ → ℕ, StrictMono ψ →
      (∀ ℓ, Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Qfull ℓ))) →
      Tendsto (fun ℓ ↦ Qfull (ψ ℓ)) atTop (𝓝 Rfull) →
      Tendsto (fun p : ℕ × ℕ ↦ gap (ψ p.1) (φ (ψ p.1) p.2))
        ((atTop : Filter ℕ).curry atTop) (𝓝 0) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  classical
  intro H laws coord Γp Γm gap Qfull Rfull φ hφ ψ hψ hinner houter
  have hfp (ℓ n : ℕ) :
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ w.2 (ap ℓ n w) := (hp ℓ n).mono fun _ hw ↦ hw.1
  have hfm (ℓ n : ℕ) :
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ w.2 (am ℓ n w) := (hm ℓ n).mono fun _ hw ↦ hw.1
  apply tendsto_curry_zero_of_vanishing_accuracy_approximants
    (fun ℓ n ↦ gap (ψ ℓ) (φ (ψ ℓ) n))
  intro accuracy haccuracy
  obtain ⟨χ, hχ, sample, hsample, hcutoff⟩ :=
    exists_original_fixed_seed_macro_clock_probe_cutoff_accuracy_of_face j
      hF hcomplete hu ha hinj horder hκ hbalance hcore hrecovery hface
      hAsupport hBsupport hAB hμA hνB hμreg hνreg
      scale hscalePos hscale ap am hpm hmm hfp hfm Energy hEnergy hEp hEm
      η g (accuracy / 2) (by positivity)
  let Gjoint := physicalSceneMacroClockCompactKernel η g χ
  let Hgap : MacroScene → ℝ := fun s ↦
    |physicalSceneFullParameterizedCompactReadout base Gjoint true s -
      physicalSceneFullParameterizedCompactReadout base Gjoint false s|
  let Bgap : ℕ → ℕ → ℝ≥0∞ := fun ℓ n ↦ ∫⁻ s, ENNReal.ofReal (Hgap s)
    ∂(laws (ψ ℓ) (φ (ψ ℓ) n) : Measure MacroScene)
  have hcompact := original_full_parameterized_compact_gap_expectation_limits_zero_of_face j base
    hF hcomplete hu ha hinj horder hdim m hμchart hνchart nearRadius
    scale hscalePos hscale hnormalization probe hprobe G hprobeBound t ht0 ht0lim
    ap am hpm hmm hp hm rootDomain hrootDomain hμlaw hνlaw
    hAsupport hBsupport hAB hμreg hνreg hκ hbalance hcore hrecovery hface
    hμA hνB hnearRadius Energy hEnergy hEp hEm rootCarrier hrootCarrier hrootIn
    Gjoint Qfull Rfull φ hφ ψ hψ hinner houter
  have hBgap : Tendsto (fun p : ℕ × ℕ ↦ Bgap p.1 p.2)
      ((atTop : Filter ℕ).curry atTop) (𝓝 0) :=
    tendsto_lintegral_ofReal_curry_zero_of_iterated_readout_limits
      (fun ℓ n ↦ (laws ℓ n : Measure MacroScene))
      (fun ℓ ↦ (Qfull ℓ : Measure MacroScene)) φ ψ Hgap
      (fun _ ↦ abs_nonneg _) (fun ℓ ↦ ⟨(hcompact.1 ℓ).2.1, (hcompact.1 ℓ).2.2⟩)
      hcompact.2.2
  refine ⟨Bgap, hBgap, (fun ℓ n ↦ sample (φ (ψ ℓ) n) + sample (φ (ψ ℓ) n)), ?_, ?_⟩
  · intro ℓ
    simpa only [add_zero, Function.comp_def] using
      (hsample.comp (hφ (ψ ℓ)).tendsto_atTop).add
        (hsample.comp (hφ (ψ ℓ)).tendsto_atTop)
  · intro ℓ
    apply Eventually.of_forall
    intro n
    let N := φ (ψ ℓ) n
    let Penv := (Measure.pi (fun _ : Fin (N + 1) ↦ ν)).prod (dirichletOne N)
    have hH : MeasurableSet H := measurableSet_physicalSceneOriginalSeedSource
      hF hcomplete hu ha hinj j
    have hcoord : Measurable (coord N) := measurable_physicalSceneOriginalSeedScaledPosition
      hF hcomplete hu ha hinj j (scale N)
    have hcmp := lintegral_actual_full_macro_clock_probe_gap_le_compact_gap_add_errors
      base Penv μ (ap (ψ ℓ) N) (am (ψ ℓ) N) (hpm (ψ ℓ) N) (hmm (ψ ℓ) N)
      (fun w ↦ w.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst)
      H hH (coord N) hcoord u hu.continuous.measurable (scale N)
      (rootDomain N) (hrootDomain N) η g χ hχ
    have hcp := hcutoff rootDomain hrootDomain (ψ ℓ) N true
      (physicalSceneMacroscopicRoot (scale N))
    have hcm := hcutoff rootDomain hrootDomain (ψ ℓ) N false
      (physicalSceneMacroscopicRoot (scale N))
    have hhalf : ENNReal.ofReal (accuracy / 2) + ENNReal.ofReal (accuracy / 2) =
        ENNReal.ofReal accuracy := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    apply hcmp.trans
    apply (add_le_add (add_le_add le_rfl hcp) hcm).trans_eq
    change Bgap ℓ n + (ENNReal.ofReal (accuracy / 2) + sample N) +
        (ENNReal.ofReal (accuracy / 2) + sample N) =
      Bgap ℓ n + ENNReal.ofReal accuracy + (sample N + sample N)
    calc
      _ = Bgap ℓ n + (ENNReal.ofReal (accuracy / 2) + ENNReal.ofReal (accuracy / 2)) +
          (sample N + sample N) := by ac_rfl
      _ = _ := by rw [hhalf]

end OTSelector.Reconstruction
