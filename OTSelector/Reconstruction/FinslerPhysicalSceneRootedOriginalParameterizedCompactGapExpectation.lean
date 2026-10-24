import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalParameterizedCompactExpectation
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalFullAgreement
/-!
# Vanishing original joint compact readout gap

Actual joint macro and edge compact readouts pass through the same prescribed
weak laws. Original opposite tilted full-plan agreement makes their expected
absolute readout difference vanish after the inner sample and outer tilt limits.
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

local instance originalParameterizedCompactGapExpectationStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalParameterizedCompactGapExpectationConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance originalParameterizedCompactGapExpectationConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalParameterizedCompactGapExpectationConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalParameterizedCompactGapExpectationPlanPolish {ι : Type*} [Fintype ι] :
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

/-- Actual original opposite tilted plans have vanishing expected absolute compact
readout gap after the prescribed inner sample and outer tilt limits. -/
theorem original_full_parameterized_compact_gap_expectation_limits_zero_of_face
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
    (Gjoint : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × Edge, ℝ)) :
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
    let readoutGap : MacroScene → ℝ := fun s ↦
      |physicalSceneFullParameterizedCompactReadout base Gjoint true s -
        physicalSceneFullParameterizedCompactReadout base Gjoint false s|
    ∀ (Qfull : ℕ → ProbabilityMeasure MacroScene) (Rfull : ProbabilityMeasure MacroScene)
      (φ : ℕ → ℕ → ℕ), (∀ ℓ, StrictMono (φ ℓ)) →
      ∀ ψ : ℕ → ℕ, StrictMono ψ →
      (∀ ℓ, Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Qfull ℓ))) →
      Tendsto (fun ℓ ↦ Qfull (ψ ℓ)) atTop (𝓝 Rfull) →
      (∀ ℓ, Integrable readoutGap (Qfull ℓ : Measure MacroScene) ∧
        (∀ᶠ n in atTop, Integrable readoutGap (laws ℓ (φ ℓ n) : Measure MacroScene)) ∧
        Tendsto (fun n ↦ ∫ s, readoutGap s ∂(laws ℓ (φ ℓ n) : Measure MacroScene)) atTop
          (𝓝 (∫ s, readoutGap s ∂(Qfull ℓ : Measure MacroScene)))) ∧
      Integrable readoutGap (Rfull : Measure MacroScene) ∧
      Tendsto (fun ℓ ↦ ∫ s, readoutGap s ∂(Qfull (ψ ℓ) : Measure MacroScene))
        atTop (𝓝 0) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  classical
  intro H laws readoutGap Qfull Rfull φ hφ ψ hψ hinner houter
  have hfp (ℓ n : ℕ) :
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ w.2 (ap ℓ n w) := (hp ℓ n).mono fun _ hw ↦ hw.1
  have hfm (ℓ n : ℕ) :
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ w.2 (am ℓ n w) := (hm ℓ n).mono fun _ hw ↦ hw.1
  have hexpectation := original_full_parameterized_compact_readout_expectation_limits_of_face j base
    hF hcomplete hu ha hinj horder hκ hbalance hcore hrecovery hface
    hAsupport hBsupport hAB hμA hνB hμreg hνreg nearRadius hnearRadius
    scale hscalePos hscale hnormalization ap am hpm hmm hfp hfm
    rootDomain hrootDomain Energy hEnergy hEp hEm rootCarrier hrootCarrier hrootIn
    Gjoint Qfull Rfull φ hφ ψ hψ hinner houter
  have hfull := ae_original_full_plans_eq_of_face j base
    hF hcomplete hu ha hinj horder hdim m hμchart hνchart nearRadius
    scale hscalePos hscale hnormalization probe hprobe G hprobeBound t ht0 ht0lim
    ap am hpm hmm hp hm rootDomain hrootDomain hμlaw hνlaw
    hAsupport hBsupport hAB hμreg hνreg hκ hbalance hcore hrecovery hface
    hμA hνB hnearRadius Energy hEnergy hEp hEm rootCarrier hrootCarrier hrootIn
    Qfull Rfull φ hφ ψ hψ hinner houter
  have hzero : (∫ s, readoutGap s ∂(Rfull : Measure MacroScene)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hfull] with s hs
    change |LocalFiniteMeasure.testIntegral s.2.1.1 (parameterizedCompactSlice Gjoint s.1) -
      LocalFiniteMeasure.testIntegral s.2.1.2 (parameterizedCompactSlice Gjoint s.1)| = 0
    simp only [LocalFiniteMeasure.testIntegral, hs, sub_self, abs_zero]
  have hlimit : Tendsto (fun ℓ ↦ ∫ s, readoutGap s
      ∂(Qfull (ψ ℓ) : Measure MacroScene)) atTop
      (𝓝 (∫ s, readoutGap s ∂(Rfull : Measure MacroScene))) := hexpectation.2.2.2
  rw [hzero] at hlimit
  exact ⟨hexpectation.2.1, hexpectation.2.2.1, hlimit⟩

end OTSelector.Reconstruction
