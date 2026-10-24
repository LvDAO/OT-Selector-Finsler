import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalFullClippingBudget
import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutClippingDifference
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalSourceReferenceExtension
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalClockScreenAccuracy
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedProjectedSourceAbsoluteContinuity
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMaskedDecomposition
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalMaskedLossLimit

/-!
# Full original tagged compact readout expectation limits

Original population cores provide clipping approximations on the unchanged full
scene laws. True global slack energy removes the finite-sample error for each
fixed core. Population loss then vanishes after the two prescribed weak limits,
producing integrability and expectation convergence without an extra assumption.
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

local instance originalFullCompactExpectationStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalFullCompactExpectationConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance originalFullCompactExpectationConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalFullCompactExpectationConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalFullCompactExpectationPlanPolish {ι : Type*} [Fintype ι] :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ}

variable (j : ℕ)
set_option quotPrecheck false
local notation "Edge" => (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))
variable (base : (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "Point" => ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "PairScene" => CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "MacroScene" => (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- Original population accuracy and true energy produce full compact readout
integrability and expectation convergence through the SAME two weak stages.
No uniform-integrability or readout-limit assumption is made. -/
theorem original_full_tagged_compact_readout_expectation_limits_of_face
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hκ : ∀ i, (κ i).IsAddHaarMeasure)
    (hbalance : μ.map a = ν.map a)
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
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : μ Aᶜ = 0) (hνB : ν Bᶜ = 0)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (nearRadius : ℝ) (hnearRadius : 0 < nearRadius)
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n) (hscale : Tendsto scale atTop atTop)
    (hnormalization : ∀ n, scale n ^ finrank ℝ (P j).seed.covector.ker = (n : ℝ) + 1)
    (ap am : ∀ (_ℓ n : ℕ),
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hpm : ∀ ℓ n k, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ ap ℓ n z.1 z.2 k))
    (hmm : ∀ ℓ n k, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ am ℓ n z.1 z.2 k))
    (hfp : ∀ ℓ n,
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ w.2 (ap ℓ n w))
    (hfm : ∀ ℓ n,
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ w.2 (am ℓ n w))
    (rootDomain : ℕ → Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
    (hrootDomain : ∀ n, volume (rootDomain n) = ENNReal.ofReal ((n : ℝ) + 1))
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
    (U : Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
    (hU : IsOpen U) (hUf : volume U ≠ ⊤)
    (χ : C_c(Edge, ℝ)) (hχU : tsupport χ ⊆ {e : Edge | e.1.1 ∈ U})
    (tag : BoundedContinuousFunction (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) ℝ) :
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
    ∀ (Qfull : ℕ → ProbabilityMeasure MacroScene) (Rfull : ProbabilityMeasure MacroScene)
      (φ : ℕ → ℕ → ℕ), (∀ ℓ, StrictMono (φ ℓ)) →
      ∀ ψ : ℕ → ℕ, StrictMono ψ →
      (∀ ℓ, Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Qfull ℓ))) →
      Tendsto (fun ℓ ↦ Qfull (ψ ℓ)) atTop (𝓝 Rfull) →
      (∀ plus : Bool,
        (∀ ℓ, Integrable (physicalSceneFullTaggedCompactReadout base χ plus tag)
          (Qfull ℓ : Measure MacroScene) ∧
          (∀ᶠ n in atTop, Integrable (physicalSceneFullTaggedCompactReadout base χ plus tag)
            (laws ℓ (φ ℓ n) : Measure MacroScene)) ∧
          Tendsto (fun n ↦ ∫ s, physicalSceneFullTaggedCompactReadout base χ plus tag s
            ∂(laws ℓ (φ ℓ n) : Measure MacroScene)) atTop
            (𝓝 (∫ s, physicalSceneFullTaggedCompactReadout base χ plus tag s
              ∂(Qfull ℓ : Measure MacroScene)))) ∧
        Integrable (physicalSceneFullTaggedCompactReadout base χ plus tag)
          (Rfull : Measure MacroScene) ∧
        Tendsto (fun ℓ ↦ ∫ s, physicalSceneFullTaggedCompactReadout base χ plus tag s
          ∂(Qfull (ψ ℓ) : Measure MacroScene)) atTop
          (𝓝 (∫ s, physicalSceneFullTaggedCompactReadout base χ plus tag s
            ∂(Rfull : Measure MacroScene)))) ∧
      (∀ ℓ, Integrable (fun s ↦
          |physicalSceneFullTaggedCompactReadout base χ true tag s -
            physicalSceneFullTaggedCompactReadout base χ false tag s|)
          (Qfull ℓ : Measure MacroScene) ∧
        (∀ᶠ n in atTop, Integrable (fun s ↦
          |physicalSceneFullTaggedCompactReadout base χ true tag s -
            physicalSceneFullTaggedCompactReadout base χ false tag s|)
          (laws ℓ (φ ℓ n) : Measure MacroScene)) ∧
        Tendsto (fun n ↦ ∫ s,
          |physicalSceneFullTaggedCompactReadout base χ true tag s -
            physicalSceneFullTaggedCompactReadout base χ false tag s|
          ∂(laws ℓ (φ ℓ n) : Measure MacroScene)) atTop
          (𝓝 (∫ s, |physicalSceneFullTaggedCompactReadout base χ true tag s -
            physicalSceneFullTaggedCompactReadout base χ false tag s|
            ∂(Qfull ℓ : Measure MacroScene)))) ∧
      Integrable (fun s ↦ |physicalSceneFullTaggedCompactReadout base χ true tag s -
        physicalSceneFullTaggedCompactReadout base χ false tag s|)
        (Rfull : Measure MacroScene) ∧
      Tendsto (fun ℓ ↦ ∫ s,
        |physicalSceneFullTaggedCompactReadout base χ true tag s -
          physicalSceneFullTaggedCompactReadout base χ false tag s|
        ∂(Qfull (ψ ℓ) : Measure MacroScene)) atTop
        (𝓝 (∫ s, |physicalSceneFullTaggedCompactReadout base χ true tag s -
          physicalSceneFullTaggedCompactReadout base χ false tag s|
          ∂(Rfull : Measure MacroScene))) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let _instHaar (k : ℕ) : (κ k).IsAddHaarMeasure := hκ k
  classical
  intro H laws Qfull Rfull φ hφ ψ hψ hinner houter
  have hμAs : ∀ᵐ x ∂μ, x ∈ A := hμA
  have hνBs : ∀ᵐ y ∂ν, y ∈ B := hνB
  obtain ⟨gap, hgap, hdist⟩ := exists_original_support_gap hA hB hAB
  obtain ⟨Dseq, hscreen, _hμtail, _hνtail, hpopulation⟩ :=
    exists_original_small_clock_screen_core_sequence_of_face hcore hrecovery hF hcomplete hu ha hinj
      hκ hbalance hA hB hμAs hνBs hνreg hμreg hface (by positivity : 0 < gap / 2)
  have hbud (k : ℕ) := (Dseq k).exists_original_full_tagged_compact_clipping_budget_of_iterated j base
    hF hcomplete hu ha hinj horder hA.measurableSet hB.measurableSet hμA hνB
    gap nearRadius hgap hdist hnearRadius (hscreen k) scale hscalePos hscale hnormalization
    ap am hpm hmm hfp hfm rootDomain hrootDomain Energy hEnergy hEp hEm
    rootCarrier hrootCarrier hrootIn U hU hUf χ hχU tag
    Qfull Rfull φ hφ ψ hψ hinner houter
  choose K hK c hc hfinite using hbud
  let C : ℝ≥0∞ := ENNReal.ofReal (2 * ‖tag‖ * ‖χ.toBoundedContinuousFunction‖) * volume U
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hUf
  let δerror : ℕ → ℝ≥0∞ := fun k ↦ C *
    (μ (⋃ i, (Dseq k).physicalCoreDomain i)ᶜ + ν (⋃ i, (Dseq k).physicalCoreDomain i)ᶜ)
  have hδ : Tendsto δerror atTop (𝓝 0) := by
    simpa only [δerror, mul_zero] using ENNReal.Tendsto.const_mul hpopulation (Or.inr hC)
  let sample : ℕ → ℕ → ℕ → ℝ≥0∞ := fun k _ n ↦ C *
    (Energy / ENNReal.ofReal (scale n ^ 2 * c k))
  have hsample (k ℓ : ℕ) : Tendsto (sample k ℓ) atTop (𝓝 0) := by
    have hscale2 : Tendsto (fun n ↦ scale n ^ 2) atTop atTop :=
      (tendsto_pow_atTop (α := ℝ) (by decide : (2 : ℕ) ≠ 0)).comp hscale
    have hden : Tendsto (fun n ↦ ENNReal.ofReal (scale n ^ 2 * c k)) atTop (𝓝 ⊤) :=
      ENNReal.tendsto_ofReal_nhds_top.mpr (hscale2.atTop_mul_const (hc k))
    have hdiv : Tendsto (fun n ↦ Energy / ENNReal.ofReal (scale n ^ 2 * c k))
        atTop (𝓝 0) := by
      simpa only [ENNReal.div_top] using ENNReal.Tendsto.div tendsto_const_nhds
        (Or.inr (by simp)) hden (Or.inr hEnergy)
    simpa only [sample, mul_zero] using ENNReal.Tendsto.const_mul hdiv (Or.inr hC)
  constructor
  · intro plus
    have hresult := integrable_and_tendsto_integral_of_iterated_weak_vanishing_clipping_errors
      laws Qfull Rfull φ (fun ℓ ↦ (hφ ℓ).tendsto_atTop) ψ hinner houter
      (physicalSceneFullTaggedCompactReadout base χ plus tag)
      (continuous_physicalSceneFullTaggedCompactReadout base χ plus tag)
      K hK δerror hδ sample hsample (fun k ℓ ↦ Eventually.of_forall fun n ↦ by
        simpa only [δerror, sample, C, mul_add, mul_assoc] using hfinite k ℓ n plus)
    exact ⟨hresult.2.1, hresult.2.2.2.1, hresult.2.2.2.2⟩
  · exact integrable_and_tendsto_integral_abs_sub_of_iterated_weak_clipping_errors
      laws Qfull Rfull φ (fun ℓ ↦ (hφ ℓ).tendsto_atTop) ψ hinner houter
      (physicalSceneFullTaggedCompactReadout base χ true tag)
      (physicalSceneFullTaggedCompactReadout base χ false tag)
      (continuous_physicalSceneFullTaggedCompactReadout base χ true tag)
      (continuous_physicalSceneFullTaggedCompactReadout base χ false tag)
      K hK δerror hδ sample hsample
      (fun k ℓ ↦ Eventually.of_forall fun n ↦ by
        simpa only [δerror, sample, C, mul_add, mul_assoc] using hfinite k ℓ n true)
      (fun k ℓ ↦ Eventually.of_forall fun n ↦ by
        simpa only [δerror, sample, C, mul_add, mul_assoc] using hfinite k ℓ n false)

end OTSelector.Reconstruction
