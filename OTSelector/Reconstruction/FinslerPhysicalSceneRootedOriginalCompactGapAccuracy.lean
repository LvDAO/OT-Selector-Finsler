import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalRetainedCompactGapExtension
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalFullAgreement
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalClockScreenAccuracy
/-!
# Agreement of the same original opposite tilted full scene plans

Original full-source absolute continuity, the actual countable clock carrier,
exact full marginal equality and the original macro-cost cycle inequality
are produced for the same prescribed two-stage scene law. Genuine original
clock-dependent coefficient distinction gives full-plan equality on its actual
countable target cloud without spatial injectivity of that cloud.
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

local instance originalCompactGapAccuracyStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalCompactGapAccuracyConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance originalCompactGapAccuracyConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalCompactGapAccuracyConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalCompactGapAccuracyPlanPolish {ι : Type*} [Fintype ι] :
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

/-- Original accuracy is sent to zero only after the SAME prescribed inner sample
and outer tilt limits. Every auxiliary readout keeps its actual masked weak witnesses. -/
theorem exists_original_retained_compact_gap_accuracy_of_face
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
    (U : Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
    (hU : IsOpen U) (hUf : volume U ≠ ⊤)
    (χ : C_c(Edge, ℝ)) (hχU : tsupport χ ⊆ {e : Edge | e.1.1 ∈ U}) :
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
      ∀ accuracy : ℝ≥0∞, accuracy ≠ 0 →
      ∃ δloss : ℝ≥0∞,
      ∃ D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
          (fun z ↦ ∃ π : Measure (ℝ × ℝ),
            Vlasov.IsCoupling π (condDistrib u a μ z) (condDistrib u a ν z) ∧
              ∀ᵐ p ∂π, p.1 ≤ p.2) r δloss δloss,
      let maskedLaws : ℕ → ℕ → ProbabilityMeasure JointScene := fun ℓ n ↦
        actualAllocationRootedMaskedMacroscopicSceneLaw base
          ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ
          (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n)
          (fun w ↦ w.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst)
          H (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j)
          (D.retainedNearCarrierEvent A B nearRadius)
          (D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hAsupport.measurableSet hBsupport.measurableSet nearRadius)
          (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n))
          (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale n))
          u (by
            let _inst : MetricSpace M := F.metricSpace
            exact hu.continuous.measurable) (scale n) (rootDomain n) (hrootDomain n)
      ∃ Qaux : ℕ → ProbabilityMeasure JointScene, ∃ θ : ℕ → ℕ → ℕ,
        (∀ ℓ, StrictMono (θ ℓ) ∧ StrictMono (fun n ↦ φ ℓ (θ ℓ n)) ∧
          Tendsto (fun n ↦ maskedLaws ℓ (φ ℓ (θ ℓ n))) atTop (𝓝 (Qaux ℓ)) ∧
          (Qaux ℓ).map (f := Prod.fst) measurable_fst.aemeasurable = Qfull ℓ ∧
          ∀ᵐ s ∂(Qaux ℓ : Measure JointScene),
            s ∈ physicalSceneMaskedDecompositionCarrier base) ∧
        ∃ Raux : ProbabilityMeasure JointScene, ∃ η : ℕ → ℕ,
          StrictMono η ∧ StrictMono (fun ℓ ↦ ψ (η ℓ)) ∧
          Tendsto (fun ℓ ↦ Qaux (ψ (η ℓ))) atTop (𝓝 Raux) ∧
          Raux.map (f := Prod.fst) measurable_fst.aemeasurable = Rfull ∧
          (∀ᵐ s ∂(Raux : Measure JointScene),
            s ∈ physicalSceneMaskedDecompositionCarrier base) ∧
          (∫⁻ s, physicalSceneMaskedLostSourceMass base U s ∂(Raux : Measure JointScene)) ≤
            volume U * (μ (⋃ i, D.physicalCoreDomain i)ᶜ +
              ν (⋃ i, D.physicalCoreDomain i)ᶜ) ∧
          (∫⁻ s, ENNReal.ofReal |LocalFiniteMeasure.testIntegral s.2.1.1 χ -
            LocalFiniteMeasure.testIntegral s.2.1.2 χ| ∂(Raux : Measure JointScene)) ≤
            accuracy ∧
          ∀ tag : BoundedContinuousFunction (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) ℝ,
            (∫⁻ s, ENNReal.ofReal |tag s.1.1 *
              (LocalFiniteMeasure.testIntegral s.2.1.1 χ -
                LocalFiniteMeasure.testIntegral s.2.1.2 χ)| ∂(Raux : Measure JointScene)) ≤
              ENNReal.ofReal ‖tag‖ * accuracy := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  classical
  intro H laws Qfull Rfull φ hφ ψ hψ hinner houter accuracy haccuracy
  have hfp (ℓ n : ℕ) :
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ w.2 (ap ℓ n w) := (hp ℓ n).mono fun _ hw ↦ hw.1
  have hfm (ℓ n : ℕ) :
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ w.2 (am ℓ n w) := (hm ℓ n).mono fun _ hw ↦ hw.1
  have hfull := ae_original_full_plans_eq_of_face j base
    hF hcomplete hu ha hinj horder hdim m hμchart hνchart nearRadius
    scale hscalePos hscale hnormalization probe hprobe G hprobeBound t ht0 ht0lim
    ap am hpm hmm hp hm rootDomain hrootDomain hμlaw hνlaw
    hAsupport hBsupport hAB hμreg hνreg hκ hbalance hcore hrecovery hface
    hμA hνB hnearRadius Energy hEnergy hEp hEm rootCarrier hrootCarrier hrootIn
    Qfull Rfull φ hφ ψ hψ hinner houter
  have hμAs : ∀ᵐ x ∂μ, x ∈ A := hμA
  have hνBs : ∀ᵐ y ∂ν, y ∈ B := hνB
  obtain ⟨gap, hgap, hdist⟩ := exists_original_support_gap hAsupport hBsupport hAB
  obtain ⟨Dseq, hscreen, _hμtail, _hνtail, hpopulation⟩ :=
    exists_original_small_clock_screen_core_sequence_of_face hcore hrecovery hF hcomplete hu ha hinj
      hκ hbalance hAsupport hBsupport hμAs hνBs hνreg hμreg hface
        (by positivity : 0 < gap / 2)
  let C : ℝ≥0∞ := ENNReal.ofReal (2 * ‖χ.toBoundedContinuousFunction‖) * volume U
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hUf
  have hlim : Tendsto (fun k ↦ C *
      (μ (⋃ i, (Dseq k).physicalCoreDomain i)ᶜ +
        ν (⋃ i, (Dseq k).physicalCoreDomain i)ᶜ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hpopulation (Or.inr hC)
  obtain ⟨k, hk⟩ := ((tendsto_order.mp hlim).2 accuracy
    (bot_lt_iff_ne_bot.mpr haccuracy)).exists
  obtain ⟨Qaux, θ, hQaux, Raux, η, hη, hψη, hRouter, hRmap, hdecomp,
      hlost, hχgap, htaggap⟩ := (Dseq k).exists_original_retained_compact_gap_extension j base
    hF hcomplete hu ha hinj horder hAsupport.measurableSet hBsupport.measurableSet hμA hνB
    gap nearRadius hgap hdist hnearRadius (hscreen k) scale hscalePos hscale
    ap am hpm hmm hfp hfm rootDomain hrootDomain Energy hEnergy hEp hEm
    rootCarrier hrootCarrier hrootIn U hU hUf χ hχU Qfull Rfull φ hφ ψ hψ hinner houter hfull
  have hsmall : ENNReal.ofReal (2 * ‖χ.toBoundedContinuousFunction‖) *
      (volume U * (μ (⋃ i, (Dseq k).physicalCoreDomain i)ᶜ +
        ν (⋃ i, (Dseq k).physicalCoreDomain i)ᶜ)) ≤ accuracy := by
    simpa only [C, mul_assoc] using hk.le
  refine ⟨(((k + 1 : ℕ) : ℝ≥0∞))⁻¹, Dseq k, Qaux, θ, hQaux, Raux, η,
    hη, hψη, hRouter, hRmap, hdecomp, hlost, hχgap.trans hsmall, ?_⟩
  intro tag
  apply (htaggap tag).trans
  have hfactor : ENNReal.ofReal (2 * ‖tag‖ * ‖χ.toBoundedContinuousFunction‖) =
      ENNReal.ofReal ‖tag‖ * ENNReal.ofReal (2 * ‖χ.toBoundedContinuousFunction‖) := by
    rw [← ENNReal.ofReal_mul (norm_nonneg _)]
    congr 1
    ring
  rw [hfactor, mul_assoc]
  exact mul_le_mul_right hsmall _

end OTSelector.Reconstruction
