import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalSourceReferenceExtension
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalClockScreenAccuracy
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedProjectedSourceAbsoluteContinuity
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMaskedDecomposition
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalMaskedLossLimit

/-!
# Full original source absolute continuity on the same two weak limits

The original optimal face constructs a vanishing-loss core sequence. Each
core supplies actual conditional-clock references and an auxiliary extension
projecting onto the SAME full scene law. Original population losses tend to
zero only after the fixed-tilt sample limit and the outer tilt limit. A countable
spatial cover yields absolute continuity of the full average source marginal.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

local instance originalFullSourceACStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalFullSourceACConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance originalFullSourceACConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalFullSourceACConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalFullSourceACPlanPolish {ι : Type*} [Fintype ι] :
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

/-- The original optimal face and true energy bounds give full source AC on
every prescribed original two-stage scene limit. All accuracy cores, references
and projected auxiliary laws are constructed inside the proof. -/
theorem ae_original_full_source_absolutelyContinuous_of_face
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
 :
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
      ∀ᵐ s ∂(Rfull : Measure MacroScene),
        (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge).fst ≪
          (volume : Measure (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)).prod
            (volume : Measure ℝ) := by
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
  let error : ℕ → ℝ≥0∞ := fun k ↦ (((k + 1 : ℕ) : ℝ≥0∞))⁻¹
  have herror : Tendsto error atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hlocal (U : Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
      (hU : IsOpen U) (hUf : volume U ≠ ⊤) :
      ∀ᵐ s ∂(Rfull : Measure MacroScene),
        (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge).fst.restrict (U ×ˢ univ) ≪
          (volume : Measure (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)).prod
            (volume : Measure ℝ) := by
    have hexists (k : ℕ) := (Dseq k).exists_original_retained_source_reference_extension j base
      hF hcomplete hu ha hinj horder hA.measurableSet hB.measurableSet hμA hνB
      gap nearRadius hgap hdist hnearRadius (hscreen k) scale hscalePos hscale hnormalization
      ap am hpm hmm hfp hfm rootDomain hrootDomain Energy hEnergy hEp hEm
      rootCarrier hrootCarrier hrootIn U hU hUf (error k) (by simp [error])
    choose reference hfinite hregular hac href using hexists
    have haux (k : ℕ) := href k Qfull Rfull φ hφ ψ hψ hinner houter
    choose Raux hprojection hdecomposition hretained hlost using haux
    let _instRegular (k : ℕ) : (reference k).OuterRegular := hregular k
    have hloss : Tendsto (fun k ↦ volume U *
        (μ (⋃ i, (Dseq k).physicalCoreDomain i)ᶜ +
          ν (⋃ i, (Dseq k).physicalCoreDomain i)ᶜ)) atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul hpopulation (Or.inr hUf)
    exact ae_full_source_restrict_absolutelyContinuous_of_actual_projected_masked_accuracy
      base Rfull Raux hprojection U hU _ reference hac error
      (fun k ↦ volume U * (μ (⋃ i, (Dseq k).physicalCoreDomain i)ᶜ +
        ν (⋃ i, (Dseq k).physicalCoreDomain i)ᶜ)) herror hloss hdecomposition hretained hlost
  let windows : ℕ → Set Point := fun k ↦ Metric.ball 0 ((k : ℝ) + 1) ×ˢ univ
  have hcover : ⋃ k, windows k = univ := by
    apply eq_univ_of_forall
    intro p
    obtain ⟨k, hk⟩ := exists_nat_gt ‖p.1‖
    apply mem_iUnion.mpr
    refine ⟨k, ?_, mem_univ _⟩
    change dist p.1 0 < (k : ℝ) + 1
    rw [dist_zero_right]
    exact hk.trans (by linarith)
  apply ae_absolutelyContinuous_fst_of_countable_source_restrictions
    (Rfull : Measure MacroScene) (fun s ↦ LocalFiniteMeasure.cavityAverage s.2.1) _ windows
    (fun k ↦ Metric.isOpen_ball.measurableSet.prod MeasurableSet.univ) hcover
  intro k
  have h := hlocal _ Metric.isOpen_ball (ne_top_of_le_ne_top
    (isCompact_closedBall (0 : Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) ((k : ℝ) + 1)).measure_ne_top
    (measure_mono Metric.ball_subset_closedBall))
  filter_upwards [h] with s hs
  rw [fst_restrict_sourceProduct_eq_restrict_fst _ _
    (Metric.isOpen_ball.measurableSet.prod MeasurableSet.univ)]
  exact hs

end OTSelector.Reconstruction
