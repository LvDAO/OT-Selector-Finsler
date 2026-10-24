import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalCyclePairAccuracy
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedCyclePairExhaustion
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalClockScreenAccuracy
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedProjectedCyclePairAccuracy
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMaskedDecomposition
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalMaskedLossLimit
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalClockCarrierConcentration
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalCoreConcentration
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalRationalClockLimit
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalMacroRetainedStrictSupport

/-!
# Actual original full-scene legal two-cycle optimality

The original optimal face produces arbitrarily accurate auxiliary cores. Each
core has its actual retained/lost extension of the prescribed full original
scene law. Both scene limits are fixed before the original core complement is
sent to zero. Countable compact and clock/gain exhaustion then yields one
common event with the true macro-dependent cost inequality for all legal pairs.
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

local instance originalTwoCycleStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalTwoCycleConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance originalTwoCycleConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalTwoCycleConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalTwoCyclePlanPolish {ι : Type*} [Fintype ι] :
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

/-- Original iid-target times Dirichlet global opposite optimizers produce
legal full-plan two-cycle optimality on the SAME prescribed two-stage scene
limit. Core sequences, retained certificates, lost-mass limits and the full
positive clock gap are all constructed from the original inputs internally. -/
theorem ae_original_full_twoCycle_cost_le_of_face
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
    (hrootIn : ∀ n z, z ∈ rootDomain n → physicalSceneMacroscopicRoot (scale n) z ∈ rootCarrier) :
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
        ∀ᵐ p ∂(LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge).prod
          (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge),
          (p.1.1.2 < p.1.2.2 ∧ p.2.1.2 < p.2.2.2 ∧
            p.1.1.2 < p.2.2.2 ∧ p.2.1.2 < p.1.2.2) →
          physicalSceneOriginalMacroCost (P := P) (a := a) j s.1 p.1.1 p.1.2 +
            physicalSceneOriginalMacroCost (P := P) (a := a) j s.1 p.2.1 p.2.2 ≤
          physicalSceneOriginalMacroCost (P := P) (a := a) j s.1 p.1.1 p.2.2 +
            physicalSceneOriginalMacroCost (P := P) (a := a) j s.1 p.2.1 p.1.2 := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  classical
  intro H laws Qfull Rfull φ hφ ψ hψ hinner houter
  have hμAs : ∀ᵐ x ∂μ, x ∈ A := by rw [ae_iff]; exact hμA
  have hνBs : ∀ᵐ y ∂ν, y ∈ B := by rw [ae_iff]; exact hνB
  obtain ⟨physicalGap, hphysicalGap, hdist⟩ := exists_original_support_gap hAsupport hBsupport hAB
  let Areg := A ∩ F.potentialRegularDomain u
  let Breg := B ∩ F.potentialRegularDomain u
  have hAreg : MeasurableSet Areg :=
    hAsupport.measurableSet.inter (hF.measurableSet_potentialRegularDomain hcomplete u)
  have hBreg : MeasurableSet Breg :=
    hBsupport.measurableSet.inter (hF.measurableSet_potentialRegularDomain hcomplete u)
  have hμAreg : μ Aregᶜ = 0 := (hμAs.and hμreg)
  have hνBreg : ν Bregᶜ = 0 := (hνBs.and hνreg)
  apply ae_physicalScene_twoCycle_cost_le_of_compact_cyclePairMass_zero
    (Rfull : Measure MacroScene)
    (fun s : MacroScene ↦ LocalFiniteMeasure.cavityAverage s.2.1)
    (fun s : MacroScene ↦ physicalSceneOriginalMacroCost (P := P) (a := a) j s.1)
  intro K hK k l
  let g : ℝ := 1 / ((k : ℝ) + 1)
  let margin : ℝ := 1 / ((l : ℝ) + 1)
  have hg : 0 < g := by dsimp only [g]; positivity
  have hmargin0 : 0 ≤ margin := by dsimp only [margin]; positivity
  let θ := min (physicalGap / 4) g
  have hθ : 0 < θ := lt_min (by positivity) hg
  obtain ⟨Dseq, hscreen, hμtail, hνtail, hpopulation⟩ :=
    exists_original_small_clock_screen_core_sequence_of_face hcore hrecovery hF hcomplete hu ha hinj
      hκ hbalance hAsupport hBsupport hμAs hνBs hνreg hμreg hface hθ
  obtain ⟨W, hW⟩ := (hK.image (continuous_fst.fst : Continuous (fun e : Edge ↦ e.1.1))).isBounded.exists_norm_le
  let U := Metric.ball (0 : Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) (|W| + 1)
  have hU : IsOpen U := Metric.isOpen_ball
  have hUf : volume U ≠ ⊤ := ne_top_of_le_ne_top
    (isCompact_closedBall (0 : Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) (|W| + 1)).measure_ne_top
    (measure_mono Metric.ball_subset_closedBall)
  have hKU : K ⊆ {e | e.1.1 ∈ U} := by
    intro e he
    change dist e.1.1 0 < |W| + 1
    rw [dist_zero_right]
    exact lt_of_le_of_lt ((hW e.1.1 (mem_image_of_mem _ he)).trans (le_abs_self W)) (by linarith)
  exact PopulationLocalPressureCore.ae_original_full_cyclePairMass_zero_of_core_accuracy j base Dseq
    hF hcomplete hu ha hinj horder hdim m hμchart hνchart hAsupport hμAs
    hAreg hBreg (fun _ hx ↦ hx.2) (fun _ hx ↦ hx.2) nearRadius
    scale hscalePos hscale probe hprobe G hprobeBound t ht0 ht0lim ap am hpm hmm hp hm
    rootDomain hrootDomain hμlaw hνlaw physicalGap g margin hmargin0
    (fun q i ↦ (hscreen q i).trans_lt (lt_of_le_of_lt (min_le_left _ _) (by linarith)))
    (fun q i ↦ (hscreen q i).trans (min_le_right _ _)) K hK
    hphysicalGap (fun x hx y hy ↦ hdist x hx.1 y hy.1) hμAreg hνBreg hnearRadius
    Energy hEnergy hEp hEm rootCarrier hrootCarrier hrootIn U hU hUf hKU hpopulation
    Qfull Rfull φ hφ ψ hψ hinner houter
end OTSelector.Reconstruction
