import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutMacroscopicMarginals

/-!
# Original full limiting marginals and actual countable target support

Every prescribed original macroscopic sample/tilt weak limit inherits the exact
full common marginals and its own realized countable target cloud. Original
feasible allocation families and their true global energy supply all inputs.
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

local instance originalFullLimitStructureStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalFullLimitStructureConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance originalFullLimitStructureConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalFullLimitStructureConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalFullLimitStructurePlanPolish {ι : Type*} [Fintype ι] :
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

/-- Original feasibility, population accuracy and global energy determine the full structure
of the SAME prescribed macroscopic weak limit, without a marginal or carrier premise. -/
theorem ae_original_full_limit_structure_of_face
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
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n) (hscale : Tendsto scale atTop atTop)
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
        ((s.2.1.1 : Measure Edge).fst = (s.2.1.2 : Measure Edge).fst ∧
          (s.2.1.1 : Measure Edge).snd = (s.2.1.2 : Measure Edge).snd) ∧
        (Function.support (LocalConfiguration.multiplicity s.2.2)).Countable ∧
        (∀ᵐ e ∂(s.2.1.1 : Measure Edge),
          e.2 ∈ Function.support (LocalConfiguration.multiplicity s.2.2)) ∧
        (∀ᵐ e ∂(s.2.1.2 : Measure Edge),
          e.2 ∈ Function.support (LocalConfiguration.multiplicity s.2.2)) ∧
        (IsFiniteMeasureOnCompacts (s.2.1.1 : Measure Edge).fst ∧
          IsFiniteMeasureOnCompacts (s.2.1.2 : Measure Edge).fst) ∧
        (IsFiniteMeasureOnCompacts (s.2.1.1 : Measure Edge).snd ∧
          IsFiniteMeasureOnCompacts (s.2.1.2 : Measure Edge).snd) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  intro H sceneLaw Qfull Rfull φ hφ ψ hψ hinner houter
  have hμAs : ∀ᵐ x ∂μ, x ∈ A := hμA
  have hνBs : ∀ᵐ y ∂ν, y ∈ B := hνB
  obtain ⟨gap, hgap, hdist⟩ := exists_original_support_gap hA hB hAB
  have hscaleSquare : Tendsto (fun n ↦ scale n ^ 2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by decide : (2 : ℕ) ≠ 0)).comp hscale
  have hH : MeasurableSet H :=
    measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
  let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
  have hcoord (n : ℕ) : Measurable (coord n) :=
    measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale n)
  let Penv := fun n ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  let Y := fun n (z : (Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) ↦ z.1
  have hY (n : ℕ) (k : Fin (n + 1)) : Measurable (fun z ↦ Y n z k) :=
    (measurable_pi_apply k).comp measurable_fst
  let Qplain := fun ℓ ↦ (Qfull ℓ).map (f := Prod.snd) measurable_snd.aemeasurable
  let Rplain := Rfull.map (f := Prod.snd) measurable_snd.aemeasurable
  let laws := fun ℓ n ↦ actualAllocationRootedCountableSceneLaw base (Penv n) μ
    (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n) (Y n) (hY n)
    H hH (coord n) (hcoord n) u hu.continuous.measurable (rootDomain n) (hrootDomain n)
  have hinnerplain (ℓ : ℕ) : Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Qplain ℓ)) := by
    have hw := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      _ (Qfull ℓ) (hinner ℓ) continuous_snd
    simpa only [sceneLaw, map_actualAllocationRootedMacroscopicSceneLaw_scene] using hw
  have houterplain : Tendsto (Qplain ∘ ψ) atTop (𝓝 Rplain) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ Rfull houter continuous_snd
  have hsource := ae_iterated_actualAllocationRootedScene_source_locallyFinite base
    id Penv μ ap am hpm hmm Y hY (fun _ z ↦ z.2) hfp hfm
    (fun _ ↦ H) (fun _ ↦ hH) coord hcoord u hu.continuous.measurable rootDomain hrootDomain
    Qplain φ hinnerplain Rplain ψ houterplain
  have htarget := ae_iterated_actualAllocationRootedScene_target_locallyFinite base
    id Penv μ ap am hpm hmm Y hY (fun _ z ↦ z.2) hfp hfm
    (fun _ ↦ H) (fun _ ↦ hH) coord hcoord u hu.continuous.measurable rootDomain hrootDomain
    Qplain φ hinnerplain Rplain ψ houterplain
  have hlocal := hsource.and htarget
  have hequal := ae_common_marginals_of_original_fixed_seed_iterated_countable_scene
    hcore hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hμAs hνBs hνreg hμreg hface
    hgap hdist j ap am hpm hmm hfp hfm scale hscalePos hscaleSquare
    rootDomain hrootDomain Energy hEnergy hEp hEm base Rplain Qplain φ
    (fun ℓ ↦ (hφ ℓ).tendsto_atTop) ψ hinnerplain houterplain hlocal
  have hfinite (ℓ n : ℕ) : ∀ᵐ s ∂(laws ℓ n : Measure (CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × LocalConfiguration base)),
      SupportedOverConfiguration Prod.snd s.2 s.1.1 ∧
        SupportedOverConfiguration Prod.snd s.2 s.1.2 :=
    ae_physicalSceneRootedCountableLocalSceneLaw_supported base (Penv n)
      (physicalSceneGlobalAllocationFamily μ (ap ℓ n) (Y n))
      (physicalSceneGlobalAllocationFamily μ (am ℓ n) (Y n))
      (measurable_physicalSceneGlobalAllocationFamily μ (ap ℓ n) (hpm ℓ n) (Y n) (hY n))
      (measurable_physicalSceneGlobalAllocationFamily μ (am ℓ n) (hmm ℓ n) (Y n) (hY n))
      H hH (coord n) (hcoord n) u hu.continuous.measurable (Y n) (hY n) (rootDomain n) (hrootDomain n)
      (ae_physicalSceneGlobalAllocationFamily_targets (Penv n) μ (ap ℓ n) (Y n)
        (fun z ↦ z.2) (hfp ℓ n))
      (ae_physicalSceneGlobalAllocationFamily_targets (Penv n) μ (am ℓ n) (Y n)
        (fun z ↦ z.2) (hfm ℓ n))
  have hinnerSupport (ℓ : ℕ) : ∀ᵐ s ∂(Qplain ℓ : Measure (CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × LocalConfiguration base)),
      SupportedOverConfiguration Prod.snd s.2 s.1.1 ∧
        SupportedOverConfiguration Prod.snd s.2 s.1.2 :=
    (ae_supportedOverConfiguration_of_weak_tendsto (Qplain ℓ) _ (hinnerplain ℓ)
      Prod.snd continuous_snd Prod.snd (fun s ↦ s.1.1) continuous_snd continuous_fst.fst
      (fun n ↦ (hfinite ℓ (φ ℓ n)).mono fun _ h ↦ h.1)).and
    (ae_supportedOverConfiguration_of_weak_tendsto (Qplain ℓ) _ (hinnerplain ℓ)
      Prod.snd continuous_snd Prod.snd (fun s ↦ s.1.2) continuous_snd continuous_fst.snd
      (fun n ↦ (hfinite ℓ (φ ℓ n)).mono fun _ h ↦ h.2))
  have hsupportPlus := ae_supportedOverConfiguration_of_weak_tendsto Rplain _ houterplain
    Prod.snd continuous_snd Prod.snd (fun s ↦ s.1.1) continuous_snd continuous_fst.fst
    (fun k ↦ (hinnerSupport (ψ k)).mono fun _ h ↦ h.1)
  have hsupportMinus := ae_supportedOverConfiguration_of_weak_tendsto Rplain _ houterplain
    Prod.snd continuous_snd Prod.snd (fun s ↦ s.1.2) continuous_snd continuous_fst.snd
    (fun k ↦ (hinnerSupport (ψ k)).mono fun _ h ↦ h.2)
  have hplain := ((hsource.and htarget).and hequal).and
    (hsupportPlus.and hsupportMinus)
  have hlift := ae_of_ae_map measurable_snd.aemeasurable hplain
  filter_upwards [hlift] with s hs
  rcases hs with ⟨⟨⟨hsrc, htgt⟩, hmeq⟩, hsupport⟩
  exact ⟨hmeq, countable_multiplicity_support s.2.2,
    (supportedOverConfiguration_iff_ae_mem Prod.snd continuous_snd _ _).mp hsupport.1,
    (supportedOverConfiguration_iff_ae_mem Prod.snd continuous_snd _ _).mp hsupport.2,
    hsrc, htgt⟩

end OTSelector.Reconstruction
