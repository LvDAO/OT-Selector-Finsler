import OTSelector.MeasureTheory.WeakClosedCarrier
import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSeedCountableMarginals
import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutFixedIterated
import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutMacroscopicIterated
import OTSelector.Reconstruction.FinslerPhysicalSceneLimitCountableForward

/-!
Conditions: Actual weak convergence of probability laws, a closed set and almost-everywhere support of every approximant there, under the stated outer-approximation topology assumptions.

Objects: The weak limit is carried on the same closed set.

Proof detail: Apply the open-set Portmanteau inequality to its complement and use zero approximating complement mass.

Sources: D. H. Fremlin, Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation (https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61).
Relation: Portmanteau closed-carrier corollary. The abstract HasOuterApproxClosed assumptions are retained rather than replaced by a book’s Radon/metric assumptions.
-/

/-!
# Actual original macroscopic scene limits with exact full marginals

The original macro root is retained jointly with both original global plans
and their common integer target carrier. Original feasibility and energy
produce both separate weak stages, positive legal clocks and locally finite
full marginals; the fixed-frame tail and crossing estimates identify both
full limiting marginal pairs exactly.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  TopologicalSpace OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

local instance originalFixedMacroCompleteMarginalStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalFixedMacroCompleteMarginalConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance originalFixedMacroCompleteMarginalConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalFixedMacroCompleteMarginalConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalFixedMacroCompleteMarginalPlanPolish {ι : Type*} [Fintype ι] : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace



variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M} {r : ℝ}


/-- The original fixed-frame macro-tagged experiment supplies both weak stages,
actual carrier and clocks, and exact full common limiting marginals. -/
theorem exists_original_fixed_seed_macroscopic_iterated_legal_scene_common_marginals
    (hcore : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hbalance : μ.map a = ν.map a)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hreg : ∀ᵐ x ∂ν, x ∈ F.potentialRegularDomain u)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
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
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (j : ℕ)
    (aplus aminus : ∀ (_ℓ n : ℕ),
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hplus : ∀ ℓ n k, Measurable (fun z : (((Fin (n + 1) → M) ×
      (Fin (n + 1) → ℝ)) × M) ↦ aplus ℓ n z.1 z.2 k))
    (hminus : ∀ ℓ n k, Measurable (fun z : (((Fin (n + 1) → M) ×
      (Fin (n + 1) → ℝ)) × M) ↦ aminus ℓ n z.1 z.2 k))
    (hfp : ∀ ℓ n, ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ z.2 (aplus ℓ n z))
    (hfm : ∀ ℓ n, ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ z.2 (aminus ℓ n z))
    (spatialScale : ℕ → ℝ) (hsp : ∀ n, 0 < spatialScale n)
    (hscale : Tendsto (fun n ↦ spatialScale n ^ 2) atTop atTop)
    (rootDomain : ℕ → Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
    (hRoot : ∀ n, volume (rootDomain n) = ENNReal.ofReal ((n : ℝ) + 1))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hEp : ∀ ℓ n, (∫⁻ w, ∫⁻ p, ENNReal.ofReal (spatialScale n ^ 2 *
      ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
      ∂physicalSceneGlobalAllocationFamily μ (aplus ℓ n) (fun z ↦ z.1) w
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C)
    (hEm : ∀ ℓ n, (∫⁻ w, ∫⁻ p, ENNReal.ofReal (spatialScale n ^ 2 *
      ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
      ∂physicalSceneGlobalAllocationFamily μ (aminus ℓ n) (fun z ↦ z.1) w
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C)

    (base : ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))
    (rootCarrier : Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)) (hCarrier : IsCompact rootCarrier)
    (hRootCarrier : ∀ n z, z ∈ rootDomain n →
      physicalSceneMacroscopicRoot (spatialScale n) z ∈ rootCarrier) :
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let hH := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (spatialScale n)
    let hcoord := fun n ↦ measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj
      j (spatialScale n)
    let sceneLaw := fun ℓ n ↦ actualAllocationRootedMacroscopicSceneLaw base
      ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ
      (aplus ℓ n) (aminus ℓ n) (hplus ℓ n) (hminus ℓ n)
      (fun z ↦ z.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst)
      H hH (coord n) (hcoord n) u (by
        let _inst : MetricSpace M := F.metricSpace
        exact hu.continuous.measurable) (spatialScale n) (rootDomain n) (hRoot n)
    ∃ Q : ℕ → ProbabilityMeasure ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × LocalConfiguration base)), ∃ φ : ℕ → ℕ → ℕ,
      (∀ ℓ, StrictMono (φ ℓ) ∧
        Tendsto (fun n ↦ sceneLaw ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ))) ∧
      ∃ R : ProbabilityMeasure ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × LocalConfiguration base)), ∃ ψ : ℕ → ℕ,
        StrictMono ψ ∧ Tendsto (fun k ↦ Q (ψ k)) atTop (𝓝 R) ∧
        ∃ gap' : ℝ, 0 < gap' ∧ ∀ᵐ scene ∂(R : Measure ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × LocalConfiguration base))),
          scene.1 ∈ rootCarrier ∧
          (Function.support (LocalConfiguration.multiplicity scene.2.2)).Countable ∧
          (∀ᵐ e ∂(scene.2.1.1 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))),
            e.2 ∈ Function.support (LocalConfiguration.multiplicity scene.2.2) ∧
              gap' / 2 ≤ e.2.2 - e.1.2) ∧
          (∀ᵐ e ∂(scene.2.1.2 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))),
            e.2 ∈ Function.support (LocalConfiguration.multiplicity scene.2.2) ∧
              gap' / 2 ≤ e.2.2 - e.1.2) ∧
          IsFiniteMeasureOnCompacts (scene.2.1.1 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).fst ∧
          IsFiniteMeasureOnCompacts (scene.2.1.2 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).fst ∧
          IsFiniteMeasureOnCompacts (scene.2.1.1 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).snd ∧
          IsFiniteMeasureOnCompacts (scene.2.1.2 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).snd ∧
          (scene.2.1.1 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).fst = (scene.2.1.2 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).fst ∧
          (scene.2.1.1 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).snd = (scene.2.1.2 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).snd := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  dsimp only
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
  have hH : MeasurableSet H :=
    measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
  let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (spatialScale n)
  have hcoord (n : ℕ) : Measurable (coord n) :=
    measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (spatialScale n)
  have hAB : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    have hd := hdist x hxA x hxB
    simp only [dist_self] at hd
    exact (not_le_of_gt hgap) hd
  let energy := fun n (e : M × M) ↦
    ENNReal.ofReal (spatialScale n ^ 2 * (dist e.1 e.2 - u e.2 + u e.1))
  have henergy (n : ℕ) : Measurable (energy n) :=
    ((((continuous_fst.dist continuous_snd).sub (hu.continuous.comp continuous_snd)).add
      (hu.continuous.comp continuous_fst)).const_mul (spatialScale n ^ 2)).measurable.ennreal_ofReal
  have hep (ℓ n : ℕ) : (∫⁻ w, ∫⁻ e,
      ENNReal.ofReal (spatialScale n ^ 2 * (dist e.1 (w.1 e.2) - u (w.1 e.2) + u e.1))
      ∂semidiscreteAllocationMeasure μ (aplus ℓ n w)
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C := by
    have h := hEp ℓ n
    change (∫⁻ w, ∫⁻ e, energy n e
      ∂physicalSceneGlobalAllocationFamily μ (aplus ℓ n) (fun z ↦ z.1) w
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C at h
    rw [lintegral_physicalSceneGlobalAllocationFamily_eq _ μ (aplus ℓ n)
      (fun z ↦ z.1) (fun z ↦ z.2) (hfp ℓ n) (fun _ ↦ energy n) (fun _ ↦ henergy n)] at h
    exact h
  have hem (ℓ n : ℕ) : (∫⁻ w, ∫⁻ e,
      ENNReal.ofReal (spatialScale n ^ 2 * (dist e.1 (w.1 e.2) - u (w.1 e.2) + u e.1))
      ∂semidiscreteAllocationMeasure μ (aminus ℓ n w)
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C := by
    have h := hEm ℓ n
    change (∫⁻ w, ∫⁻ e, energy n e
      ∂physicalSceneGlobalAllocationFamily μ (aminus ℓ n) (fun z ↦ z.1) w
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C at h
    rw [lintegral_physicalSceneGlobalAllocationFamily_eq _ μ (aminus ℓ n)
      (fun z ↦ z.1) (fun z ↦ z.2) (hfm ℓ n) (fun _ ↦ energy n) (fun _ ↦ henergy n)] at h
    exact h
  let Penv := fun n ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  let Y := fun n (z : (Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) ↦ z.1
  have hY (n : ℕ) (k : Fin (n + 1)) : Measurable (fun z ↦ Y n z k) :=
    (measurable_pi_apply k).comp measurable_fst
  obtain ⟨Q, φ, hinner, R, ψ, hψ, houter⟩ :=
    exists_iterated_actualAllocationRootedMacroscopicSceneLaw base id Penv μ
      aplus aminus hplus hminus Y hY (fun _ z ↦ z.2) hfp hfm
      (fun _ ↦ H) (fun _ ↦ hH) coord hcoord u hu.continuous.measurable spatialScale
      rootDomain hRoot rootCarrier hCarrier hRootCarrier
  let Qplain := fun ℓ ↦ (Q ℓ).map (f := Prod.snd) measurable_snd.aemeasurable
  let Rplain := R.map (f := Prod.snd) measurable_snd.aemeasurable
  let laws := fun ℓ n ↦ actualAllocationRootedCountableSceneLaw base (Penv n) μ
    (aplus ℓ n) (aminus ℓ n) (hplus ℓ n) (hminus ℓ n) (Y n) (hY n)
    H hH (coord n) (hcoord n) u hu.continuous.measurable (rootDomain n) (hRoot n)
  have hinnerplain (ℓ : ℕ) : Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Qplain ℓ)) := by
    have hw := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      _ (Q ℓ) (hinner ℓ).2 continuous_snd
    simpa only [map_actualAllocationRootedMacroscopicSceneLaw_scene] using hw
  have houterplain : Tendsto (Qplain ∘ ψ) atTop (𝓝 Rplain) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ R houter continuous_snd
  have hsource := ae_iterated_actualAllocationRootedScene_source_locallyFinite base
    id Penv μ aplus aminus hplus hminus Y hY (fun _ z ↦ z.2) hfp hfm
    (fun _ ↦ H) (fun _ ↦ hH) coord hcoord u hu.continuous.measurable rootDomain hRoot
    Qplain φ hinnerplain Rplain ψ houterplain
  have htarget := ae_iterated_actualAllocationRootedScene_target_locallyFinite base
    id Penv μ aplus aminus hplus hminus Y hY (fun _ z ↦ z.2) hfp hfm
    (fun _ ↦ H) (fun _ ↦ hH) coord hcoord u hu.continuous.measurable rootDomain hRoot
    Qplain φ hinnerplain Rplain ψ houterplain
  have hlocal := hsource.and htarget
  have hequal := ae_common_marginals_of_original_fixed_seed_iterated_countable_scene
    hcore hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hμ hν hreg hμreg hface
    hgap hdist j aplus aminus hplus hminus hfp hfm spatialScale hsp hscale
    rootDomain hRoot C hC hEp hEm base Rplain Qplain φ
    (fun ℓ ↦ (hinner ℓ).1.tendsto_atTop) ψ hinnerplain houterplain hlocal
  obtain ⟨gap', hgap', hclock⟩ := ae_iterated_actualAllocationRootedScene_clock_gap base
    id Penv μ ν hA hB hAB hμ hν aplus aminus hplus hminus Y hY
    (fun n k ↦ physicalSceneOriginalDirichlet_target_law ν n k) (fun _ z ↦ z.2)
    hfp hfm (fun _ ↦ H) (fun _ ↦ hH) coord hcoord hu (fun n ↦ spatialScale n ^ 2)
    (fun n ↦ sq_pos_of_pos (hsp n)) hscale rootDomain hRoot C hC hep hem
    Qplain φ (fun ℓ ↦ (hinner ℓ).1) hinnerplain Rplain ψ houterplain
  have hfinite (ℓ n : ℕ) : ∀ᵐ s ∂(laws ℓ n : Measure (CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × LocalConfiguration base)),
      SupportedOverConfiguration Prod.snd s.2 s.1.1 ∧
        SupportedOverConfiguration Prod.snd s.2 s.1.2 :=
    ae_physicalSceneRootedCountableLocalSceneLaw_supported base (Penv n)
      (physicalSceneGlobalAllocationFamily μ (aplus ℓ n) (Y n))
      (physicalSceneGlobalAllocationFamily μ (aminus ℓ n) (Y n))
      (measurable_physicalSceneGlobalAllocationFamily μ (aplus ℓ n) (hplus ℓ n) (Y n) (hY n))
      (measurable_physicalSceneGlobalAllocationFamily μ (aminus ℓ n) (hminus ℓ n) (Y n) (hY n))
      H hH (coord n) (hcoord n) u hu.continuous.measurable (Y n) (hY n) (rootDomain n) (hRoot n)
      (ae_physicalSceneGlobalAllocationFamily_targets (Penv n) μ (aplus ℓ n) (Y n)
        (fun z ↦ z.2) (hfp ℓ n))
      (ae_physicalSceneGlobalAllocationFamily_targets (Penv n) μ (aminus ℓ n) (Y n)
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
  have hplain := (((hsource.and htarget).and hequal).and hclock).and
    (hsupportPlus.and hsupportMinus)
  have hlift := ae_of_ae_map measurable_snd.aemeasurable hplain
  have htagFinite (ℓ n : ℕ) : ∀ᵐ s ∂(actualAllocationRootedMacroscopicSceneLaw base
      (Penv n) μ (aplus ℓ n) (aminus ℓ n) (hplus ℓ n) (hminus ℓ n) (Y n) (hY n)
      H hH (coord n) (hcoord n) u hu.continuous.measurable (spatialScale n)
      (rootDomain n) (hRoot n) : Measure ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × LocalConfiguration base))), s.1 ∈ rootCarrier :=
    ae_physicalSceneRootedMacroscopicSceneLaw_macro_mem base (Penv n)
      (physicalSceneGlobalAllocationFamily μ (aplus ℓ n) (Y n))
      (physicalSceneGlobalAllocationFamily μ (aminus ℓ n) (Y n))
      (measurable_physicalSceneGlobalAllocationFamily μ (aplus ℓ n) (hplus ℓ n) (Y n) (hY n))
      (measurable_physicalSceneGlobalAllocationFamily μ (aminus ℓ n) (hminus ℓ n) (Y n) (hY n))
      H hH (coord n) (hcoord n) u hu.continuous.measurable (spatialScale n)
      (Y n) (hY n) (rootDomain n) (hRoot n) rootCarrier hCarrier.measurableSet (hRootCarrier n)
  have htagInner (ℓ : ℕ) : ∀ᵐ s ∂(Q ℓ : Measure ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × LocalConfiguration base))), s.1 ∈ rootCarrier :=
    ae_closed_set_of_physicalScene_weak_tendsto (Q ℓ) _ (hinner ℓ).2
      (Prod.fst ⁻¹' rootCarrier) (hCarrier.isClosed.preimage continuous_fst)
      (fun n ↦ htagFinite ℓ (φ ℓ n))
  have htag := ae_closed_set_of_physicalScene_weak_tendsto R _ houter
    (Prod.fst ⁻¹' rootCarrier) (hCarrier.isClosed.preimage continuous_fst)
    (fun k ↦ htagInner (ψ k))
  refine ⟨Q, φ, hinner, R, ψ, hψ, houter, gap', hgap', ?_⟩
  filter_upwards [hlift, htag] with scene hs htag
  rcases hs with ⟨hfirst, hsupport⟩
  rcases hfirst with ⟨hsecond, hclock⟩
  rcases hsecond with ⟨hloc, hmeq⟩
  rcases hloc with ⟨hsrc, htgt⟩
  exact ⟨htag, countable_multiplicity_support scene.2.2,
    ((supportedOverConfiguration_iff_ae_mem Prod.snd continuous_snd _ _).mp hsupport.1).and hclock.1,
    ((supportedOverConfiguration_iff_ae_mem Prod.snd continuous_snd _ _).mp hsupport.2).and hclock.2,
    hsrc.1, hsrc.2, htgt.1, htgt.2, hmeq.1, hmeq.2⟩

end OTSelector.Reconstruction
