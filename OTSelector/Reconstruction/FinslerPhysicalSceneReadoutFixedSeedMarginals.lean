import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSeedCountableMarginals
import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutFixedIterated
import OTSelector.Reconstruction.FinslerPhysicalSceneLimitCountableForward

/-!
# Actual legal fixed seed scene limits with exact full marginals

The same original two-index allocation family supplies both weak-limit stages,
the actual countable target carrier and a positive legal clock gap. Actual
fixed-frame tail and crossing estimates give exact full limiting marginals.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  TopologicalSpace OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

local instance originalFixedCompleteMarginalStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalFixedCompleteMarginalConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance originalFixedCompleteMarginalConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalFixedCompleteMarginalConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalFixedCompleteMarginalPlanPolish {ι : Type*} [Fintype ι] : PolishSpace
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


/-- Original physical hypotheses produce both weak-limit stages, an actual target carrier,
a positive clock gap, locally finite full marginals, and their exact equality. -/
theorem exists_original_fixed_seed_iterated_legal_scene_common_marginals
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

    (base : ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)) :
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let hH := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (spatialScale n)
    let hcoord := fun n ↦ measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj
      j (spatialScale n)
    let sceneLaw := fun ℓ n ↦ actualAllocationRootedCountableSceneLaw base
      ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ
      (aplus ℓ n) (aminus ℓ n) (hplus ℓ n) (hminus ℓ n)
      (fun z ↦ z.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst)
      H hH (coord n) (hcoord n) u (by
        let _inst : MetricSpace M := F.metricSpace
        exact hu.continuous.measurable) (rootDomain n) (hRoot n)
    ∃ Q : ℕ → ProbabilityMeasure (CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × LocalConfiguration base), ∃ φ : ℕ → ℕ → ℕ,
      (∀ ℓ, StrictMono (φ ℓ) ∧
        Tendsto (fun n ↦ sceneLaw ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ))) ∧
      ∃ R : ProbabilityMeasure (CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × LocalConfiguration base), ∃ ψ : ℕ → ℕ,
        StrictMono ψ ∧ Tendsto (fun k ↦ Q (ψ k)) atTop (𝓝 R) ∧
        ∃ gap' : ℝ, 0 < gap' ∧ ∀ᵐ scene ∂(R : Measure (CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × LocalConfiguration base)),
          (Function.support (LocalConfiguration.multiplicity scene.2)).Countable ∧
          (∀ᵐ e ∂(scene.1.1 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))),
            e.2 ∈ Function.support (LocalConfiguration.multiplicity scene.2) ∧
              gap' / 2 ≤ e.2.2 - e.1.2) ∧
          (∀ᵐ e ∂(scene.1.2 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))),
            e.2 ∈ Function.support (LocalConfiguration.multiplicity scene.2) ∧
              gap' / 2 ≤ e.2.2 - e.1.2) ∧
          IsFiniteMeasureOnCompacts (scene.1.1 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).fst ∧
          IsFiniteMeasureOnCompacts (scene.1.2 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).fst ∧
          IsFiniteMeasureOnCompacts (scene.1.1 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).snd ∧
          IsFiniteMeasureOnCompacts (scene.1.2 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).snd ∧
          (scene.1.1 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).fst = (scene.1.2 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).fst ∧
          (scene.1.1 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).snd = (scene.1.2 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).snd := by
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
  obtain ⟨Q, φ, hinner, R, ψ, hψ, houter, gap', hgap', hproperties⟩ :=
    exists_given_potential_iterated_legal_scene_locallyFinite_marginals base μ ν
      hA hB hAB hμ hν u hu (fun n ↦ spatialScale n ^ 2)
      (fun n ↦ sq_pos_of_pos (hsp n)) hscale aplus aminus hplus hminus hfp hfm C hC hep hem
      (fun _ ↦ H) (fun _ ↦ hH) coord hcoord rootDomain hRoot
  have hlocal : ∀ᵐ scene ∂(R : Measure (CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × LocalConfiguration base)),
      (IsFiniteMeasureOnCompacts (scene.1.1 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).fst ∧
        IsFiniteMeasureOnCompacts (scene.1.2 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).fst) ∧
      (IsFiniteMeasureOnCompacts (scene.1.1 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).snd ∧
        IsFiniteMeasureOnCompacts (scene.1.2 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).snd) :=
    hproperties.mono fun scene hs ↦ by
      rcases hs with ⟨_hc, _hp, _hm, hsp, hsm, htp, htm⟩
      exact ⟨⟨hsp, hsm⟩, htp, htm⟩
  have hequal := ae_common_marginals_of_original_fixed_seed_iterated_countable_scene
    hcore hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hμ hν hreg hμreg hface
    hgap hdist j aplus aminus hplus hminus hfp hfm spatialScale hsp hscale
    rootDomain hRoot C hC hEp hEm base R Q φ
    (fun ℓ ↦ (hinner ℓ).1.tendsto_atTop) ψ (fun ℓ ↦ (hinner ℓ).2) houter hlocal
  refine ⟨Q, φ, hinner, R, ψ, hψ, houter, gap', hgap', ?_⟩
  filter_upwards [hproperties, hequal] with scene hs he
  rcases hs with ⟨hc, hp, hm, hsp, hsm, htp, htm⟩
  exact ⟨hc, hp, hm, hsp, hsm, htp, htm, he.1, he.2⟩

end OTSelector.Reconstruction
