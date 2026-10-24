import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSeedIteratedMarginals
import OTSelector.Reconstruction.FinslerPhysicalSceneLimitCountableForward
import OTSelector.MeasureTheory.MarginalLocalFinitenessMeasurability

/-!
# Exact full marginals in the actual countable target scene

Projecting only the auxiliary actual countable target carrier leaves the same
physical pair law. Both separate weak limits therefore retain the exact full
source and target marginals, while the actual carrier is kept in the final law.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  TopologicalSpace OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

local instance originalFixedCountableMarginalStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalFixedCountableMarginalConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance originalFixedCountableMarginalConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalFixedCountableMarginalConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalFixedCountableMarginalPlanPolish {ι : Type*} [Fintype ι] : PolishSpace
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


/-- The original actual iterated countable-target scene has exact full marginals. -/
theorem ae_common_marginals_of_original_fixed_seed_iterated_countable_scene
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
    ∀ (R : ProbabilityMeasure (CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × LocalConfiguration base))
      (Q : ℕ → ProbabilityMeasure (CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × LocalConfiguration base))
      (φ : ℕ → ℕ → ℕ), (∀ ℓ, Tendsto (φ ℓ) atTop atTop) → ∀ ψ : ℕ → ℕ,
      (∀ ℓ, Tendsto (fun n ↦ sceneLaw ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ))) →
      Tendsto (fun k ↦ Q (ψ k)) atTop (𝓝 R) →
      (∀ᵐ scene ∂(R : Measure (CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × LocalConfiguration base)),
        (IsFiniteMeasureOnCompacts (scene.1.1 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).fst ∧
          IsFiniteMeasureOnCompacts (scene.1.2 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).fst) ∧
        (IsFiniteMeasureOnCompacts (scene.1.1 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).snd ∧
          IsFiniteMeasureOnCompacts (scene.1.2 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).snd)) →
      ∀ᵐ scene ∂(R : Measure (CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × LocalConfiguration base)),
        (scene.1.1 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).fst = (scene.1.2 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).fst ∧
        (scene.1.1 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).snd = (scene.1.2 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).snd := by
  let _inst : MetricSpace M := F.metricSpace
  dsimp only
  intro R Q φ hφ ψ hinner houter hlocal
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
  have hH : MeasurableSet H :=
    measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
  let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (spatialScale n)
  have hcoord (n : ℕ) : Measurable (coord n) :=
    measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (spatialScale n)
  let laws := fun ℓ n ↦ actualAllocationRootedCountableSceneLaw base
    ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ
    (aplus ℓ n) (aminus ℓ n) (hplus ℓ n) (hminus ℓ n)
    (fun z ↦ z.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst)
    H hH (coord n) (hcoord n) u hu.continuous.measurable (rootDomain n) (hRoot n)
  let Rpair := R.map (f := Prod.fst) measurable_fst.aemeasurable
  let Qpair := fun ℓ ↦ (Q ℓ).map (f := Prod.fst) measurable_fst.aemeasurable
  have hinnerpair (ℓ : ℕ) : Tendsto (fun n ↦ actualAllocationRootedSceneLaw
      ((Measure.pi (fun _ : Fin (φ ℓ n + 1) ↦ ν)).prod (dirichletOne (φ ℓ n))) μ
      (aplus ℓ (φ ℓ n)) (aminus ℓ (φ ℓ n)) (hplus ℓ (φ ℓ n)) (hminus ℓ (φ ℓ n))
      (fun z ↦ z.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst)
      H hH (coord (φ ℓ n)) (hcoord (φ ℓ n)) u hu.continuous.measurable
      ((φ ℓ n : ℝ) + 1) (by positivity) (rootDomain (φ ℓ n)) (hRoot (φ ℓ n)))
      atTop (𝓝 (Qpair ℓ)) := by
    have hw := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n ↦ laws ℓ (φ ℓ n)) (Q ℓ) (hinner ℓ) continuous_fst
    simpa only [laws, map_actualAllocationRootedCountableSceneLaw_pair] using hw
  have houterpair : Tendsto (fun k ↦ Qpair (ψ k)) atTop (𝓝 Rpair) := by
    exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun k ↦ Q (ψ k)) R houter continuous_fst
  let K : CompactExhaustion ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) := physicalSceneSpatialClockExhaustion 0 0
  have hs := measurableSet_physicalScene_fst_locallyFinite (X := ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))
    (Y := ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)) K
  have ht := measurableSet_physicalScene_snd_locallyFinite (X := ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))
    (Y := ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)) K
  have hm : MeasurableSet {scene : CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) |
      (IsFiniteMeasureOnCompacts (scene.1 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).fst ∧
        IsFiniteMeasureOnCompacts (scene.2 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).fst) ∧
      (IsFiniteMeasureOnCompacts (scene.1 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).snd ∧
        IsFiniteMeasureOnCompacts (scene.2 : Measure (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))).snd)} :=
    ((hs.preimage measurable_fst).inter (hs.preimage measurable_snd)).inter
      ((ht.preimage measurable_fst).inter (ht.preimage measurable_snd))
  have hlocalpair := (ae_map_iff (μ := (R : Measure (CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × LocalConfiguration base)))
    measurable_fst.aemeasurable hm).mpr hlocal
  have hequal := ae_common_marginals_of_original_fixed_seed_iterated_scene
    hcore hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hμ hν hreg hμreg hface
    hgap hdist j aplus aminus hplus hminus hfp hfm spatialScale hsp hscale
    (fun n ↦ (n : ℝ) + 1) (fun _ ↦ by positivity) rootDomain hRoot C hC hEp hEm
    Rpair Qpair φ hφ ψ hinnerpair houterpair hlocalpair
  exact ae_of_ae_map measurable_fst.aemeasurable hequal

end OTSelector.Reconstruction
