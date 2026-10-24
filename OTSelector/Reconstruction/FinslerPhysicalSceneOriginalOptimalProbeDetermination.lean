import OTSelector.Geometry.Finsler.Calibration.PopulationConditionalLaw
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalSeedCountableProbeDetermination
import OTSelector.Geometry.Finsler.Calibration.OptimalFaceCarrier
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalSeedCompactProbe

/-!
# Original optimal plans are determined by fixed countable seed probes

The original optimal-face representation internally supplies the unchanged
regular same-ray carrier. The actual conditional population law supplies
countable seed coverage, and the original probes then determine the full plan.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ : M → ℝ} {v : ℕ → E → ℝ}
variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
  (hlaw : PopulationConditionalWindowLaw P a κ lambda μ ρ v)
  (horder : let _inst : MetricSpace M := F.metricSpace
    ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
  (hκ : ∀ j, SigmaFinite (κ j))
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
include hF hcomplete hu ha hinj hlaw horder hκ hface

/-- The original complete optimal face and conditional population law reduce
full plan equality to the fixed countable original coordinate probes. -/
theorem original_optimal_plans_eq_of_countable_seed_probe_eq_of_face
    {π₀ π₁ : Measure (M × M)}
    (hπ₀ : let _inst : MetricSpace M := F.metricSpace; IsOptimalCoupling edist μ ν π₀)
    (hπ₁ : let _inst : MetricSpace M := F.metricSpace; IsOptimalCoupling edist μ ν π₁)
    (htest : ∀ j : ℕ, ∀ i : ℕ ⊕ (ℕ × ℕ),
      ∫ p, physicalSceneOriginalSeedSeparatingProbe (P := P) j i
          (physicalSceneOriginalSeedPairReadout (P := P) (a := a) j p)
        ∂π₀.restrict (physicalSceneOriginalSeedSource
          (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ univ) =
      ∫ p, physicalSceneOriginalSeedSeparatingProbe (P := P) j i
          (physicalSceneOriginalSeedPairReadout (P := P) (a := a) j p)
        ∂π₁.restrict (physicalSceneOriginalSeedSource
          (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ univ)) :
    π₀ = π₁ := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  have _instMap₀ : IsProbabilityMeasure (π₀.map Prod.fst) := hπ₀.1.1.symm ▸ inferInstance
  have _instMap₁ : IsProbabilityMeasure (π₁.map Prod.fst) := hπ₁.1.1.symm ▸ inferInstance
  have _instPlan₀ : IsProbabilityMeasure π₀ := Measure.isProbabilityMeasure_of_map Prod.fst
  have _instPlan₁ : IsProbabilityMeasure π₁ := Measure.isProbabilityMeasure_of_map Prod.fst
  have hcarrier₀ := ae_original_regular_sameLabel_forward_of_optimal_face
    hF hcomplete hu ha hface hπ₀
  have hcarrier₁ := ae_original_regular_sameLabel_forward_of_optimal_face
    hF hcomplete hu ha hface hπ₁
  exact original_coupling_eq_of_countable_seed_probe_eq hF hcomplete hu ha hinj
    hlaw horder hκ hπ₀.1.1 hπ₁.1.1
    (hcarrier₀.mono fun p hp ↦ ⟨hp.1, hp.2.1, hp.2.2.1⟩)
    (hcarrier₁.mono fun p hp ↦ ⟨hp.1, hp.2.1, hp.2.2.1⟩) htest

/-- Countably many almost-everywhere original probe identities determine random
original optimizers on one common event, without a measurable equality predicate. -/
theorem ae_original_optimal_plans_eq_of_countable_seed_probe_ae_eq_of_face
    {Ω : Type*} [MeasurableSpace Ω] (R : Measure Ω)
    (π₀ π₁ : Ω → Measure (M × M))
    (hπ₀ : ∀ᵐ sample ∂R, let _inst : MetricSpace M := F.metricSpace;
      IsOptimalCoupling edist μ ν (π₀ sample))
    (hπ₁ : ∀ᵐ sample ∂R, let _inst : MetricSpace M := F.metricSpace;
      IsOptimalCoupling edist μ ν (π₁ sample))
    (htest : ∀ j : ℕ, ∀ i : ℕ ⊕ (ℕ × ℕ), ∀ᵐ sample ∂R,
      ∫ p, physicalSceneOriginalSeedSeparatingProbe (P := P) j i
          (physicalSceneOriginalSeedPairReadout (P := P) (a := a) j p)
        ∂(π₀ sample).restrict (physicalSceneOriginalSeedSource
          (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ univ) =
      ∫ p, physicalSceneOriginalSeedSeparatingProbe (P := P) j i
          (physicalSceneOriginalSeedPairReadout (P := P) (a := a) j p)
        ∂(π₁ sample).restrict (physicalSceneOriginalSeedSource
          (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ univ)) :
    ∀ᵐ sample ∂R, π₀ sample = π₁ sample := by
  have hall := ae_all_iff.mpr fun j ↦ ae_all_iff.mpr fun i ↦ htest j i
  filter_upwards [hπ₀, hπ₁, hall] with sample hopt₀ hopt₁ hreadout
  exact original_optimal_plans_eq_of_countable_seed_probe_eq_of_face
    hF hcomplete hu ha hinj hlaw horder hκ hface hopt₀ hopt₁ hreadout

/-- The literal bounded physical indicator probes determine original optimizers;
the exact source-restriction readout identities are discharged internally. -/
theorem original_optimal_plans_eq_of_original_seed_probe_eq_of_face
    {π₀ π₁ : Measure (M × M)}
    (hπ₀ : let _inst : MetricSpace M := F.metricSpace; IsOptimalCoupling edist μ ν π₀)
    (hπ₁ : let _inst : MetricSpace M := F.metricSpace; IsOptimalCoupling edist μ ν π₁)
    (htest : ∀ j : ℕ, ∀ i : ℕ ⊕ (ℕ × ℕ),
      ∫ p, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
          (lambda := lambda) j (physicalSceneOriginalSeedSeparatingProbe (P := P) j i)
          p.1 p.2 ∂π₀ =
      ∫ p, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
          (lambda := lambda) j (physicalSceneOriginalSeedSeparatingProbe (P := P) j i)
          p.1 p.2 ∂π₁) :
    π₀ = π₁ := by
  let _instFinite : IsFiniteMeasure lambda := hlaw.label_law ▸ inferInstance
  let _instSigma : ∀ j, SigmaFinite (κ j) := hκ
  apply original_optimal_plans_eq_of_countable_seed_probe_eq_of_face
    hF hcomplete hu ha hinj hlaw horder hκ hface hπ₀ hπ₁
  intro j i
  rw [← integral_physicalSceneOriginalSeedCompactProbe_eq_restrict_readout
    hF hcomplete hu ha hinj j _ π₀,
    ← integral_physicalSceneOriginalSeedCompactProbe_eq_restrict_readout
      hF hcomplete hu ha hinj j _ π₁]
  exact htest j i

/-- One common almost-everywhere event of literal original physical probe
identities identifies random original optimal plans. -/
theorem ae_original_optimal_plans_eq_of_original_seed_probe_ae_eq_of_face
    {Ω : Type*} [MeasurableSpace Ω] (R : Measure Ω)
    (π₀ π₁ : Ω → Measure (M × M))
    (hπ₀ : ∀ᵐ sample ∂R, let _inst : MetricSpace M := F.metricSpace;
      IsOptimalCoupling edist μ ν (π₀ sample))
    (hπ₁ : ∀ᵐ sample ∂R, let _inst : MetricSpace M := F.metricSpace;
      IsOptimalCoupling edist μ ν (π₁ sample))
    (htest : ∀ j : ℕ, ∀ i : ℕ ⊕ (ℕ × ℕ), ∀ᵐ sample ∂R,
      ∫ p, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
          (lambda := lambda) j (physicalSceneOriginalSeedSeparatingProbe (P := P) j i)
          p.1 p.2 ∂π₀ sample =
      ∫ p, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
          (lambda := lambda) j (physicalSceneOriginalSeedSeparatingProbe (P := P) j i)
          p.1 p.2 ∂π₁ sample) :
    ∀ᵐ sample ∂R, π₀ sample = π₁ sample := by
  have hall := ae_all_iff.mpr fun j ↦ ae_all_iff.mpr fun i ↦ htest j i
  filter_upwards [hπ₀, hπ₁, hall] with sample hopt₀ hopt₁ hreadout
  exact original_optimal_plans_eq_of_original_seed_probe_eq_of_face
    hF hcomplete hu ha hinj hlaw horder hκ hface hopt₀ hopt₁ hreadout

end OTSelector.Reconstruction
