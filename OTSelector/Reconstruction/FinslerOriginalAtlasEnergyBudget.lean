import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSeed
import OTSelector.Reconstruction.OriginalGlobalAllocationMeanPlan

/-! The actual countable seed restrictions spend the original global physical
energy only once, before changing coordinates or passing to any local limit. -/
open Set Function MeasureTheory ProbabilityTheory Manifold
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [BorelSpace M] in
/-- The original physical source pieces inherit the actual root partition's
pairwise disjointness, independently of every auxiliary finite core. -/
theorem pairwiseDisjoint_physicalSceneOriginalSeedSource :
    Pairwise (Disjoint on physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := lambda)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  exact Set.disjoint_left.mp (pairwiseDisjoint_populationSeedRootPiece P a κ lambda hij)
    hxi hxj

variable [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]

/-- All actual seed restrictions together cost at most the original physical
plan energy. This is one global budget, with no factor for the number of seeds. -/
theorem tsum_originalSeed_sourceEnergy_le
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (Γ : Measure (M × M)) (energy : M × M → ℝ≥0∞) :
    (∑' j, ∫⁻ p in
      physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ
        (univ : Set M), energy p ∂Γ) ≤ ∫⁻ p, energy p ∂Γ := by
  let H := fun j ↦ physicalSceneOriginalSeedSource
    (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ (univ : Set M)
  have hH (j : ℕ) : MeasurableSet (H j) :=
    (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j).prod
      MeasurableSet.univ
  have hdisj : Pairwise (Disjoint on H) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hpi hpj
    exact Set.disjoint_left.mp (pairwiseDisjoint_physicalSceneOriginalSeedSource hij)
      hpi.1 hpj.1
  rw [← lintegral_iUnion hH hdisj energy]
  exact lintegral_mono' Measure.restrict_le_self le_rfl

omit [TopologicalSpace M] [T2Space M] [PreconnectedSpace M] [BorelSpace M] in
/-- Set energy of the actual original mean plan is precisely the mean set
energy of those same sampled physical allocation plans. -/
theorem setLIntegral_originalGlobalAllocationMeanPlan
    (μ ν : Measure M) [IsFiniteMeasure μ] (n : ℕ)
    (allocation : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) →
      M → Fin (n + 1) → ℝ)
    (hmeas : ∀ j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ allocation z.1 z.2 j))
    (energy : M × M → ℝ≥0∞) (henergy : Measurable energy)
    {H : Set (M × M)} (hH : MeasurableSet H) :
    (∫⁻ p in H, energy p ∂originalGlobalAllocationMeanPlan μ ν n allocation) =
      ∫⁻ z, ∫⁻ p in H, energy p
        ∂physicalSceneGlobalAllocationFamily μ allocation (fun z ↦ z.1) z
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) := by
  calc
    _ = ∫⁻ p, H.indicator energy p
        ∂originalGlobalAllocationMeanPlan μ ν n allocation := (lintegral_indicator hH energy).symm
    _ = _ := lintegral_originalGlobalAllocationMeanPlan μ ν n allocation hmeas _
      (henergy.indicator hH)
    _ = _ := lintegral_congr (fun _ ↦ lintegral_indicator hH energy)

/-- All actual seed-restricted expected energies, in the original sampled
experiment, share the single full original expected energy budget. -/
theorem tsum_originalSeed_sampledSourceEnergy_le
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (μ ν : Measure M) [IsFiniteMeasure μ] (n : ℕ)
    (allocation : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) →
      M → Fin (n + 1) → ℝ)
    (hmeas : ∀ j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ allocation z.1 z.2 j))
    (energy : M × M → ℝ≥0∞) (henergy : Measurable energy) :
    (∑' j, ∫⁻ z, ∫⁻ p in physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ (univ : Set M), energy p
      ∂physicalSceneGlobalAllocationFamily μ allocation (fun z ↦ z.1) z
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
      ∫⁻ z, ∫⁻ p, energy p
        ∂physicalSceneGlobalAllocationFamily μ allocation (fun z ↦ z.1) z
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) := by
  let H := fun j ↦ physicalSceneOriginalSeedSource
    (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ (univ : Set M)
  have hH (j : ℕ) : MeasurableSet (H j) :=
    (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j).prod
      MeasurableSet.univ
  calc
    _ = ∑' j, ∫⁻ p in H j, energy p
        ∂originalGlobalAllocationMeanPlan μ ν n allocation := by
      apply tsum_congr
      intro j
      exact (setLIntegral_originalGlobalAllocationMeanPlan μ ν n allocation hmeas
        energy henergy (hH j)).symm
    _ ≤ ∫⁻ p, energy p ∂originalGlobalAllocationMeanPlan μ ν n allocation :=
      tsum_originalSeed_sourceEnergy_le hF hcomplete hu ha hinj _ energy
    _ = _ := lintegral_originalGlobalAllocationMeanPlan μ ν n allocation hmeas energy henergy

end OTSelector.Reconstruction
