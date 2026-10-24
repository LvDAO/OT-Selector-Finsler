import OTSelector.Reconstruction.FinslerSeedRootPartition
import OTSelector.Geometry.Finsler.Calibration.SeedPairReadout
import OTSelector.MeasureTheory.InjectiveObservationDetermination

/-!
# Original compact coordinate probes determine regular ray couplings

The actual conditional population law covers the original source by its
countable fixed seed pieces. The original seed coordinate and both unchanged
clocks identify physical endpoint pairs, so these tests determine the entire
original coupling after restriction to those same source pieces.
-/
open Set Function MeasureTheory Manifold Module OTSelector.Geometry
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
variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
include hF hcomplete hu ha hinj

/-- Normalization of the original conditional population law gives full
physical source coverage by the fixed original seed pieces. -/
theorem PopulationConditionalWindowLaw.ae_mem_physicalSceneOriginalSeedSources
    {μ : Measure M} [IsFiniteMeasure μ] {ρ : M → ℝ} {v : ℕ → E → ℝ}
    (hlaw : PopulationConditionalWindowLaw P a κ lambda μ ρ v)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hκ : ∀ j, SigmaFinite (κ j)) :
    ∀ᵐ x ∂μ, x ∈ ⋃ j, physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := lambda) j := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instFinite : IsFiniteMeasure lambda := hlaw.label_law ▸ inferInstance
  have hroot := hlaw.ae_mem_populationSeedRootPieces P a κ lambda
    hF hcomplete hu ha hinj horder hκ
  have hm : MeasurableSet (⋃ j, populationSeedRootPiece P a κ lambda j) :=
    MeasurableSet.iUnion fun j ↦ measurableSet_populationSeedRootPiece
      P a κ lambda hF hcomplete hu ha hinj j
  have hrootMap : ∀ᵐ z ∂μ.map a, z ∈ ⋃ j, populationSeedRootPiece P a κ lambda j := by
    rw [hlaw.label_law]
    exact hroot
  have hx := (ae_map_iff ha.aemeasurable hm).mp hrootMap
  filter_upwards [hx] with x hx
  change a x ∈ ⋃ j, populationSeedRootPiece P a κ lambda j at hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨j, hj⟩

/-- All compact probes in one actual original seed coordinate determine the
original plan on that source piece. -/
theorem original_seed_restriction_eq_of_compact_probe_eq
    [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
    {π₀ π₁ : Measure (M × M)} [IsFiniteMeasure π₀] [IsFiniteMeasure π₁]
    (hπ₀ : ∀ᵐ p ∂π₀, p.1 ∈ F.potentialRegularDomain u ∧
      p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2)
    (hπ₁ : ∀ᵐ p ∂π₁, p.1 ∈ F.potentialRegularDomain u ∧
      p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2)
    (j : ℕ)
    (htest : ∀ g : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ),
      ∫ p, g (physicalSceneOriginalSeedPairReadout (P := P) (a := a) j p)
        ∂π₀.restrict (physicalSceneOriginalSeedSource
          (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ univ) =
      ∫ p, g (physicalSceneOriginalSeedPairReadout (P := P) (a := a) j p)
        ∂π₁.restrict (physicalSceneOriginalSeedSource
          (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ univ)) :
    π₀.restrict (physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ univ) =
    π₁.restrict (physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ univ) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  have hH : MeasurableSet (physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ (univ : Set M)) :=
    (measurableSet_physicalSceneOriginalSeedSource
    (P := P) (a := a) (κ := κ) (lambda := lambda) hF hcomplete hu ha hinj j).prod
      MeasurableSet.univ
  apply measure_eq_of_compactProbe_integral_eq_of_injOn_ae
    (measurable_physicalSceneOriginalSeedPairReadout hF hcomplete hu ha hinj j)
    (measurableSet_physicalSceneOriginalSeedRegularRayPairs
      (P := P) (a := a) (κ := κ) (lambda := lambda) hF hcomplete hu ha hinj j)
    (physicalSceneOriginalSeedPairReadout_injOn
      (P := P) (a := a) (κ := κ) (lambda := lambda) hF hcomplete hu ha hinj j)
    (π₀ := π₀.restrict _) (π₁ := π₁.restrict _) ?_ ?_ htest
  · filter_upwards [ae_restrict_mem hH, ae_restrict_of_ae hπ₀] with p hp hreg
    exact ⟨hp.1, hreg⟩
  · filter_upwards [ae_restrict_mem hH, ae_restrict_of_ae hπ₁] with p hp hreg
    exact ⟨hp.1, hreg⟩

/-- The unchanged original conditional population law and compact probes on
its fixed countable seed pieces determine the entire regular same-ray coupling. -/
theorem original_coupling_eq_of_seed_compact_probe_eq
    {μ : Measure M} [IsFiniteMeasure μ] {ρ : M → ℝ} {v : ℕ → E → ℝ}
    (hlaw : PopulationConditionalWindowLaw P a κ lambda μ ρ v)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hκ : ∀ j, SigmaFinite (κ j))
    {π₀ π₁ : Measure (M × M)} [IsFiniteMeasure π₀] [IsFiniteMeasure π₁]
    (hsource₀ : π₀.fst = μ) (hsource₁ : π₁.fst = μ)
    (hπ₀ : ∀ᵐ p ∂π₀, p.1 ∈ F.potentialRegularDomain u ∧
      p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2)
    (hπ₁ : ∀ᵐ p ∂π₁, p.1 ∈ F.potentialRegularDomain u ∧
      p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2)
    (htest : ∀ j : ℕ,
      ∀ g : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ),
      ∫ p, g (physicalSceneOriginalSeedPairReadout (P := P) (a := a) j p)
        ∂π₀.restrict (physicalSceneOriginalSeedSource
          (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ univ) =
      ∫ p, g (physicalSceneOriginalSeedPairReadout (P := P) (a := a) j p)
        ∂π₁.restrict (physicalSceneOriginalSeedSource
          (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ univ)) :
    π₀ = π₁ := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instFinite : IsFiniteMeasure lambda := hlaw.label_law ▸ inferInstance
  let _instSigma : ∀ j, SigmaFinite (κ j) := hκ
  have hcover := hlaw.ae_mem_physicalSceneOriginalSeedSources hF hcomplete hu ha hinj horder hκ
  have hcover₀ : ∀ᵐ x ∂π₀.fst, x ∈ ⋃ j, physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := lambda) j := by
    rw [hsource₀]
    exact hcover
  have hcover₁ : ∀ᵐ x ∂π₁.fst, x ∈ ⋃ j, physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := lambda) j := by
    rw [hsource₁]
    exact hcover
  apply measure_eq_of_restrict_eq_on_ae_iUnion
    (D := fun j ↦ physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ (univ : Set M))
  · filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hcover₀] with p hp
    obtain ⟨j, hj⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨j, hj, mem_univ p.2⟩
  · filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hcover₁] with p hp
    obtain ⟨j, hj⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨j, hj, mem_univ p.2⟩
  · intro j
    exact original_seed_restriction_eq_of_compact_probe_eq hF hcomplete hu ha hinj
      hπ₀ hπ₁ j (htest j)

end OTSelector.Reconstruction
