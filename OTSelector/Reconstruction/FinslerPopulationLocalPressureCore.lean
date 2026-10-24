import OTSelector.Reconstruction.FinslerPopulationHaarPressureCore
import OTSelector.Reconstruction.FinslerCoefficientCoreCoordinates

/-!
# Original physical cores for local pressure comparison

The original finite Haar intensity cores also retain one actual distance remainder
radius across the whole finite family. The physical populations, conditional
kernels, seed coefficients and original root masses are the same throughout.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- A finite original population core with continuous positive intensity, uniform
inverse moments and a uniform actual distance expansion on its retained windows. -/
structure PopulationLocalPressureCore (P : ℕ → F.CalibratedSeedWindow u)
    (a : M → (ℚ → M)) (κ : ∀ j, Measure (P j).seed.covector.ker)
    (lambda : Measure (ℚ → M)) (η₀ η₁ : Measure M)
    [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] (ρ₀ ρ₁ : M → ℝ) (v : ℕ → E → ℝ)
    (b : (ℚ → M) × ℝ → M) (Good : (ℚ → M) → Prop) (r : ℝ) (δ ε : ℝ≥0∞) where
  haar : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε
  remainder : ∀ η > 0, ∃ radius > 0, ∀ i : Fin haar.continuous.count,
    ∀ z ∈ (haar.continuous.coefficient i).roots,
      (haar.continuous.coefficient i).RemainderBound z η radius

/-- Arbitrarily large local pressure cores are produced from the original population
law, with arbitrary retained almost-everywhere information. -/
def PopulationLocalPressureCoreLaw (P : ℕ → F.CalibratedSeedWindow u)
    (a : M → (ℚ → M)) (κ : ∀ j, Measure (P j).seed.covector.ker)
    (lambda : Measure (ℚ → M)) (η₀ η₁ : Measure M)
    [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] (ρ₀ ρ₁ : M → ℝ) (v : ℕ → E → ℝ)
    (b : (ℚ → M) × ℝ → M) (r : ℝ) : Prop :=
  ∀ (Good : (ℚ → M) → Prop), (∀ᵐ z ∂lambda, Good z) →
    ∀ δ : ℝ≥0∞, δ ≠ 0 → ∀ ε : ℝ≥0∞, ε ≠ 0 →
      Nonempty (PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε)

/-- The original Haar law supplies the actual geometric remainder on a further
large compact core, preserving every intensity, moment and recovery identity. -/
theorem PopulationHaarPressureCoreLaw.local_core
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    [IsFiniteMeasure lambda] {η₀ η₁ : Measure M}
    [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M} {r : ℝ}
    (hcore : PopulationHaarPressureCoreLaw P a κ lambda η₀ η₁ ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b lambda η₀ η₁)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instLocalPressureCoreMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure) :
    PopulationLocalPressureCoreLaw P a κ lambda η₀ η₁ ρ₀ ρ₁ v b r := by
  let _instLocalPressureCoreMetric : MetricSpace M := F.metricSpace
  let _instLocalPressureCoreProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instLocalPressureCorePolish : PolishSpace M := inferInstance
  let _instLocalPressureCoreBorel : BorelSpace (ℚ → M) := inferInstance
  intro Good hGood δ hδ ε hε
  obtain ⟨D⟩ := hcore Good hGood δ hδ (ε / 2) (ENNReal.half_pos hε).ne'
  obtain ⟨K, hloss, hK, hrem⟩ :=
    OriginalPopulationCoefficientCore.exists_finite_uniform_distance_refinement
      hF hcomplete hu ha hinj D.continuous.coefficient hκ (ENNReal.half_pos hε).ne'
  have hsmall : lambda (⋃ i, K i)ᶜ < ε := by
    have hcover : (⋃ i, K i)ᶜ ⊆ D.continuous.population.rootsᶜ ∪
        ((⋃ i, (D.continuous.coefficient i).roots) \ ⋃ i, K i) := by
      intro z hz
      by_cases h : z ∈ D.continuous.population.roots
      · exact Or.inr ⟨D.continuous.union_eq.symm ▸ h, hz⟩
      · exact Or.inl h
    exact ((measure_mono hcover).trans (measure_union_le _ _)).trans_lt
      (by simpa only [ENNReal.add_halves] using
        ENNReal.add_lt_add D.continuous.population.complement_small hloss)
  exact ⟨{
    haar := D.refine hrecovery hcomplete ha hu.continuous.measurable
      (fun i ↦ (hK i).2.1) (fun i ↦ (hK i).1) hsmall
    remainder := hrem }⟩

/-- The actual source-fixed remainder is expressed in precisely the coordinates
used by the retained coefficient and the local quadratic pressure comparison. -/
theorem PopulationLocalPressureCore.source_remainder_on_piece
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
    {Good : (ℚ → M) → Prop} {r : ℝ} {δ ε : ℝ≥0∞}
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instLocalSourceMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) :
    ∀ η > 0, ∃ radius > 0, ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      (D.haar.continuous.coefficient i).SourceCoordinateRemainderBound z η radius := by
  let _instLocalSourceMetric : MetricSpace M := F.metricSpace
  let _instLocalSourceProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instLocalSourcePolish : PolishSpace M := inferInstance
  let _instLocalSourceBorel : BorelSpace (ℚ → M) := inferInstance
  apply (D.haar.continuous.coefficient i).uniform_source_remainder_in_coordinates
    hF hcomplete hu ha hinj Subset.rfl
  intro η hη
  obtain ⟨radius, hradius, hbound⟩ := D.remainder η hη
  exact ⟨radius, hradius, hbound i⟩

/-- One source-coordinate radius works simultaneously for every retained original
coefficient piece, with no further core selection. -/
theorem PopulationLocalPressureCore.source_remainder
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
    {Good : (ℚ → M) → Prop} {r : ℝ} {δ ε : ℝ≥0∞}
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instLocalCommonRadiusMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val))) :
    ∀ η > 0, ∃ radius > 0, ∀ i : Fin D.haar.continuous.count,
      ∀ z ∈ (D.haar.continuous.coefficient i).roots,
        (D.haar.continuous.coefficient i).SourceCoordinateRemainderBound z η radius := by
  classical
  intro η hη
  choose radius hpos hbound using fun i ↦
    D.source_remainder_on_piece hF hcomplete hu ha hinj i η hη
  obtain ⟨R, hR, hle⟩ :=
    (isCompact_univ : IsCompact (univ : Set (Fin D.haar.continuous.count))).exists_forall_le'
      (f := radius) continuous_of_discreteTopology.continuousOn (fun i _ ↦ hpos i)
  refine ⟨R, hR, ?_⟩
  intro i z hz t ht v hv hallowed
  exact hbound i z hz t ht v (hv.trans_le (hle i (mem_univ i))) hallowed

end OTSelector.Reconstruction
