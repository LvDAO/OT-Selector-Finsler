import OTSelector.Reconstruction.FinslerPhysicalSceneRootedPopulationSourceCover
import OTSelector.Reconstruction.FinslerCoefficientCorePartition

/-!
# Finite original source references on arbitrary retained subcells

The original Taylor partition splits every source observation exactly. Its seed
label images remain disjoint, so the actual variation defect is controlled by
local Haar mass independently of the number of original clock references.
-/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
namespace PopulationLocalPressureCore
variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)

/-- A finite original root partition splits every observed source subcell exactly. -/
theorem original_source_partition_observation_eq_sum
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count)
    (T : (D.haar.continuous.coefficient i).TaylorRootCover 1)
    (Q : FiniteRootNeighborhoodPartition (D.haar.continuous.coefficient i).roots
      T.centers T.neighborhood)
    {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    {X : Type*} [MeasurableSpace X]
    (obs : (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker × ℝ → X)
    (hobs : Measurable obs) (s : Set X) (hs : MeasurableSet s) :
    ((η₀.restrict (a ⁻¹' L)).map (fun x ↦ obs (D.haar.sceneCoordinate i x))) s =
      ∑ k : Fin Q.count,
        ((η₀.restrict (a ⁻¹' (Q.cell k ∩ L))).map
          (fun x ↦ obs (D.haar.sceneCoordinate i x))) s := by
  let _inst : MetricSpace M := F.metricSpace
  have hobs' : Measurable (fun x : M ↦ obs (D.haar.sceneCoordinate i x)) := by
    have hh := hobs.comp (D.haar.measurable_sceneCoordinate hF hcomplete hu ha hinj i)
    simpa only [Function.comp_def] using hh
  have hcover : (⋃ k : Fin Q.count, a ⁻¹' (Q.cell k ∩ L)) = a ⁻¹' L := by
    ext x
    simp only [mem_iUnion, mem_preimage, mem_inter_iff]
    constructor
    · rintro ⟨k, _, hx⟩
      exact hx
    · intro hx
      obtain ⟨k, hk⟩ := mem_iUnion.mp (Q.union_eq.symm ▸ hsub hx)
      exact ⟨k, hk, hx⟩
  have hd : Pairwise (fun k l : Fin Q.count ↦
      Disjoint (a ⁻¹' (Q.cell k ∩ L)) (a ⁻¹' (Q.cell l ∩ L))) := by
    intro k l hkl
    exact ((Q.disjoint hkl).mono inter_subset_left inter_subset_left).preimage a
  have hm : ∀ k : Fin Q.count, MeasurableSet (a ⁻¹' (Q.cell k ∩ L)) :=
    fun k ↦ ha ((Q.measurable_cell k).inter hL)
  rw [Measure.map_apply hobs' hs]
  simp_rw [Measure.map_apply hobs' hs]
  have hh := Measure.restrict_iUnion_apply (μ := η₀) hd hm (hobs' hs)
  rw [hcover, tsum_fintype] at hh
  exact hh

/-- The same original seed label remains injective on all retained cells,
so their Haar masses add without a partition-cardinality factor. -/
theorem sum_original_partition_cell_haar
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (i : Fin D.haar.continuous.count)
    (T : (D.haar.continuous.coefficient i).TaylorRootCover 1)
    (Q : FiniteRootNeighborhoodPartition (D.haar.continuous.coefficient i).roots
      T.centers T.neighborhood)
    {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots) :
    (∑ k : Fin Q.count, (κ (D.haar.continuous.coefficient i).seedIndex)
      (populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a ''
        (Q.cell k ∩ L))) =
      (κ (D.haar.continuous.coefficient i).seedIndex)
        (populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a '' L) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let C := D.haar.continuous.coefficient i
  let R := populationSeedRootLabelValue (P C.seedIndex).seed a
  have hRi : InjOn R C.roots := by
    intro z hz z' hz' he
    have hzI : z ∈ (D.haar.intensity i).roots := by rwa [D.haar.intensity_roots]
    have hzI' : z' ∈ (D.haar.intensity i).roots := by rwa [D.haar.intensity_roots]
    calc
      z = a ((P C.seedIndex).seed.curve (R z) 0) :=
        ((D.haar.intensity i).root_identity z hzI).symm
      _ = z' := by rw [he]; exact (D.haar.intensity i).root_identity z' hzI'
  have hd : Pairwise (fun k l : Fin Q.count ↦
      Disjoint (R '' (Q.cell k ∩ L)) (R '' (Q.cell l ∩ L))) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    rintro w ⟨z, hz, rfl⟩ ⟨z', hz', he⟩
    have heq : z' = z := hRi (hsub hz'.2) (hsub hz.2) he
    exact Set.disjoint_left.mp (Q.disjoint hkl) hz.1 (heq ▸ hz'.1)
  have hm : ∀ k : Fin Q.count, MeasurableSet (R '' (Q.cell k ∩ L)) := by
    intro k
    exact D.haar.measurable_cell_label_image hcomplete i ((Q.measurable_cell k).inter hL)
      (fun _ hz ↦ hsub hz.2)
  have hcover : (⋃ k : Fin Q.count, R '' (Q.cell k ∩ L)) = R '' L := by
    ext w
    constructor
    · intro hw
      obtain ⟨k, hk⟩ := mem_iUnion.mp hw
      rcases hk with ⟨z, hz, rfl⟩
      exact ⟨z, hz.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨k, hk⟩ := mem_iUnion.mp (Q.union_eq.symm ▸ hsub hz)
      exact mem_iUnion.mpr ⟨k, z, ⟨hk, hz⟩, rfl⟩
  have hh := measure_iUnion (μ := κ C.seedIndex) hd hm
  rw [hcover, tsum_fintype] at hh
  exact hh.symm

/-- The freezing error is bounded by the actual local Haar mass, independently
of the number of original reference clocks in the finite partition. -/
theorem original_partition_variation_error_le
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (i : Fin D.haar.continuous.count)
    (T : (D.haar.continuous.coefficient i).TaylorRootCover 1)
    (Q : FiniteRootNeighborhoodPartition (D.haar.continuous.coefficient i).roots
      T.centers T.neighborhood)
    {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    {tolerance : ℝ} (htolerance : 0 ≤ tolerance) :
    (∑ k : Fin Q.count,
      ENNReal.ofReal (2 * tolerance * D.rootIntensity i (Q.center k)) *
        (κ (D.haar.continuous.coefficient i).seedIndex)
          (populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a ''
            (Q.cell k ∩ L))) ≤
      ENNReal.ofReal (2 * tolerance * (D.haar.intensity i).upper) *
        (κ (D.haar.continuous.coefficient i).seedIndex)
          (populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a '' L) := by
  have hbound (k : Fin Q.count) : D.rootIntensity i (Q.center k) ≤ (D.haar.intensity i).upper := by
    apply ((D.haar.intensity i).bounds _ ?_).2
    apply mem_image_of_mem
    rw [D.haar.intensity_roots]
    exact T.subset (Q.center_mem k)
  calc
    _ ≤ ∑ k : Fin Q.count,
        ENNReal.ofReal (2 * tolerance * (D.haar.intensity i).upper) *
          (κ (D.haar.continuous.coefficient i).seedIndex)
            (populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a ''
              (Q.cell k ∩ L)) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (hbound k) (mul_nonneg (by norm_num) htolerance))) _
    _ = _ := by
      rw [← Finset.mul_sum, D.sum_original_partition_cell_haar hcomplete i T Q hL hsub]

/-- The original density continuity supplies finite absolutely continuous clock
references and simultaneous source bounds for every measurable portion of the
same retained core. The partition introduces no further population loss. -/
theorem exists_original_source_partition_observation_bound
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ T : (D.haar.continuous.coefficient i).TaylorRootCover 1,
    ∃ Q : FiniteRootNeighborhoodPartition (D.haar.continuous.coefficient i).roots
      T.centers T.neighborhood,
      (∀ k : Fin Q.count, condDistrib u a η₀ (Q.center k) ≪ (volume : Measure ℝ)) ∧
      ∀ (L : Set (ℚ → M)) (_hL : MeasurableSet L)
        (_hsub : L ⊆ (D.haar.continuous.coefficient i).roots),
      ∀ {X : Type*} [MeasurableSpace X]
        (obs : (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker × ℝ → X),
        Measurable obs → ∀ s : Set X, MeasurableSet s →
        ((η₀.restrict (a ⁻¹' L)).map (fun x ↦ obs (D.haar.sceneCoordinate i x))) s ≤
          (∑ k : Fin Q.count,
            (((D.rootIntensity i (Q.center k)).toNNReal •
              ((κ (D.haar.continuous.coefficient i).seedIndex).restrict
                (populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a ''
                  (Q.cell k ∩ L))).prod (condDistrib u a η₀ (Q.center k))).map obs) s) +
          ENNReal.ofReal (2 * tolerance * (D.haar.intensity i).upper) *
            (κ (D.haar.continuous.coefficient i).seedIndex)
              (populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a '' L) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  obtain ⟨T, hclock, hbound⟩ :=
    D.exists_original_source_cell_observation_cover hF hcomplete hu ha hinj i htolerance
  obtain ⟨Q⟩ := T.nonempty_partition
  refine ⟨T, Q, fun k ↦ hclock _ (Q.center_mem k), ?_⟩
  intro L hL hsub X _ obs hobs s hs
  rw [D.original_source_partition_observation_eq_sum hF hcomplete hu ha hinj i T Q
    hL hsub obs hobs s hs]
  have hb := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) ↦
    hbound (Q.center k) (Q.center_mem k) (Q.cell k ∩ L)
      ((Q.measurable_cell k).inter hL)
      (fun z hz ↦ Q.cell_subset k hz.1) obs hobs s hs
  have hh := add_le_add (le_refl (∑ k : Fin Q.count,
      (((D.rootIntensity i (Q.center k)).toNNReal •
        ((κ (D.haar.continuous.coefficient i).seedIndex).restrict
          (populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a ''
            (Q.cell k ∩ L))).prod (condDistrib u a η₀ (Q.center k))).map obs) s))
    (D.original_partition_variation_error_le hcomplete i T Q hL hsub htolerance.le)
  simp only [Finset.sum_add_distrib] at hb
  exact hb.trans hh
end PopulationLocalPressureCore
end OTSelector.Reconstruction
