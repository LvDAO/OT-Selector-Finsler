import OTSelector.Reconstruction.FinslerConcreteUpperMicrocellShape

/-! Exact linear-coordinate images of the original microcell shape. -/
open Set Function MeasureTheory ProbabilityTheory BoxIntegral
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {q : ℕ}

/-- The normalized shape of the literal original root cell agrees with the
shape constructed in its linear image. There is no replacement spatial law. -/
theorem originalMicrocellShape_linear_image
    (e : E ≃L[ℝ] (Fin q → ℝ)) (n : ℕ) (ν : Fin q → ℤ) (s : Set E) :
    originalMicrocellShape (ContinuousLinearEquiv.refl ℝ (Fin q → ℝ)) n ν (e '' s) =
      originalMicrocellShape e n ν s := by
  ext y
  constructor
  · rintro ⟨x, ⟨⟨z, hzs, rfl⟩, hzB⟩, hxy⟩
    exact ⟨z, ⟨hzs, hzB⟩, hxy⟩
  · rintro ⟨x, ⟨hxs, hxB⟩, hxy⟩
    exact ⟨e x, ⟨mem_image_of_mem e hxs, hxB⟩, hxy⟩

/-- Restricting the original cell to one literal partition box produces
precisely its canonical normalized shape, including Haar-null faces. -/
theorem originalMicrocellShape_inter_unitPartition
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    (n : ℕ) [NeZero n] (ν : Fin q → ℤ) (s : Set E) :
    originalMicrocellShape e n ν (s ∩ e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))) =
      originalMicrocellShape e n ν s := by
  unfold originalMicrocellShape
  congr 1
  have hsub := affineHaarCube_subset_unitPartitionBox e n ν
  ext x
  simp only [mem_inter_iff]
  exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, hsub h.2⟩, h.2⟩⟩

/-- The original positive half-open root subcell has its exact canonical shape
law, with any original count weights kept unchanged. -/
theorem original_microcell_blockDataLaw_map
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    (n : ℕ) [NeZero n] (ν : Fin q → ℤ) {s : Set E} (hs : MeasurableSet s)
    (hmass : μ (s ∩ e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))) ≠ 0)
    {A : Type*} [MeasurableSpace A] (α : Measure A) [IsProbabilityMeasure α]
    (prob : ℕ → ℝ≥0∞) :
    let K := s ∩ e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))
    let _inst := normalized_original_unitPartitionCell_probability μ e n ν
      (hs.inter ((unitPartition.box n ν).measurableSet_coe.preimage e.continuous.measurable))
      inter_subset_right hmass
    (blockDataLaw ((normalizedFiniteLaw (μ.restrict K)).prod α) prob).map
      (mapBlockData (Prod.map
        (affineHaarCubeCoord e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹) id)) =
        blockDataLaw ((restrictedPointLaw (cubeMeasure (Fin q) 1)
          (originalMicrocellShape e n ν s)).prod α) prob := by
  let K := s ∩ e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))
  have hK : MeasurableSet K :=
    hs.inter ((unitPartition.box n ν).measurableSet_coe.preimage e.continuous.measurable)
  have hcarried := ae_mem_affineHaarCube_of_unitPartitionBox μ e n ν hK inter_subset_right
  have hside : 0 < (n : ℝ≥0)⁻¹ := inv_pos.mpr (by exact_mod_cast n.pos_of_neZero)
  have hB := measurableSet_affineHaarCube e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹
  have hr := restrict_inter_eq_of_ae_mem μ hB hcarried
  have hm : μ (K ∩ affineHaarCube e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹) = μ K := by
    simpa only [Measure.restrict_apply_univ] using congrArg (fun ν : Measure E ↦ ν univ) hr
  have hpos := affineHaarCubeCoord_image_pos μ e _ hside (hK.inter hB)
    inter_subset_right (by rw [hm]; exact hmass)
  have hshape := affineHaarShape_image_eq e (fun l ↦ (ν l : ℝ) / n) hside
    (inter_subset_right : K ∩ affineHaarCube e _ _ ⊆ _)
  have hpoint := normalized_affineHaarShape_law_of_pos μ e (fun l ↦ (ν l : ℝ) / n) hside
    (measurableSet_affineHaarCubeCoord_image e (fun l ↦ (ν l : ℝ) / n) hside (hK.inter hB)) hpos
  rw [hshape, hr] at hpoint
  have hp : (normalizedFiniteLaw (μ.restrict K)).map
      (affineHaarCubeCoord e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹) =
      restrictedPointLaw (cubeMeasure (Fin q) 1) (originalMicrocellShape e n ν s) := by
    change _ = restrictedPointLaw (cubeMeasure (Fin q) 1) (originalMicrocellShape e n ν K) at hpoint
    rw [show K = s ∩ e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ)) from rfl,
      originalMicrocellShape_inter_unitPartition μ e n ν s] at hpoint
    exact hpoint
  letI := normalized_original_unitPartitionCell_probability μ e n ν hK inter_subset_right hmass
  dsimp only
  apply blockDataLaw_mapPoints _ _
    ((measurable_affineHaarCubeCoord e _ _).prodMap measurable_id)
  rw [← Measure.map_prod_map _ _ (measurable_affineHaarCubeCoord e _ _) measurable_id,
    hp, Measure.map_id]

end OTSelector.Reconstruction
