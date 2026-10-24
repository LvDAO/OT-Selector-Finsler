import OTSelector.Probability.HaarAffineCell

/-! Original Haar cells may meet the faces of their affine microbox. Null
coordinate faces do not change their original point law or count intensity. -/
open Set Function MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open scoped ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Probability
open OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace A] {q : ℕ}

/-- Removing an almost surely absent microbox boundary preserves the literal
original restricted measure. -/
theorem restrict_inter_eq_of_ae_mem {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {K B : Set X} (hB : MeasurableSet B)
    (hcarried : ∀ᵐ x ∂μ.restrict K, x ∈ B) :
    μ.restrict (K ∩ B) = μ.restrict K := by
  rw [inter_comm, ← Measure.restrict_restrict hB]
  exact Measure.restrict_eq_self_of_ae_mem hcarried

/-- All faces of a normalized affine microbox are null for the actual original
Haar measure, in every dimension. -/
theorem affineHaarCube_ae_eq_closed (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : E ≃L[ℝ] (Fin q → ℝ)) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side) :
    affineHaarCube e origin side =ᵐ[μ]
      affineHaarCubeCoord e origin side ⁻¹' Icc (0 : Fin q → ℝ) 1 := by
  let _inst : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  let c := addHaarScalarFactor (μ.map e) (volume : Measure (Fin q → ℝ))
  have hmap : μ.map e = c • (volume : Measure (Fin q → ℝ)) :=
    isAddLeftInvariant_eq_smul _ _
  have hv : seedUnitCube q =ᵐ[(volume : Measure (Fin q → ℝ))]
      Icc (0 : Fin q → ℝ) 1 := by
    rw [volume_pi]
    exact Measure.univ_pi_Ioo_ae_eq_Icc
  have hs := ae_smul_measure hv (c * side ^ q)
  rw [← map_affineHaarCubeCoord μ e hmap origin hside] at hs
  exact ae_of_ae_map (measurable_affineHaarCubeCoord e origin side).aemeasurable hs

/-- A cell in a closed or half-open microbox is carried almost surely by the
open microbox. This uses Haar nullity of faces, not an interior assumption on K. -/
theorem ae_mem_affineHaarCube_of_subset_closed (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : E ≃L[ℝ] (Fin q → ℝ)) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side) {K : Set E} (hK : MeasurableSet K)
    (hsub : K ⊆ affineHaarCubeCoord e origin side ⁻¹' Icc (0 : Fin q → ℝ) 1) :
    ∀ᵐ x ∂μ.restrict K, x ∈ affineHaarCube e origin side := by
  filter_upwards [ae_restrict_mem hK,
    ae_restrict_of_ae (affineHaarCube_ae_eq_closed μ e origin hside)] with x hx heq
  exact heq.mpr (hsub hx)

/-- Exact original conditional point laws are unaffected by removing faces. -/
theorem normalized_original_affineHaarCell_probability_of_ae
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ)) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side) {K : Set E} (hK : MeasurableSet K)
    (hcarried : ∀ᵐ x ∂μ.restrict K, x ∈ affineHaarCube e origin side) (hmass : μ K ≠ 0) :
    IsProbabilityMeasure (normalizedFiniteLaw (μ.restrict K)) := by
  have hB := measurableSet_affineHaarCube e origin side
  have hr := restrict_inter_eq_of_ae_mem μ hB hcarried
  have hm : μ (K ∩ affineHaarCube e origin side) = μ K := by
    simpa only [Measure.restrict_apply_univ] using
      congrArg (fun ν : Measure E ↦ ν univ) hr
  have hp := normalized_original_affineHaarCell_probability μ e origin hside
    (hK.inter hB) inter_subset_right (by rw [hm]; exact hmass)
  simpa only [hr] using hp

/-- An original positive cell carried by a microbox supplies its exact shape
law at the unchanged original Poisson count, including boundary-touching cells. -/
theorem original_affineHaarCell_poisson_blockDataLaw_map_of_ae
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ)) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side) {K : Set E} (hK : MeasurableSet K)
    (hcarried : ∀ᵐ x ∂μ.restrict K, x ∈ affineHaarCube e origin side) (hmass : μ K ≠ 0)
    (α : Measure A) [IsProbabilityMeasure α] (ambient markMass : ℝ≥0) :
    let _inst := normalized_original_affineHaarCell_probability_of_ae μ e origin hside
      hK hcarried hmass
    (blockDataLaw ((normalizedFiniteLaw (μ.restrict K)).prod α)
      (fun n ↦ poissonMeasure (ambient * (μ K).toNNReal * markMass) {n})).map
      (mapBlockData (Prod.map (affineHaarCubeCoord e origin side) id)) =
      shapeBlockLaw q α (ambient * (μ (affineHaarCube e origin side)).toNNReal * markMass)
        (affineHaarCubeCoord e origin side '' (K ∩ affineHaarCube e origin side)) := by
  have hB := measurableSet_affineHaarCube e origin side
  have hr := restrict_inter_eq_of_ae_mem μ hB hcarried
  have hm : μ (K ∩ affineHaarCube e origin side) = μ K := by
    simpa only [Measure.restrict_apply_univ] using
      congrArg (fun ν : Measure E ↦ ν univ) hr
  have h := original_affineHaarCell_poisson_blockDataLaw_map μ e origin hside
    (hK.inter hB) inter_subset_right (by rw [hm]; exact hmass) α ambient markMass
  simpa only [hr, hm] using h

/-- The original boundary-touching cell produces its own positive measurable
unit-cube shape, exact original mass, and exact conditional point law. -/
theorem exists_original_affineHaarCell_shape_of_ae
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ)) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side) {K : Set E} (hK : MeasurableSet K)
    (hcarried : ∀ᵐ x ∂μ.restrict K, x ∈ affineHaarCube e origin side) (hmass : μ K ≠ 0) :
    ∃ S : Set (Fin q → ℝ), MeasurableSet S ∧ S ⊆ seedUnitCube q ∧
      (cubeMeasure (Fin q) 1) S ≠ 0 ∧
      μ K = μ (affineHaarCube e origin side) * (cubeMeasure (Fin q) 1) S ∧
      (normalizedFiniteLaw (μ.restrict K)).map (affineHaarCubeCoord e origin side) =
        restrictedPointLaw (cubeMeasure (Fin q) 1) S := by
  have hB := measurableSet_affineHaarCube e origin side
  have hr := restrict_inter_eq_of_ae_mem μ hB hcarried
  have hm : μ (K ∩ affineHaarCube e origin side) = μ K := by
    simpa only [Measure.restrict_apply_univ] using
      congrArg (fun ν : Measure E ↦ ν univ) hr
  let S := affineHaarCubeCoord e origin side '' (K ∩ affineHaarCube e origin side)
  have hS : MeasurableSet S :=
    measurableSet_affineHaarCubeCoord_image e origin hside (hK.inter hB)
  have hpos : (cubeMeasure (Fin q) 1) S ≠ 0 :=
    affineHaarCubeCoord_image_pos μ e origin hside (hK.inter hB) inter_subset_right
      (by rw [hm]; exact hmass)
  have hshape : affineHaarShape e origin side S = K ∩ affineHaarCube e origin side :=
    affineHaarShape_image_eq e origin hside inter_subset_right
  refine ⟨S, hS, ?_, hpos, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  · simpa only [hshape, hm] using affineHaarShape_mass_eq μ e origin hside hS
  · simpa only [hshape, hr] using
      normalized_affineHaarShape_law_of_pos μ e origin hside hS hpos

/-- Arbitrary original count laws are kept literally, including fixed-sample
binomial cell counts. Boundary deletion acts only on the null point event. -/
theorem original_affineHaarCell_blockDataLaw_map_of_ae
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ)) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side) {K : Set E} (hK : MeasurableSet K)
    (hcarried : ∀ᵐ x ∂μ.restrict K, x ∈ affineHaarCube e origin side) (hmass : μ K ≠ 0)
    (α : Measure A) [IsProbabilityMeasure α] (prob : ℕ → ℝ≥0∞) :
    let _inst := normalized_original_affineHaarCell_probability_of_ae μ e origin hside
      hK hcarried hmass
    ∃ S : Set (Fin q → ℝ), MeasurableSet S ∧ S ⊆ seedUnitCube q ∧
      (cubeMeasure (Fin q) 1) S ≠ 0 ∧
      μ K = μ (affineHaarCube e origin side) * (cubeMeasure (Fin q) 1) S ∧
      (blockDataLaw ((normalizedFiniteLaw (μ.restrict K)).prod α) prob).map
        (mapBlockData (Prod.map (affineHaarCubeCoord e origin side) id)) =
          blockDataLaw ((restrictedPointLaw (cubeMeasure (Fin q) 1) S).prod α) prob := by
  dsimp only
  let _inst := normalized_original_affineHaarCell_probability_of_ae μ e origin hside
    hK hcarried hmass
  obtain ⟨S, hS, hsub, hpos, hmassS, hpoint⟩ :=
    exists_original_affineHaarCell_shape_of_ae μ e origin hside hK hcarried hmass
  refine ⟨S, hS, hsub, hpos, hmassS, ?_⟩
  apply blockDataLaw_mapPoints _ _
    ((measurable_affineHaarCubeCoord e origin side).prodMap measurable_id)
  rw [← Measure.map_prod_map _ _ (measurable_affineHaarCubeCoord e origin side) measurable_id,
    hpoint, Measure.map_id]

end OTSelector.Probability
