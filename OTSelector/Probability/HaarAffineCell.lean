import OTSelector.Probability.HaarAffineCloudLaw

/-! The actual original measurable cell, rather than a prespecified model shape,
produces its exact normalized affine shape and finite observation law. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Probability
open OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace A] {q : ℕ}

/-- The actual inverse of normalized microbox coordinates is the original
basis coordinate map composed with translation and positive dilation. -/
def affineHaarCubeHomeomorph (e : E ≃L[ℝ] (Fin q → ℝ))
    (origin : Fin q → ℝ) (side : ℝ≥0) (hside : 0 < side) : E ≃ₜ (Fin q → ℝ) where
  toFun := affineHaarCubeCoord e origin side
  invFun := fun x ↦ e.symm (origin + (side : ℝ) • x)
  left_inv := by
    intro x
    apply e.injective
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    funext l
    change origin l + (side : ℝ) * ((side : ℝ)⁻¹ * (e x l - origin l)) = e x l
    rw [← mul_assoc, mul_inv_cancel₀ (show (side : ℝ) ≠ 0 by exact_mod_cast hside.ne'), one_mul]
    ring
  right_inv := by
    intro x
    funext l
    change (side : ℝ)⁻¹ * (e (e.symm (origin + (side : ℝ) • x)) l - origin l) = x l
    rw [ContinuousLinearEquiv.apply_symm_apply]
    change (side : ℝ)⁻¹ * ((origin l + (side : ℝ) * x l) - origin l) = x l
    rw [add_sub_cancel_left, ← mul_assoc,
      inv_mul_cancel₀ (show (side : ℝ) ≠ 0 by exact_mod_cast hside.ne'), one_mul]
  continuous_toFun := by unfold affineHaarCubeCoord; fun_prop
  continuous_invFun := by fun_prop

/-- An arbitrary original measurable cell has a measurable normalized image. -/
theorem measurableSet_affineHaarCubeCoord_image (e : E ≃L[ℝ] (Fin q → ℝ))
    (origin : Fin q → ℝ) {side : ℝ≥0} (hside : 0 < side)
    {K : Set E} (hK : MeasurableSet K) :
    MeasurableSet (affineHaarCubeCoord e origin side '' K) :=
  (affineHaarCubeHomeomorph e origin side hside).measurableEmbedding.measurableSet_image.mpr hK

/-- No shape hypothesis is added to an original cell: its normalized image
represents exactly the same original points in the affine microbox. -/
theorem affineHaarShape_image_eq (e : E ≃L[ℝ] (Fin q → ℝ))
    (origin : Fin q → ℝ) {side : ℝ≥0} (hside : 0 < side)
    {K : Set E} (hK : K ⊆ affineHaarCube e origin side) :
    affineHaarShape e origin side (affineHaarCubeCoord e origin side '' K) = K := by
  unfold affineHaarShape
  have hi : Injective (affineHaarCubeCoord e origin side) :=
    (affineHaarCubeHomeomorph e origin side hside).injective
  rw [hi.preimage_image]
  exact inter_eq_right.mpr hK

/-- A positive original Haar cell produces a positive normalized shape, keeping
its actual original Haar mass rather than imposing full-cube domination. -/
theorem affineHaarCubeCoord_image_pos (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : E ≃L[ℝ] (Fin q → ℝ)) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side) {K : Set E} (hK : MeasurableSet K)
    (hsub : K ⊆ affineHaarCube e origin side) (hmass : μ K ≠ 0) :
    (cubeMeasure (Fin q) 1) (affineHaarCubeCoord e origin side '' K) ≠ 0 := by
  intro hz
  have hm := affineHaarShape_mass_eq μ e origin hside
    (measurableSet_affineHaarCubeCoord_image e origin hside hK)
  rw [affineHaarShape_image_eq e origin hside hsub, hz, mul_zero] at hm
  exact hmass hm

/-- The actual original positive Haar cell has a normalized probability law. -/
theorem normalized_original_affineHaarCell_probability (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : E ≃L[ℝ] (Fin q → ℝ)) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side) {K : Set E} (hK : MeasurableSet K)
    (hsub : K ⊆ affineHaarCube e origin side) (hmass : μ K ≠ 0) :
    IsProbabilityMeasure (normalizedFiniteLaw (μ.restrict K)) := by
  have hi := normalized_affineHaarShape_probability μ e origin hside
    (measurableSet_affineHaarCubeCoord_image e origin hside hK)
    (affineHaarCubeCoord_image_pos μ e origin hside hK hsub hmass)
  simpa only [affineHaarShape_image_eq e origin hside hsub] using hi

/-- The exact original positive cell supplies its own normalized shape law and
its original Poisson intensity. Marks and the count are transported literally. -/
theorem original_affineHaarCell_poisson_blockDataLaw_map
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ)) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side) {K : Set E} (hK : MeasurableSet K)
    (hsub : K ⊆ affineHaarCube e origin side) (hmass : μ K ≠ 0)
    (α : Measure A) [IsProbabilityMeasure α] (ambient markMass : ℝ≥0) :
    let _inst := normalized_original_affineHaarCell_probability μ e origin hside hK hsub hmass
    (blockDataLaw ((normalizedFiniteLaw (μ.restrict K)).prod α)
      (fun n ↦ poissonMeasure (ambient * (μ K).toNNReal * markMass) {n})).map
      (mapBlockData (Prod.map (affineHaarCubeCoord e origin side) id)) =
      shapeBlockLaw q α (ambient * (μ (affineHaarCube e origin side)).toNNReal * markMass)
        (affineHaarCubeCoord e origin side '' K) := by
  have h := affineHaarShape_poisson_blockDataLaw_map μ e origin hside
    (measurableSet_affineHaarCubeCoord_image e origin hside hK)
    (affineHaarCubeCoord_image_pos μ e origin hside hK hsub hmass) α ambient markMass
  simpa only [affineHaarShape_image_eq e origin hside hsub] using h

end OTSelector.Probability
