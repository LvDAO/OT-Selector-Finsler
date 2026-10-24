import OTSelector.Probability.HaarAffineShape
import OTSelector.Probability.BlockDataTransport
import OTSelector.Probability.MarkedShapeLaw

/-! Exact original finite Haar-cell observations in affine microboxes: the
conditional point law changes coordinates, and the original count law is kept. -/
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

/-- Original Haar cell mass is actual full microbox mass times the normalized
spatial shape mass. In particular, a null shape has zero original intensity. -/
theorem affineHaarShape_mass_eq (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : E ≃L[ℝ] (Fin q → ℝ)) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S) :
    μ (affineHaarShape e origin side S) =
      μ (affineHaarCube e origin side) * (cubeMeasure (Fin q) 1) S := by
  let _instCube : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  obtain ⟨c, hc, hm⟩ := exists_original_affineHaarShape_masses μ e
  have hwhole := hm origin side hside univ MeasurableSet.univ
  simp only [affineHaarShape, preimage_univ, inter_univ, measure_univ, mul_one] at hwhole
  rw [hwhole]
  exact hm origin side hside S hS

/-- A positive original spatial shape has its actual normalized probability
law; positivity is checked in the normalized unit-cube shape. -/
theorem normalized_affineHaarShape_probability (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : E ≃L[ℝ] (Fin q → ℝ)) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S)
    (hpos : (cubeMeasure (Fin q) 1) S ≠ 0) :
    IsProbabilityMeasure (normalizedFiniteLaw (μ.restrict (affineHaarShape e origin side S))) := by
  let _instCube : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  let _instMap : IsProbabilityMeasure
      ((normalizedFiniteLaw (μ.restrict (affineHaarShape e origin side S))).map
        (affineHaarCubeCoord e origin side)) := by
    rw [normalized_affineHaarShape_law_of_pos μ e origin hside hS hpos]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map (affineHaarCubeCoord e origin side)

/-- Any original count distribution is kept literally when transporting all
used Haar-cell coordinates and the unchanged independent marks. -/
theorem affineHaarShape_blockDataLaw_map (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : E ≃L[ℝ] (Fin q → ℝ)) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S)
    (hpos : (cubeMeasure (Fin q) 1) S ≠ 0)
    (α : Measure A) [IsProbabilityMeasure α] (prob : ℕ → ℝ≥0∞) :
    let _instCube : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
      isProbabilityMeasure_cubeMeasure (by norm_num)
    let _instShape := normalized_affineHaarShape_probability μ e origin hside hS hpos
    (blockDataLaw ((normalizedFiniteLaw (μ.restrict (affineHaarShape e origin side S))).prod α)
      prob).map (mapBlockData (Prod.map (affineHaarCubeCoord e origin side) id)) =
        blockDataLaw ((restrictedPointLaw (cubeMeasure (Fin q) 1) S).prod α) prob := by
  dsimp only
  let _instCube : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  let _instShape := normalized_affineHaarShape_probability μ e origin hside hS hpos
  apply blockDataLaw_mapPoints _ _
    ((measurable_affineHaarCubeCoord e origin side).prodMap measurable_id)
  rw [← Measure.map_prod_map _ _ (measurable_affineHaarCubeCoord e origin side) measurable_id,
    normalized_affineHaarShape_law_of_pos μ e origin hside hS hpos, Measure.map_id]

/-- The physical cell intensity includes both the actual original Haar mass
and the total retained mark mass. Neither is normalized away. -/
theorem affineHaarShape_intensity_eq (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : E ≃L[ℝ] (Fin q → ℝ)) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S)
    (ambient markMass : ℝ≥0) :
    ambient * (μ (affineHaarShape e origin side S)).toNNReal * markMass =
      (ambient * (μ (affineHaarCube e origin side)).toNNReal * markMass) *
        restrictionWeight (cubeMeasure (Fin q) 1) S := by
  rw [affineHaarShape_mass_eq μ e origin hside hS, ENNReal.toNNReal_mul]
  unfold restrictionWeight
  ring

/-- Actual Poisson observations of an original positive Haar cell map to the
exact shape-prefix law used by legal-pressure recovery. The full microbox
intensity retains its original Haar and retained-class masses. -/
theorem affineHaarShape_poisson_blockDataLaw_map (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : E ≃L[ℝ] (Fin q → ℝ)) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S)
    (hpos : (cubeMeasure (Fin q) 1) S ≠ 0)
    (α : Measure A) [IsProbabilityMeasure α] (ambient markMass : ℝ≥0) :
    let _instShape := normalized_affineHaarShape_probability μ e origin hside hS hpos
    (blockDataLaw ((normalizedFiniteLaw (μ.restrict (affineHaarShape e origin side S))).prod α)
      (fun n ↦ poissonMeasure
        (ambient * (μ (affineHaarShape e origin side S)).toNNReal * markMass) {n})).map
      (mapBlockData (Prod.map (affineHaarCubeCoord e origin side) id)) =
      shapeBlockLaw q α (ambient * (μ (affineHaarCube e origin side)).toNNReal * markMass) S := by
  dsimp only
  let _instShape := normalized_affineHaarShape_probability μ e origin hside hS hpos
  rw [affineHaarShape_intensity_eq μ e origin hside hS ambient markMass]
  exact affineHaarShape_blockDataLaw_map μ e origin hside hS hpos α _

end OTSelector.Probability
