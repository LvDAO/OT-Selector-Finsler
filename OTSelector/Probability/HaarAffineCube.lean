import OTSelector.Probability.HaarCoordinateNormalization
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Actual affine cube laws and original Haar masses in any finite-dimensional
seed label space. The geometry is unchanged; these are coordinate identities. -/
open Set Function MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open scoped ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Probability
open OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {q : ℕ}

/-- Normalize an actual affine microbox in the original seed coordinates. -/
def affineHaarCubeCoord (e : E ≃L[ℝ] (Fin q → ℝ))
    (origin : Fin q → ℝ) (side : ℝ≥0) (x : E) : Fin q → ℝ :=
  fun l ↦ (side : ℝ)⁻¹ * (e x l - origin l)

theorem measurable_affineHaarCubeCoord (e : E ≃L[ℝ] (Fin q → ℝ))
    (origin : Fin q → ℝ) (side : ℝ≥0) :
    Measurable (affineHaarCubeCoord e origin side) := by
  unfold affineHaarCubeCoord
  fun_prop

/-- The actual seed-label set of a normalized affine cube. -/
def affineHaarCube (e : E ≃L[ℝ] (Fin q → ℝ))
    (origin : Fin q → ℝ) (side : ℝ≥0) : Set E :=
  affineHaarCubeCoord e origin side ⁻¹' seedUnitCube q

theorem measurableSet_affineHaarCube (e : E ≃L[ℝ] (Fin q → ℝ))
    (origin : Fin q → ℝ) (side : ℝ≥0) : MeasurableSet (affineHaarCube e origin side) :=
  (measurableSet_seedUnitCube q).preimage (measurable_affineHaarCubeCoord e origin side)

/-- Normalizing by a positive side length multiplies the pushed Haar density by
side^q. This is the same volume factor used by the physical quadratic cost. -/
theorem map_volume_inverse_smul_cube (q : ℕ) {side : ℝ≥0} (hside : 0 < side) :
    (volume : Measure (Fin q → ℝ)).map (fun z ↦ (side : ℝ)⁻¹ • z) =
      side ^ q • (volume : Measure (Fin q → ℝ)) := by
  have hs : 0 < (side : ℝ) := by exact_mod_cast hside
  rw [map_addHaar_smul volume (inv_ne_zero hs.ne')]
  simp only [Module.finrank_fin_fun, inv_pow, inv_inv,
    abs_of_nonneg (pow_nonneg side.coe_nonneg q), ENNReal.ofReal_pow side.coe_nonneg,
    ENNReal.ofReal_coe_nnreal]
  rfl

/-- Translation and normalization of the original Haar point law have the exact
original density and volume factor, with no population-density assumption. -/
theorem map_affineHaarCubeCoord (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : E ≃L[ℝ] (Fin q → ℝ)) {c : ℝ≥0}
    (hmap : μ.map e = c • (volume : Measure (Fin q → ℝ)))
    (origin : Fin q → ℝ) {side : ℝ≥0} (hside : 0 < side) :
    μ.map (affineHaarCubeCoord e origin side) =
      (c * side ^ q) • (volume : Measure (Fin q → ℝ)) := by
  let _inst : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have htrans : Measurable (fun z : Fin q → ℝ ↦ -origin + z) := by fun_prop
  have hscale : Measurable (fun z : Fin q → ℝ ↦ (side : ℝ)⁻¹ • z) := by fun_prop
  calc
    _ = ((μ.map e).map (fun z : Fin q → ℝ ↦ -origin + z)).map
        (fun z : Fin q → ℝ ↦ (side : ℝ)⁻¹ • z) := by
      rw [Measure.map_map hscale htrans,
        Measure.map_map (hscale.comp htrans) e.continuous.measurable]
      congr 1
      funext x l
      simp only [affineHaarCubeCoord, Function.comp_def, Pi.smul_apply, smul_eq_mul,
        Pi.add_apply, Pi.neg_apply]
      ring
    _ = (μ.map e).map (fun z : Fin q → ℝ ↦ (side : ℝ)⁻¹ • z) := by
      rw [IsAddLeftInvariant.map_add_left_eq_self]
    _ = _ := by
      rw [hmap, Measure.map_smul, map_volume_inverse_smul_cube q hside, smul_smul]

/-- One Haar Jacobian is produced from the actual original measure. All affine
microboxes then have their exact mass and normalized unit-cube point law. -/
theorem exists_original_affineHaarCube_laws (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : E ≃L[ℝ] (Fin q → ℝ)) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (origin : Fin q → ℝ) (side : ℝ≥0), 0 < side →
      μ (affineHaarCube e origin side) = ((c * side ^ q : ℝ≥0) : ℝ≥0∞) ∧
      (normalizedFiniteLaw (μ.restrict (affineHaarCube e origin side))).map
        (affineHaarCubeCoord e origin side) = cubeMeasure (Fin q) 1 := by
  let _inst : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  let c := addHaarScalarFactor (μ.map e) (volume : Measure (Fin q → ℝ))
  have hc : 0 < c := addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hmap : μ.map e = c • (volume : Measure (Fin q → ℝ)) :=
    isAddLeftInvariant_eq_smul _ _
  refine ⟨c, hc, fun origin side hside ↦ ?_⟩
  have hscaled := map_affineHaarCubeCoord μ e hmap origin hside
  have hcoord := measurable_affineHaarCubeCoord e origin side
  have hmass : μ (affineHaarCube e origin side) = ((c * side ^ q : ℝ≥0) : ℝ≥0∞) := by
    have hm := congrArg (fun ν : Measure (Fin q → ℝ) ↦ ν (seedUnitCube q)) hscaled
    rw [Measure.map_apply hcoord (measurableSet_seedUnitCube q),
      Measure.smul_apply, volume_seedUnitCube] at hm
    simpa only [affineHaarCube, ENNReal.smul_one] using hm
  exact ⟨hmass, normalized_haar_coordinate_preimage_cube q μ hcoord
    (mul_pos hc (pow_pos hside q)) hscaled⟩

end OTSelector.Probability
