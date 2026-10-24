import OTSelector.Probability.HaarAffineCube
import OTSelector.Probability.FiniteMeasureConditioning
import OTSelector.Probability.PoissonRestriction

/-! Original Haar cells of arbitrary measurable shape inside affine microboxes.
Their masses remain physical, while normalized point laws use the unit shape. -/
open Set Function MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open scoped ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Probability
open OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {q : ℕ}

/-- Keep the actual original seed points in a measurable shape of one affine
microbox. No interior or boundary regularity is required of the shape. -/
def affineHaarShape (e : E ≃L[ℝ] (Fin q → ℝ))
    (origin : Fin q → ℝ) (side : ℝ≥0) (S : Set (Fin q → ℝ)) : Set E :=
  affineHaarCube e origin side ∩ affineHaarCubeCoord e origin side ⁻¹' S

theorem measurableSet_affineHaarShape (e : E ≃L[ℝ] (Fin q → ℝ))
    (origin : Fin q → ℝ) (side : ℝ≥0) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S) :
    MeasurableSet (affineHaarShape e origin side S) :=
  (measurableSet_affineHaarCube e origin side).inter
    (hS.preimage (measurable_affineHaarCubeCoord e origin side))

/-- One Jacobian from the actual Haar measure gives every measurable-cell
mass, retaining the original spatial shape mass in the Poisson intensity. -/
theorem exists_original_affineHaarShape_masses (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : E ≃L[ℝ] (Fin q → ℝ)) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (origin : Fin q → ℝ) (side : ℝ≥0), 0 < side →
      ∀ S : Set (Fin q → ℝ), MeasurableSet S →
      μ (affineHaarShape e origin side S) =
        ((c * side ^ q : ℝ≥0) : ℝ≥0∞) * (cubeMeasure (Fin q) 1) S := by
  let _inst : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  let c := addHaarScalarFactor (μ.map e) (volume : Measure (Fin q → ℝ))
  have hc : 0 < c := addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hmap : μ.map e = c • (volume : Measure (Fin q → ℝ)) :=
    isAddLeftInvariant_eq_smul _ _
  refine ⟨c, hc, fun origin side hside S hS ↦ ?_⟩
  have hf := measurable_affineHaarCubeCoord e origin side
  have hraw : (μ.restrict (affineHaarCube e origin side)).map
      (affineHaarCubeCoord e origin side) = (c * side ^ q) • cubeMeasure (Fin q) 1 := by
    rw [affineHaarCube, ← Measure.restrict_map hf (measurableSet_seedUnitCube q),
      map_affineHaarCubeCoord μ e hmap origin hside, Measure.restrict_smul,
      ← cubeMeasure_eq_volume_restrict_seedUnitCube]
  calc
    _ = (μ.restrict (affineHaarCube e origin side))
        (affineHaarCubeCoord e origin side ⁻¹' S) := by
      rw [Measure.restrict_apply (hS.preimage hf)]
      exact congrArg μ (inter_comm _ _)
    _ = ((μ.restrict (affineHaarCube e origin side)).map
        (affineHaarCubeCoord e origin side)) S := (Measure.map_apply hf hS).symm
    _ = _ := by rw [hraw, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

/-- The actual normalized Haar shape law transforms into the original
conditional unit-cube law. Null shapes are included as zero measures. -/
theorem normalized_affineHaarShape_law (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : E ≃L[ℝ] (Fin q → ℝ)) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S) :
    (normalizedFiniteLaw (μ.restrict (affineHaarShape e origin side S))).map
      (affineHaarCubeCoord e origin side) = ProbabilityTheory.cond (cubeMeasure (Fin q) 1) S := by
  obtain ⟨c, hc, hcube⟩ := exists_original_affineHaarCube_laws μ e
  have hmass := (hcube origin side hside).1
  have hpoint := (hcube origin side hside).2
  have hfin : μ (affineHaarCube e origin side) ≠ ∞ := by rw [hmass]; exact ENNReal.coe_ne_top
  have hshapeFin : μ (affineHaarShape e origin side S) ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono inter_subset_left) hfin.lt_top).ne
  have hf := measurable_affineHaarCubeCoord e origin side
  have hcond : normalizedFiniteLaw (μ.restrict (affineHaarShape e origin side S)) =
      ProbabilityTheory.cond (normalizedFiniteLaw (μ.restrict (affineHaarCube e origin side)))
        (affineHaarCubeCoord e origin side ⁻¹' S) := by
    rw [normalizedFiniteLaw_restrict_eq_cond μ _ hshapeFin,
      normalizedFiniteLaw_restrict_eq_cond μ _ hfin,
      cond_cond_eq_cond_inter' (measurableSet_affineHaarCube e origin side)
        (hS.preimage hf) hfin]
    rfl
  rw [hcond, map_cond_preimage _ hf hS, hpoint]

/-- Positive original shape laws are the same probability restrictions used
by the original finite-prefix cloud construction. -/
theorem normalized_affineHaarShape_law_of_pos (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : E ≃L[ℝ] (Fin q → ℝ)) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S)
    (hpos : (cubeMeasure (Fin q) 1) S ≠ 0) :
    (normalizedFiniteLaw (μ.restrict (affineHaarShape e origin side S))).map
      (affineHaarCubeCoord e origin side) = restrictedPointLaw (cubeMeasure (Fin q) 1) S := by
  simpa only [restrictedPointLaw, ite_eq_right hpos] using
    normalized_affineHaarShape_law μ e origin hside hS

end OTSelector.Probability
