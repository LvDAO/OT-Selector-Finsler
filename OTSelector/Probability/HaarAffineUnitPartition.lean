import OTSelector.Probability.HaarAffineCellAE
import Mathlib.Analysis.BoxIntegral.UnitPartition

/-! Exact original Haar cell laws in the literal half-open uniform grid. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Probability
open OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace A] {q : ℕ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Exact normalized coordinates in a literal uniform partition box. -/
theorem affineHaarCubeCoord_unitPartition_apply
    (e : E ≃L[ℝ] (Fin q → ℝ)) (n : ℕ) [NeZero n] (ν : Fin q → ℤ)
    (x : E) (l : Fin q) :
    affineHaarCubeCoord e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹ x l =
      (n : ℝ) * e x l - (ν l : ℝ) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  simp only [affineHaarCubeCoord, NNReal.coe_inv, NNReal.coe_natCast, inv_inv]
  field_simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The literal half-open boxes of mathlib's uniform partition fit the closed
affine microbox with their original corner and side length. -/
theorem unitPartitionBox_subset_closed_affineHaarCubeCoord
    (e : E ≃L[ℝ] (Fin q → ℝ)) (n : ℕ) [NeZero n] (ν : Fin q → ℤ) :
    e ⁻¹' ((BoxIntegral.unitPartition.box n ν) : Set (Fin q → ℝ)) ⊆
      affineHaarCubeCoord e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹ ⁻¹'
        Icc (0 : Fin q → ℝ) 1 := by
  intro x hx
  have hx' := BoxIntegral.unitPartition.mem_box_iff'.mp hx
  constructor
  · intro l
    rw [affineHaarCubeCoord_unitPartition_apply]
    exact sub_nonneg.mpr (hx' l).1.le
  · intro l
    rw [affineHaarCubeCoord_unitPartition_apply]
    change (n : ℝ) * e x l - (ν l : ℝ) ≤ (1 : ℝ)
    linarith [(hx' l).2]

/-- A measurable original cell inside an actual half-open partition box loses
no point mass when normalized into the open unit cube. -/
theorem ae_mem_affineHaarCube_of_unitPartitionBox
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    (n : ℕ) [NeZero n] (ν : Fin q → ℤ) {K : Set E} (hK : MeasurableSet K)
    (hsub : K ⊆ e ⁻¹' ((BoxIntegral.unitPartition.box n ν) : Set (Fin q → ℝ))) :
    ∀ᵐ x ∂μ.restrict K,
      x ∈ affineHaarCube e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹ := by
  have hn : 0 < (n : ℝ≥0)⁻¹ := inv_pos.mpr (by exact_mod_cast n.pos_of_neZero)
  exact ae_mem_affineHaarCube_of_subset_closed μ e _ hn hK
    (hsub.trans (unitPartitionBox_subset_closed_affineHaarCubeCoord e n ν))

/-- Normalizing a positive original cell in a half-open partition box gives its
actual probability law. -/
theorem normalized_original_unitPartitionCell_probability
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    (n : ℕ) [NeZero n] (ν : Fin q → ℤ) {K : Set E} (hK : MeasurableSet K)
    (hsub : K ⊆ e ⁻¹' ((BoxIntegral.unitPartition.box n ν) : Set (Fin q → ℝ)))
    (hmass : μ K ≠ 0) : IsProbabilityMeasure (normalizedFiniteLaw (μ.restrict K)) := by
  exact normalized_original_affineHaarCell_probability_of_ae μ e _
    (inv_pos.mpr (by exact_mod_cast n.pos_of_neZero)) hK
    (ae_mem_affineHaarCube_of_unitPartitionBox μ e n ν hK hsub) hmass

/-- The actual original cell in a half-open grid box produces the precise
normalized finite-cloud law with no boundary or interior premise. -/
theorem original_unitPartitionCell_blockDataLaw_map
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    (n : ℕ) [NeZero n] (ν : Fin q → ℤ) {K : Set E} (hK : MeasurableSet K)
    (hsub : K ⊆ e ⁻¹' ((BoxIntegral.unitPartition.box n ν) : Set (Fin q → ℝ)))
    (hmass : μ K ≠ 0) (α : Measure A) [IsProbabilityMeasure α] (prob : ℕ → ℝ≥0∞) :
    let _inst := normalized_original_unitPartitionCell_probability μ e n ν hK hsub hmass
    ∃ S : Set (Fin q → ℝ), MeasurableSet S ∧ S ⊆ seedUnitCube q ∧
      (cubeMeasure (Fin q) 1) S ≠ 0 ∧
      μ K = μ (affineHaarCube e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹) *
        (cubeMeasure (Fin q) 1) S ∧
      (blockDataLaw ((normalizedFiniteLaw (μ.restrict K)).prod α) prob).map
        (mapBlockData (Prod.map
          (affineHaarCubeCoord e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹) id)) =
          blockDataLaw ((restrictedPointLaw (cubeMeasure (Fin q) 1) S).prod α) prob := by
  dsimp only
  exact original_affineHaarCell_blockDataLaw_map_of_ae μ e _
    (inv_pos.mpr (by exact_mod_cast n.pos_of_neZero)) hK
    (ae_mem_affineHaarCube_of_unitPartitionBox μ e n ν hK hsub) hmass α prob

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The open affine box lies inside its literal half-open partition box. -/
theorem affineHaarCube_subset_unitPartitionBox
    (e : E ≃L[ℝ] (Fin q → ℝ)) (n : ℕ) [NeZero n] (ν : Fin q → ℤ) :
    affineHaarCube e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹ ⊆
      e ⁻¹' ((BoxIntegral.unitPartition.box n ν) : Set (Fin q → ℝ)) := by
  intro x hx
  apply BoxIntegral.unitPartition.mem_box_iff'.mpr
  intro l
  have hl : 0 < affineHaarCubeCoord e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹ x l ∧
      affineHaarCubeCoord e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹ x l < 1 :=
    hx l (mem_univ l)
  rw [affineHaarCubeCoord_unitPartition_apply] at hl
  constructor <;> linarith [hl.1, hl.2]

/-- The literal half-open grid box and its open affine box agree almost
everywhere under the actual original Haar measure. -/
theorem unitPartitionBox_ae_eq_affineHaarCube
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    (n : ℕ) [NeZero n] (ν : Fin q → ℤ) :
    e ⁻¹' ((BoxIntegral.unitPartition.box n ν) : Set (Fin q → ℝ)) =ᵐ[μ]
      affineHaarCube e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹ := by
  have hn : 0 < (n : ℝ≥0)⁻¹ := inv_pos.mpr (by exact_mod_cast n.pos_of_neZero)
  filter_upwards [affineHaarCube_ae_eq_closed μ e (fun l ↦ (ν l : ℝ) / n) hn] with x hx
  apply propext
  exact ⟨fun h ↦ hx.mpr (unitPartitionBox_subset_closed_affineHaarCubeCoord e n ν h),
    fun h ↦ affineHaarCube_subset_unitPartitionBox e n ν h⟩

/-- Replacing the coordinate faces does not change any original restricted
point law, before normalization or point-cloud sampling. -/
theorem unitPartitionBox_restrict_eq_affineHaarCube
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    (n : ℕ) [NeZero n] (ν : Fin q → ℤ) :
    μ.restrict (e ⁻¹' ((BoxIntegral.unitPartition.box n ν) : Set (Fin q → ℝ))) =
      μ.restrict (affineHaarCube e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹) :=
  Measure.restrict_congr_set (unitPartitionBox_ae_eq_affineHaarCube μ e n ν)

/-- The actual original count mass of a literal partition box is the same as
the mass in the affine pressure normalization. -/
theorem unitPartitionBox_haar_mass_eq
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    (n : ℕ) [NeZero n] (ν : Fin q → ℤ) :
    μ (e ⁻¹' ((BoxIntegral.unitPartition.box n ν) : Set (Fin q → ℝ))) =
      μ (affineHaarCube e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹) :=
  measure_congr (unitPartitionBox_ae_eq_affineHaarCube μ e n ν)

/-- One actual Haar Jacobian supplies every literal grid-box mass and its
normalized uniform point law, with the original side length. -/
theorem exists_original_unitPartition_box_laws
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    (n : ℕ) [NeZero n] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ ν : Fin q → ℤ,
      μ (e ⁻¹' ((BoxIntegral.unitPartition.box n ν) : Set (Fin q → ℝ))) =
        ((c * ((n : ℝ≥0)⁻¹) ^ q : ℝ≥0) : ℝ≥0∞) ∧
      (normalizedFiniteLaw
        (μ.restrict (e ⁻¹' ((BoxIntegral.unitPartition.box n ν) : Set (Fin q → ℝ))))).map
          (affineHaarCubeCoord e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹) =
            cubeMeasure (Fin q) 1 := by
  obtain ⟨c, hc, hcube⟩ := exists_original_affineHaarCube_laws μ e
  refine ⟨c, hc, fun ν ↦ ?_⟩
  have h := hcube (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹
    (inv_pos.mpr (by exact_mod_cast n.pos_of_neZero))
  simpa only [unitPartitionBox_haar_mass_eq μ e n ν,
    unitPartitionBox_restrict_eq_affineHaarCube μ e n ν] using h

end OTSelector.Probability
