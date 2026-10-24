import OTSelector.Reconstruction.FinslerConcreteUpperMicrocellShapeLaw

/-! Literal original Haar microcell count intensities, with no shape regularity
and no positivity condition on individual retained microcells. -/
open Set Function MeasureTheory ProbabilityTheory BoxIntegral
open scoped ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {q : ℕ}

/-- The exact original mass in a literal half-open microbox is its original
full-box mass times its canonical normalized shape mass, including null cells. -/
theorem original_microcell_mass_eq
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    (n : ℕ) [NeZero n] (ν : Fin q → ℤ) {s : Set E} (hs : MeasurableSet s) :
    μ (s ∩ e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))) =
      μ (affineHaarCube e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹) *
        (cubeMeasure (Fin q) 1) (originalMicrocellShape e n ν s) := by
  let origin : Fin q → ℝ := fun l ↦ (ν l : ℝ) / n
  let side : ℝ≥0 := (n : ℝ≥0)⁻¹
  have hside : 0 < side := inv_pos.mpr (by exact_mod_cast n.pos_of_neZero)
  let B := affineHaarCube e origin side
  have hB : MeasurableSet B := measurableSet_affineHaarCube e origin side
  have hS : MeasurableSet (originalMicrocellShape e n ν s) :=
    measurableSet_affineHaarCubeCoord_image e origin hside (hs.inter hB)
  have hshape : affineHaarShape e origin side (originalMicrocellShape e n ν s) = s ∩ B :=
    affineHaarShape_image_eq e origin hside inter_subset_right
  have hae : (s ∩ e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ)) : Set E) =ᵐ[μ] (s ∩ B : Set E) := by
    filter_upwards [unitPartitionBox_ae_eq_affineHaarCube μ e n ν] with x hx
    exact congrArg (fun p : Prop ↦ x ∈ s ∧ p) hx
  calc
    _ = μ (s ∩ B) := measure_congr hae
    _ = _ := by simpa only [hshape] using affineHaarShape_mass_eq μ e origin hside hS

/-- One actual original Haar Jacobian determines every original retained
microcell intensity. The literal fixed class mass multiplies it exactly. -/
theorem exists_original_microcell_class_intensities
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ)) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (classMass : ℝ≥0) (s : Set E), MeasurableSet s →
      ∀ (n : ℕ) [NeZero n] (ν : Fin q → ℤ),
      μ (s ∩ e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))) * (classMass : ℝ≥0∞) =
        (((c * classMass) * ((n : ℝ≥0)⁻¹) ^ q : ℝ≥0) : ℝ≥0∞) *
          (cubeMeasure (Fin q) 1) (originalMicrocellShape e n ν s) := by
  obtain ⟨c, hc, hcube⟩ := exists_original_affineHaarCube_laws μ e
  refine ⟨c, hc, fun classMass s hs n _ ν ↦ ?_⟩
  rw [original_microcell_mass_eq μ e n ν hs,
    (hcube (fun l ↦ (ν l : ℝ) / n) _
      (inv_pos.mpr (by exact_mod_cast n.pos_of_neZero))).1]
  simp only [ENNReal.coe_mul]
  ring

/-- The same identity in real mass units, retaining the original class mass
and original Haar coordinate factor before any finite-sample count is drawn. -/
theorem exists_original_microcell_real_class_intensities
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ)) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (classMass : ℝ≥0) (s : Set E), MeasurableSet s →
      ∀ (n : ℕ) [NeZero n] (ν : Fin q → ℤ),
      (μ (s ∩ e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ)))).toReal * (classMass : ℝ) =
        (c : ℝ) * classMass * ((n : ℝ)⁻¹) ^ q *
          ((cubeMeasure (Fin q) 1) (originalMicrocellShape e n ν s)).toReal := by
  obtain ⟨c, hc, hmass⟩ := exists_original_microcell_class_intensities μ e
  refine ⟨c, hc, fun classMass s hs n _ ν ↦ ?_⟩
  have h := congrArg ENNReal.toReal (hmass classMass s hs n ν)
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_mul, NNReal.coe_pow,
    NNReal.coe_inv, NNReal.coe_natCast] using h

/-- The full-box and all retained subcell count masses use one and the same
actual Haar Jacobian, chosen before the class weights and measurable cells. -/
theorem exists_original_microcell_intensity_laws
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ)) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (n : ℕ) [NeZero n] (ν : Fin q → ℤ),
      μ (e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))) =
        ((c * ((n : ℝ≥0)⁻¹) ^ q : ℝ≥0) : ℝ≥0∞) ∧
      ∀ (classMass : ℝ≥0) (s : Set E), MeasurableSet s →
        μ (s ∩ e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))) * (classMass : ℝ≥0∞) =
          (((c * classMass) * ((n : ℝ≥0)⁻¹) ^ q : ℝ≥0) : ℝ≥0∞) *
            (cubeMeasure (Fin q) 1) (originalMicrocellShape e n ν s) := by
  obtain ⟨c, hc, hcube⟩ := exists_original_affineHaarCube_laws μ e
  refine ⟨c, hc, fun n _ ν ↦ ?_⟩
  have hbox := (hcube (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹
    (inv_pos.mpr (by exact_mod_cast n.pos_of_neZero))).1
  refine ⟨(unitPartitionBox_haar_mass_eq μ e n ν).trans hbox, ?_⟩
  intro classMass s hs
  rw [original_microcell_mass_eq μ e n ν hs, hbox]
  simp only [ENNReal.coe_mul]
  ring

end OTSelector.Reconstruction
