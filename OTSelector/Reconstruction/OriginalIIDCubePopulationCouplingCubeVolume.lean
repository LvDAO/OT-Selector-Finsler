import OTSelector.MeasureTheory.CubeBlockDecomposition
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootBoundary
import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-! The actual original unit-cube sampler maps to normalized restricted Haar
volume on the true centered cube, retaining the closed boundary convention. -/

open MeasureTheory Set
open OTSelector.Probability
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

private theorem map_uniformInterval_one_centered {R : ℝ} (hR : 0 < R) :
    (uniformInterval 1).map (fun x : ℝ ↦ 2 * R * x - R) =
      (ENNReal.ofReal (2 * R))⁻¹ • volume.restrict (Icc (-R) R) := by
  let A : ℝ → ℝ := fun x ↦ 2 * R * x - R
  have hscale : 0 < 2 * R := by positivity
  have hemb : MeasurableEmbedding A :=
    (MeasurableEquiv.addRight (-R)).measurableEmbedding.comp
      (measurableEmbedding_const_smul₀ hscale.ne')
  have hpre : A ⁻¹' Icc (-R) R = Icc 0 1 := by
    ext x
    simp only [mem_preimage, mem_Icc]
    constructor
    · rintro ⟨hl, hu⟩
      constructor
      · apply (mul_nonneg_iff_of_pos_left hscale).mp
        dsimp only [A] at hl
        linarith
      · apply (mul_le_mul_iff_left₀ hscale).mp
        dsimp only [A] at hu
        linarith
    · rintro ⟨hl, hu⟩
      have h0 := mul_nonneg hscale.le hl
      have h1 := mul_le_mul_of_nonneg_left hu hscale.le
      dsimp only [A]
      constructor <;> linarith
  have hmap : (volume : Measure ℝ).map A = (ENNReal.ofReal (2 * R))⁻¹ • volume := by
    have hadd : Measurable (fun x : ℝ ↦ x + (-R)) := measurable_id.add measurable_const
    have hmul : Measurable (fun x : ℝ ↦ 2 * R * x) := measurable_const_mul _
    change volume.map ((fun x : ℝ ↦ x + (-R)) ∘ (fun x ↦ 2 * R * x)) = _
    rw [← Measure.map_map hadd hmul,
      Real.map_volume_mul_left hscale.ne', Measure.map_smul, map_add_right_eq_self,
      abs_of_pos (inv_pos.mpr hscale), ENNReal.ofReal_inv_of_pos hscale]
  calc
    _ = (volume.restrict (Icc (0 : ℝ) 1)).map A := by
      rw [uniformInterval, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, inv_one,
        one_smul, restrict_Ioo_eq_restrict_Icc]
    _ = (volume.map A).restrict (Icc (-R) R) := by
      rw [← hpre]
      exact (hemb.restrict_map volume (Icc (-R) R)).symm
    _ = _ := by rw [hmap, Measure.restrict_smul]

/-- The actual affine image of the original uniform unit-cube law is exactly
the normalized volume restriction to the true centered closed cube. Product
and boundary-null identities include the zero-dimensional cube automatically. -/
theorem map_originalUnitCube_centered_eq_normalized_volume (q : ℕ)
    {R : ℝ} (hR : 0 < R) :
    (cubeMeasure (Fin q) 1).map (fun v i ↦ 2 * R * v i - R) =
      (volume (haarRootCube (Fin q) R))⁻¹ •
        volume.restrict (haarRootCube (Fin q) R) := by
  have hscale : 0 < 2 * R := by positivity
  have hm : Measurable (fun x : ℝ ↦ 2 * R * x - R) :=
    (measurable_const_mul _).sub measurable_const
  have : IsProbabilityMeasure (uniformInterval 1) := isProbabilityMeasure_uniformInterval zero_lt_one
  have : ∀ _ : Fin q, IsProbabilityMeasure
      ((uniformInterval 1).map (fun x : ℝ ↦ 2 * R * x - R)) := fun _ ↦
    Measure.isProbabilityMeasure_map hm.aemeasurable
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Icc (-R) R)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have : IsProbabilityMeasure
      ((ENNReal.ofReal (2 * R))⁻¹ • (volume : Measure ℝ).restrict (Icc (-R) R)) := by
    rw [← map_uniformInterval_one_centered hR]
    exact Measure.isProbabilityMeasure_map hm.aemeasurable
  have hpismul :
      (Measure.pi fun _ : Fin q ↦ (ENNReal.ofReal (2 * R))⁻¹ •
          (volume : Measure ℝ).restrict (Icc (-R) R)) =
        ((ENNReal.ofReal (2 * R))⁻¹ ^ q) •
          Measure.pi (fun _ : Fin q ↦ (volume : Measure ℝ).restrict (Icc (-R) R)) := by
    apply Measure.pi_eq
    intro s _
    rw [Measure.smul_apply, Measure.pi_pi]
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hset : (univ.pi fun _ : Fin q ↦ Icc (-R) R) = haarRootCube (Fin q) R :=
    pi_univ_Icc (fun _ ↦ -R) (fun _ ↦ R)
  change (Measure.pi (fun _ : Fin q ↦ uniformInterval 1)).map _ = _
  rw [Measure.pi_map_pi (f := fun _ (x : ℝ) ↦ 2 * R * x - R)
    (fun _ ↦ hm.aemeasurable)]
  simp_rw [map_uniformInterval_one_centered hR]
  rw [hpismul]
  rw [← Measure.restrict_pi_pi (fun _ : Fin q ↦ (volume : Measure ℝ))
    (fun _ : Fin q ↦ Icc (-R) R), ← volume_pi, hset]
  congr 1
  simp only [volume_haarRootCube (Fin q) hR.le, Fintype.card_fin,
    ENNReal.ofReal_pow hscale.le, ENNReal.inv_pow]

end OTSelector.Reconstruction
