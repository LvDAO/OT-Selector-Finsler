import OTSelector.Analysis.Sobolev.CubeTraceFiniteRank
import OTSelector.Analysis.Sobolev.CubeCollarMeanBound

/-! Actual dyadic collar volumes and bounded finite-rank trace coefficients. -/
open Set Function Filter MeasureTheory BoxIntegral
open scoped ENNReal Topology BigOperators
noncomputable section
namespace OTSelector.Reconstruction

/-- Every actual dyadic collar has its true geometric volume, independent
of the cell; the normal thickness equals the original dyadic face side. -/
theorem originalDyadicTraceCollar_volume_real
    {q n : ℕ} (J : (originalDyadicFacePartition (ι := Fin q) n).boxes) :
    volume.real (J.1.Icc ×ˢ Icc (0 : ℝ) ((1 : ℝ) / 2^n)) =
      ((1 : ℝ) / 2^n) ^ (q + 1) := by
  rw [Measure.volume_eq_prod, measureReal_prod_prod]
  change (volume.real (Icc J.1.lower J.1.upper)) *
    (volume.real (Icc (0 : ℝ) ((1 : ℝ) / 2^n))) = _
  rw [measureReal_def, Real.volume_Icc_pi_toReal J.1.lower_le_upper,
    measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (by simp only [sub_zero]; positivity : 0 ≤ (1 : ℝ) / 2^n - 0)]
  simp_rw [originalDyadicFacePartition_side J.2]
  simp [pow_succ]

/-- The literal coefficients of the actual finite-rank trace approximation
are uniformly bounded on the smooth zero-mean unit-gradient family. -/
theorem originalDyadicTraceMeans_sq_le_of_mean_zero_unit_energy
    {q : ℕ} {f : (Fin q → ℝ) × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hmean : (∫ p in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1) ×ˢ Icc (0 : ℝ) 1,
      f p) = 0)
    (henergy : boxCollarGradientEnergy f (fun _ ↦ 0) (fun _ ↦ 1) 1 ≤ 1)
    (n : ℕ) (J : (originalDyadicFacePartition (ι := Fin q) n).boxes) :
    (originalDyadicTraceMeans f n J)^2 ≤
      (((1 : ℝ) / 2^n)^(q + 1))⁻¹ * (((q + 1 : ℕ) : ℝ) / 2) := by
  let h : ℝ := 1 / 2^n
  have hh : 0 < h := by positivity
  have hh1 : h ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hbnds := Box.le_iff_bounds.mp
    ((originalDyadicFacePartition (ι := Fin q) n).le_of_mem J.2)
  change (0 : Fin q → ℝ) ≤ J.1.lower ∧ J.1.upper ≤ 1 at hbnds
  have hsub : Icc J.1.lower J.1.upper ×ˢ Icc (0 : ℝ) h ⊆
      Icc (0 : Fin q → ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    Set.prod_mono (Icc_subset_Icc hbnds.1 hbnds.2) (Icc_subset_Icc le_rfl hh1)
  have hm := smooth_product_subcell_mean_sq_le_of_unit_energy
    J.1.lower_lt_upper hh hf hsub hmean henergy
  have hV : volume.real (Icc J.1.lower J.1.upper ×ˢ Icc (0 : ℝ) h) = h^(q + 1) :=
    originalDyadicTraceCollar_volume_real J
  dsimp only [h] at hm hV
  simpa only [originalDyadicTraceMeans, boxCollarMean, hV] using hm

end OTSelector.Reconstruction
