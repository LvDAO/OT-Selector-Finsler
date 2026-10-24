import OTSelector.Reconstruction.OriginalCubeTraceCompactnessFaceCoordinates
import OTSelector.MeasureTheory.UnitCubeReflection

/-! One actual common trace bound for all original raw unit-cube faces. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

/-- The upper coordinate face obeys the same common trace bound and original full-cube
energy, by genuine unit-cube reflection preserving both volume and derivative energy. -/
theorem smooth_rawUnitCube_upper_face_pairing_sq_le {r : ℕ} (i : Fin (r + 1))
    {g : (Fin r → ℝ) → ℝ}
    (hg : MemLp g 2 (volume.restrict (Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1))))
    {φ : (Fin (r + 1) → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hmean : (∫ x in Icc (fun _ : Fin (r + 1) ↦ (0 : ℝ)) (fun _ ↦ 1), φ x) = 0) :
    (∫ y in Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1), g y * φ (i.insertNth 1 y))^2 ≤
      originalTraceDualInfBound g * originalRawUnitCubeGradientEnergy φ := by
  have hf : ContDiff ℝ 1 (φ ∘ unitCubeCoordinateReflection i) :=
    hφ.comp ((contDiff_unitCubeCoordinateReflection i).of_le (by norm_num))
  have hm : (∫ x in Icc (fun _ : Fin (r + 1) ↦ (0 : ℝ)) (fun _ ↦ 1),
      (φ ∘ unitCubeCoordinateReflection i) x) = 0 := by
    exact (integral_unitCubeCoordinateReflection i φ).trans hmean
  have he : originalRawUnitCubeGradientEnergy (φ ∘ unitCubeCoordinateReflection i) =
      originalRawUnitCubeGradientEnergy φ := sum_integral_sq_fderiv_comp_unitCubeCoordinateReflection i hφ
  have h := smooth_rawUnitCube_lower_face_pairing_sq_le i hg hf hm
  rw [he] at h
  simpa only [Function.comp_def, unitCubeCoordinateReflection_insertNth_zero] using h

/-- The literal signed sum of all original unit-cube face trace pairings. -/
def originalRawUnitCubeBoundaryPairing {r : ℕ}
    (g : Fin (r + 1) × Fin 2 → (Fin r → ℝ) → ℝ)
    (φ : (Fin (r + 1) → ℝ) → ℝ) : ℝ :=
  ∑ j : Fin (r + 1) × Fin 2, (if j.2 = 0 then (-1 : ℝ) else 1) *
    ∫ y in Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1),
      g j y * φ (j.1.insertNth (if j.2 = 0 then 0 else 1) y)

/-- A concrete common quadratic bound for all smooth mean-zero raw-cube tests: the actual
number of faces times the sum of their proved compact-trace bounds. -/
def originalRawUnitCubeBoundaryTraceDualBound {r : ℕ}
    (g : Fin (r + 1) × Fin 2 → (Fin r → ℝ) → ℝ) : ℝ :=
  (Fintype.card (Fin (r + 1) × Fin 2) : ℝ) *
    ∑ j : Fin (r + 1) × Fin 2, originalTraceDualInfBound (g j)

/-- The concrete common boundary bound is nonnegative for every actual family of face data. -/
theorem originalRawUnitCubeBoundaryTraceDualBound_nonneg {r : ℕ}
    (g : Fin (r + 1) × Fin 2 → (Fin r → ℝ) → ℝ) :
    0 ≤ originalRawUnitCubeBoundaryTraceDualBound g :=
  mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun _ _ ↦ originalTraceDualInfBound_nonneg _))

/-- Every actual mean-zero C¹ raw-cube test is controlled on all original 2q faces at once
by the same concrete face-data bound times its original full coordinate-gradient energy. -/
theorem smooth_rawUnitCube_all_faces_pairing_sq_le {r : ℕ}
    {g : Fin (r + 1) × Fin 2 → (Fin r → ℝ) → ℝ}
    (hg : ∀ j, MemLp (g j) 2 (volume.restrict (Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1))))
    {φ : (Fin (r + 1) → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hmean : (∫ x in Icc (fun _ : Fin (r + 1) ↦ (0 : ℝ)) (fun _ ↦ 1), φ x) = 0) :
    (originalRawUnitCubeBoundaryPairing g φ)^2 ≤
      originalRawUnitCubeBoundaryTraceDualBound g * originalRawUnitCubeGradientEnergy φ := by
  classical
  let a := fun j : Fin (r + 1) × Fin 2 ↦
    ∫ y in Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1),
      g j y * φ (j.1.insertNth (if j.2 = 0 then 0 else 1) y)
  have hface (j : Fin (r + 1) × Fin 2) :
      (a j)^2 ≤ originalTraceDualInfBound (g j) * originalRawUnitCubeGradientEnergy φ := by
    by_cases hj : j.2 = 0
    · simpa only [a, ite_eq_left hj] using smooth_rawUnitCube_lower_face_pairing_sq_le j.1 (hg j) hφ hmean
    · simpa only [a, ite_eq_right hj] using smooth_rawUnitCube_upper_face_pairing_sq_le j.1 (hg j) hφ hmean
  have hc (j : Fin (r + 1) × Fin 2) : (if j.2 = 0 then (-1 : ℝ) else 1)^2 ≤ (1 : ℝ) := by
    split_ifs <;> norm_num
  have hcs := sum_mul_sq_le_fintype_card_mul_of_coeff_sq_le
    (fun j : Fin (r + 1) × Fin 2 ↦ if j.2 = 0 then (-1 : ℝ) else 1) a hc
  calc
    _ ≤ (Fintype.card (Fin (r + 1) × Fin 2) : ℝ) * ∑ j, (a j)^2 := by
      simpa only [originalRawUnitCubeBoundaryPairing, mul_one] using hcs
    _ ≤ (Fintype.card (Fin (r + 1) × Fin 2) : ℝ) *
        ∑ j, originalTraceDualInfBound (g j) * originalRawUnitCubeGradientEnergy φ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ ↦ hface j)) (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, originalRawUnitCubeBoundaryTraceDualBound]; ring

end OTSelector.Reconstruction
