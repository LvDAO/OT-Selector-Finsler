import OTSelector.Reconstruction.OriginalCubeTraceCompactnessAllFaces
import OTSelector.MeasureTheory.Integral.AffineCube

/-! True physical side-length scaling of original cube boundary traces and gradient energy. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

/-- The actual original squared coordinate-gradient energy on a raw translated box. -/
def originalRawBoxGradientEnergy {q : ℕ}
    (a b : Fin q → ℝ) (φ : (Fin q → ℝ) → ℝ) : ℝ :=
  ∑ k : Fin q, ∫ x in Icc a b, (fderiv ℝ φ x (Pi.single k 1))^2

/-- The original raw cube test has the exact positive affine pullback gradient scaling,
including its true volume factor, by actual differentiation and Haar change of variables. -/
theorem originalRawUnitCubeGradientEnergy_affine {q : ℕ}
    {φ : (Fin q → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) (a : Fin q → ℝ)
    {R : ℝ} (hR : 0 < R) :
    originalRawUnitCubeGradientEnergy (fun y ↦ φ (a + R • y)) =
      R^2 * (R^q)⁻¹ * originalRawBoxGradientEnergy a (a + R • 1) φ := by
  have haff (p : Fin q → ℝ) : HasFDerivAt (fun y : Fin q → ℝ ↦ a + R • y)
      (R • ContinuousLinearMap.id ℝ (Fin q → ℝ)) p := by
    simpa only [zero_add, Pi.add_def, Pi.smul_def, id_eq] using
      (hasFDerivAt_const a p).add ((hasFDerivAt_id p).const_smul R)
  have hd (k : Fin q) (p : Fin q → ℝ) :
      fderiv ℝ (fun y ↦ φ (a + R • y)) p (Pi.single k 1) =
        R * fderiv ℝ φ (a + R • p) (Pi.single k 1) := by
    have h := congrArg (fun L ↦ L (Pi.single k 1))
      ((hφ.differentiable (by norm_num) _).hasFDerivAt.comp p (haff p)).fderiv
    simpa only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, Function.comp_def] using h
  have hint (k : Fin q) :
      (∫ y in Icc (0 : Fin q → ℝ) 1,
        (fderiv ℝ (fun y ↦ φ (a + R • y)) y (Pi.single k 1))^2) =
        R^2 * (R^q)⁻¹ * ∫ x in Icc a (a + R • 1), (fderiv ℝ φ x (Pi.single k 1))^2 := by
    simp_rw [hd, mul_pow, integral_const_mul]
    rw [integral_affine_unit_cube_eq_inv_smul
      (fun x ↦ (fderiv ℝ φ x (Pi.single k 1))^2) a hR]
    simp only [Fintype.card_fin, smul_eq_mul, mul_assoc]
  unfold originalRawUnitCubeGradientEnergy originalRawBoxGradientEnergy
  simp only [Pi.zero_def, Pi.one_def] at hint ⊢
  simp_rw [hint]
  rw [← Finset.mul_sum]

/-- The original affine coordinate change commutes exactly with inserting the face normal. -/
theorem affine_cube_face_insertNth {r : ℕ} (a : Fin (r + 1) → ℝ) (R : ℝ)
    (i : Fin (r + 1)) (c : ℝ) (y : Fin r → ℝ) :
    a + R • i.insertNth c y = i.insertNth (a i + R*c) (a ∘ i.succAbove + R • y) := by
  funext k
  rcases i.eq_self_or_eq_succAbove k with rfl | ⟨j, rfl⟩ <;> simp

/-- The genuine signed boundary integral on the original translated side-R raw cube. Every
face uses its own actual tangent box, original face normal coordinate and area measure. -/
def originalAffineCubeBoundaryPairing {r : ℕ}
    (a : Fin (r + 1) → ℝ) (R : ℝ)
    (g : Fin (r + 1) × Fin 2 → (Fin r → ℝ) → ℝ)
    (φ : (Fin (r + 1) → ℝ) → ℝ) : ℝ :=
  ∑ j : Fin (r + 1) × Fin 2, (if j.2 = 0 then (-1 : ℝ) else 1) *
    ∫ z in Icc (a ∘ j.1.succAbove) (a ∘ j.1.succAbove + R • 1),
      g j z * φ (j.1.insertNth (if j.2 = 0 then a j.1 else a j.1 + R) z)

/-- Actual raw face area change of variables scales the full signed boundary pairing by
R to the true face dimension, with unchanged normal sign and complete test pullback. -/
theorem originalAffineCubeBoundaryPairing_eq_unit {r : ℕ}
    (a : Fin (r + 1) → ℝ) {R : ℝ} (hR : 0 < R)
    (g : Fin (r + 1) × Fin 2 → (Fin r → ℝ) → ℝ)
    (φ : (Fin (r + 1) → ℝ) → ℝ) :
    originalAffineCubeBoundaryPairing a R g φ = R^r * originalRawUnitCubeBoundaryPairing
      (fun j y ↦ g j (a ∘ j.1.succAbove + R • y)) (fun y ↦ φ (a + R • y)) := by
  have hface (j : Fin (r + 1) × Fin 2) :
      (∫ z in Icc (a ∘ j.1.succAbove) (a ∘ j.1.succAbove + R • 1),
        g j z * φ (j.1.insertNth (if j.2 = 0 then a j.1 else a j.1 + R) z)) =
      R^r * ∫ y in Icc (0 : Fin r → ℝ) 1,
        g j (a ∘ j.1.succAbove + R • y) *
          φ (a + R • j.1.insertNth (if j.2 = 0 then 0 else 1) y) := by
    rw [integral_affine_cube_eq_pow_mul _ _ hR, Fintype.card_fin]
    congr 1
    apply setIntegral_congr_fun measurableSet_Icc
    intro y _
    simp only [affine_cube_face_insertNth, mul_ite, mul_zero, mul_one, add_ite, add_zero]
  unfold originalAffineCubeBoundaryPairing originalRawUnitCubeBoundaryPairing
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hface j]
  simp only [Pi.zero_def, Pi.one_def]
  ring

/-- The true side-R original boundary squared pairing is bounded by R^q times the same unit
common trace quantity and the actual original physical box-gradient energy. Both area and
volume powers are derived, and the test mean is the actual physical cube integral. -/
theorem smooth_affineCube_all_faces_pairing_sq_le {r : ℕ}
    (a : Fin (r + 1) → ℝ) {R : ℝ} (hR : 0 < R)
    {g : Fin (r + 1) × Fin 2 → (Fin r → ℝ) → ℝ}
    (hg : ∀ j, MemLp (fun y ↦ g j (a ∘ j.1.succAbove + R • y)) 2
      (volume.restrict (Icc (0 : Fin r → ℝ) 1)))
    {φ : (Fin (r + 1) → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hmean : (∫ x in Icc a (a + R • 1), φ x) = 0) :
    (originalAffineCubeBoundaryPairing a R g φ)^2 ≤
      R^(r + 1) * originalRawUnitCubeBoundaryTraceDualBound
        (fun j y ↦ g j (a ∘ j.1.succAbove + R • y)) *
        originalRawBoxGradientEnergy a (a + R • 1) φ := by
  have hf : ContDiff ℝ 1 (fun y ↦ φ (a + R • y)) :=
    hφ.comp (contDiff_const.add (contDiff_id.const_smul R))
  have hm : (∫ y in Icc (0 : Fin (r + 1) → ℝ) 1, φ (a + R • y)) = 0 := by
    rw [integral_affine_unit_cube_eq_inv_smul φ a hR, hmean, smul_zero]
  have h := smooth_rawUnitCube_all_faces_pairing_sq_le hg hf hm
  rw [originalRawUnitCubeGradientEnergy_affine hφ a hR] at h
  have hscale : (R^r)^2 * R^2 * (R^(r + 1))⁻¹ = R^(r + 1) := by
    rw [← mul_pow, ← pow_succ, pow_two, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hR.ne'), mul_one]
  rw [originalAffineCubeBoundaryPairing_eq_unit a hR g φ, mul_pow]
  have hproduct (B E : ℝ) :
      (R^r)^2 * (B * (R^2 * (R^(r + 1))⁻¹ * E)) = R^(r + 1) * B * E := by
    calc
      _ = ((R^r)^2 * R^2 * (R^(r + 1))⁻¹) * (B * E) := by ring
      _ = _ := by rw [hscale, mul_assoc]
  exact (mul_le_mul_of_nonneg_left h (sq_nonneg (R^r))).trans_eq (hproduct _ _)


end OTSelector.Reconstruction
