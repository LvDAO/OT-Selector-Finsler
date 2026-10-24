import OTSelector.Reconstruction.OriginalCubeTraceCompactnessHomogeneous

/-! Actual raw unit-cube faces and the original product-collar trace coordinates. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

/-- The literal original coordinate insertion, with normal coordinate `i` and all other
coordinates in the unchanged `i.succAbove` order. -/
def cubeFaceCoordinateJoin {r : ℕ} (i : Fin (r + 1)) :
    ((Fin r → ℝ) × ℝ) →L[ℝ] (Fin (r + 1) → ℝ) :=
  ContinuousLinearMap.pi (i.insertNth
    (ContinuousLinearMap.snd ℝ (Fin r → ℝ) ℝ)
    (fun k ↦ (ContinuousLinearMap.proj k).comp (ContinuousLinearMap.fst ℝ (Fin r → ℝ) ℝ)))

@[simp]
theorem cubeFaceCoordinateJoin_apply {r : ℕ} (i : Fin (r + 1)) (p : (Fin r → ℝ) × ℝ) :
    cubeFaceCoordinateJoin i p = i.insertNth p.2 p.1 := by
  funext j
  rcases i.eq_self_or_eq_succAbove j with rfl | ⟨k, rfl⟩ <;> simp [cubeFaceCoordinateJoin]

private def cubeFaceCoordinateJoinEquiv {r : ℕ} (i : Fin (r + 1)) :
    ((Fin r → ℝ) × ℝ) ≃ᵐ (Fin (r + 1) → ℝ) :=
  MeasurableEquiv.prodComm.trans (MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) i).symm

/-- Actual original face-times-normal coordinate insertion preserves Lebesgue volume. -/
theorem measurePreserving_cubeFaceCoordinateJoin {r : ℕ} (i : Fin (r + 1)) :
    MeasurePreserving (cubeFaceCoordinateJoin i) volume volume := by
  have he : (cubeFaceCoordinateJoin i : ((Fin r → ℝ) × ℝ) → (Fin (r + 1) → ℝ)) =
      cubeFaceCoordinateJoinEquiv i := by
    funext p
    rw [cubeFaceCoordinateJoin_apply]
    rfl
  rw [he]
  exact ((volume_preserving_piFinSuccAbove (fun _ : Fin (r + 1) ↦ ℝ) i).symm _).comp
    Measure.measurePreserving_swap

/-- The original unit-cube integral is exactly the product-collar coordinate integral for
any true face normal, without any changed normalization or Jacobian hypothesis. -/
theorem integral_cubeFaceCoordinateJoin_unit {r : ℕ} (i : Fin (r + 1))
    (g : (Fin (r + 1) → ℝ) → ℝ) :
    (∫ p in Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1) ×ˢ Icc (0 : ℝ) 1,
      g (cubeFaceCoordinateJoin i p)) =
      ∫ x in Icc (fun _ : Fin (r + 1) ↦ (0 : ℝ)) (fun _ ↦ 1), g x := by
  let e := cubeFaceCoordinateJoinEquiv i
  have he : (cubeFaceCoordinateJoin i : ((Fin r → ℝ) × ℝ) → (Fin (r + 1) → ℝ)) = e := by
    funext p
    rw [cubeFaceCoordinateJoin_apply]
    rfl
  have hm : MeasurePreserving e volume volume := by
    rw [← he]
    exact measurePreserving_cubeFaceCoordinateJoin i
  have hpre : e ⁻¹' Icc (fun _ : Fin (r + 1) ↦ (0 : ℝ)) (fun _ ↦ 1) =
      Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1) ×ˢ Icc (0 : ℝ) 1 := by
    ext p
    change (i.insertNth p.2 p.1 ∈ Icc (fun _ ↦ (0 : ℝ)) (fun _ ↦ 1)) ↔ _
    simp only [mem_Icc, Pi.le_def, mem_prod]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨⟨fun k ↦ by simpa using h0 (i.succAbove k),
        fun k ↦ by simpa using h1 (i.succAbove k)⟩,
        by simpa using h0 i, by simpa using h1 i⟩
    · rintro ⟨⟨h0, h1⟩, hn0, hn1⟩
      constructor
      · exact i.forall_iff_succAbove.2 ⟨by simpa using hn0, fun k ↦ by simpa using h0 k⟩
      · exact i.forall_iff_succAbove.2 ⟨by simpa using hn1, fun k ↦ by simpa using h1 k⟩
  have hmr : MeasurePreserving e
      (volume.restrict (Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1) ×ˢ Icc (0 : ℝ) 1))
      (volume.restrict (Icc (fun _ : Fin (r + 1) ↦ (0 : ℝ)) (fun _ ↦ 1))) := by
    refine ⟨e.measurable, ?_⟩
    rw [← hpre, ← Measure.restrict_map e.measurable measurableSet_Icc, hm.map_eq]
  rw [he]
  exact hmr.integral_comp' g

/-- The exact original sum of squared partial derivatives integrated over the raw unit cube. -/
def originalRawUnitCubeGradientEnergy {q : ℕ} (φ : (Fin q → ℝ) → ℝ) : ℝ :=
  ∑ k : Fin q, ∫ x in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1),
    (fderiv ℝ φ x (Pi.single k 1))^2

@[simp]
theorem cubeFaceCoordinateJoin_normal {r : ℕ} (i : Fin (r + 1)) :
    cubeFaceCoordinateJoin i (0, 1) = Pi.single i (1 : ℝ) := by
  rw [cubeFaceCoordinateJoin_apply]
  funext j
  rcases i.eq_self_or_eq_succAbove j with rfl | ⟨k, rfl⟩ <;> simp

@[simp]
theorem cubeFaceCoordinateJoin_tangent {r : ℕ} (i : Fin (r + 1)) (k : Fin r) :
    cubeFaceCoordinateJoin i (Pi.single k 1, 0) = Pi.single (i.succAbove k) (1 : ℝ) := by
  rw [cubeFaceCoordinateJoin_apply]
  funext j
  rcases i.eq_self_or_eq_succAbove j with rfl | ⟨l, rfl⟩ <;> simp [Pi.single_apply]

/-- The genuine product-collar gradient energy of a raw-cube test equals its original
full raw-cube gradient energy, for every original coordinate normal. -/
theorem boxCollarGradientEnergy_cubeFaceCoordinateJoin {r : ℕ} (i : Fin (r + 1))
    {φ : (Fin (r + 1) → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) :
    boxCollarGradientEnergy (fun p ↦ φ (cubeFaceCoordinateJoin i p))
      (fun _ ↦ 0) (fun _ ↦ 1) 1 = originalRawUnitCubeGradientEnergy φ := by
  have hd (p : (Fin r → ℝ) × ℝ) (v : (Fin r → ℝ) × ℝ) :
      fderiv ℝ (fun p ↦ φ (cubeFaceCoordinateJoin i p)) p v =
        fderiv ℝ φ (cubeFaceCoordinateJoin i p) (cubeFaceCoordinateJoin i v) := by
    exact congrArg (fun L ↦ L v) ((hφ.differentiable (by norm_num) _).hasFDerivAt.comp p
      (cubeFaceCoordinateJoin i).hasFDerivAt).fderiv
  have hint (v : Fin (r + 1) → ℝ) :
      (∫ p in Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1) ×ˢ Icc (0 : ℝ) 1,
        (fderiv ℝ φ (cubeFaceCoordinateJoin i p) v)^2) =
        ∫ x in Icc (fun _ : Fin (r + 1) ↦ (0 : ℝ)) (fun _ ↦ 1),
          (fderiv ℝ φ x v)^2 := integral_cubeFaceCoordinateJoin_unit i (fun x ↦ (fderiv ℝ φ x v)^2)
  unfold boxCollarGradientEnergy
  simp_rw [hd, cubeFaceCoordinateJoin_tangent, cubeFaceCoordinateJoin_normal, hint]
  rw [originalRawUnitCubeGradientEnergy, Fin.sum_univ_succAbove _ i]
  exact add_comm _ _

/-- The actual lower face of every raw unit-cube coordinate has the same common compact-trace
bound, measured by the original full-cube gradient energy and mean-zero condition. -/
theorem smooth_rawUnitCube_lower_face_pairing_sq_le {r : ℕ} (i : Fin (r + 1))
    {g : (Fin r → ℝ) → ℝ}
    (hg : MemLp g 2 (volume.restrict (Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1))))
    {φ : (Fin (r + 1) → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hmean : (∫ x in Icc (fun _ : Fin (r + 1) ↦ (0 : ℝ)) (fun _ ↦ 1), φ x) = 0) :
    (∫ y in Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1), g y * φ (i.insertNth 0 y))^2 ≤
      originalTraceDualInfBound g * originalRawUnitCubeGradientEnergy φ := by
  have hf : ContDiff ℝ 1 (fun p ↦ φ (cubeFaceCoordinateJoin i p)) :=
    hφ.comp (cubeFaceCoordinateJoin i).contDiff
  have hm : (∫ p in Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1) ×ˢ Icc (0 : ℝ) 1,
      φ (cubeFaceCoordinateJoin i p)) = 0 := by
    rw [integral_cubeFaceCoordinateJoin_unit]
    exact hmean
  have h := smooth_trace_pairing_sq_le_originalTraceDualInfBound_mul_energy hg hf hm
  rw [boxCollarGradientEnergy_cubeFaceCoordinateJoin i hφ] at h
  simpa only [cubeFaceCoordinateJoin_apply] using h

end OTSelector.Reconstruction
