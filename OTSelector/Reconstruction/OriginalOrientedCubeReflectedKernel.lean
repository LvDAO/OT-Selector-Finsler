import OTSelector.Reconstruction.OriginalCurrentPhysicalCubeTraceBound
import OTSelector.Reconstruction.OriginalCubeReflectedInputFubini

/-! Literal reflected input kernels and smooth tests in the original chosen physical frame. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators Distributions
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace OTSelector.Reconstruction
open OTSelector.Probability

variable {q : ℕ}

/-- Euclidean radiality of an original raw-coordinate physical kernel, explicitly using
the genuine Euclidean norm rather than the raw coordinate supremum norm. -/
def IsOriginalEuclideanRadial (η : (Fin q → ℝ) → ℝ) : Prop :=
  ∀ v w, ‖(EuclideanSpace.equiv (Fin q) ℝ).symm v‖ =
    ‖(EuclideanSpace.equiv (Fin q) ℝ).symm w‖ → η v = η w

/-- The actual chosen physical orthogonal map preserves the genuine Euclidean norm. -/
theorem norm_euclidean_orthonormalPhysicalCubeMap
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (v : Fin q → ℝ) :
    ‖(EuclideanSpace.equiv (Fin q) ℝ).symm (orthonormalPhysicalCubeMap b v)‖ =
      ‖(EuclideanSpace.equiv (Fin q) ℝ).symm v‖ := by
  change ‖(orthonormalCubeCoordinates b).symm v‖ = _
  change ‖b.repr.symm ((EuclideanSpace.equiv (Fin q) ℝ).symm v)‖ = _
  exact b.repr.symm.norm_map _

/-- Radial physical kernels really retain the same literal kernel in the chosen frame. -/
theorem euclideanRadial_comp_orthonormalPhysicalCubeMap
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {η : (Fin q → ℝ) → ℝ} (hηradial : IsOriginalEuclideanRadial η) :
    η ∘ orthonormalPhysicalCubeMap b = η := by
  funext v
  exact hηradial _ _ (norm_euclidean_orthonormalPhysicalCubeMap b v)

/-- Euclidean radiality supplies the coordinate-evenness required by actual reflection. -/
theorem coordinate_even_of_euclideanRadial {η : (Fin q → ℝ) → ℝ}
    (hηradial : IsOriginalEuclideanRadial η) :
    ∀ v w : Fin q → ℝ, (∀ i, |v i| = |w i|) → η v = η w := by
  intro v w h
  apply hηradial
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change ‖v i‖^2 = ‖w i‖^2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, h i]

/-- The raw coordinate norm is bounded by the original Euclidean norm. -/
theorem raw_norm_le_euclidean_norm (v : Fin q → ℝ) :
    ‖v‖ ≤ ‖(EuclideanSpace.equiv (Fin q) ℝ).symm v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin q) ℝ).symm v) i

/-- Actual Euclidean unit-range support implies the raw support condition used by the
already proved cube reflection, without a norm-equivalence oracle. -/
theorem raw_unit_range_of_euclidean_unit_range {η : (Fin q → ℝ) → ℝ}
    (hηsupport : ∀ v, 1 ≤ ‖(EuclideanSpace.equiv (Fin q) ℝ).symm v‖ → η v = 0) :
    ∀ v, 1 ≤ ‖v‖ → η v = 0 := by
  intro v hv
  exact hηsupport v (hv.trans (raw_norm_le_euclidean_norm v))

/-- The inverse actual physical coordinate map preserves original Haar volume as well. -/
theorem measurePreserving_orthonormalPhysicalCubeMap_symm
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) :
    MeasurePreserving (orthonormalPhysicalCubeMap b).symm :=
  MeasurePreserving.symm (orthonormalPhysicalCubeMap b).toHomeomorph.toMeasurableEquiv
    (measurePreserving_orthonormalPhysicalCubeMap b)

/-- Membership in the actual physical side-L cube is literal inverse-frame membership. -/
theorem mem_originalCenteredPhysicalCubeRegion_iff
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (L : ℝ) (z : Fin q → ℝ) :
    z ∈ originalCenteredPhysicalCubeRegion b L ↔
      (orthonormalPhysicalCubeMap b).symm z ∈ haarRootCube (Fin q) (L / 2) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply, haarRootCube, neg_div] using hy
  · intro hz
    exact ⟨(orthonormalPhysicalCubeMap b).symm z,
      by simpa only [haarRootCube, neg_div] using hz,
      (orthonormalPhysicalCubeMap b).apply_symm_apply z⟩

/-- The physical reflection image across an actual face of the chosen side-L cube. -/
def originalOrientedCubeReflectionImage
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (L : ℝ) (a : Fin q → Fin 3) (x : Fin q → ℝ) : Fin q → ℝ :=
  orthonormalPhysicalCubeMap b
    (originalCubeReflectionImage (L / 2) a ((orthonormalPhysicalCubeMap b).symm x))

/-- The oriented literal response uses the actual physical kernel pulled back by the same
chosen frame; radiality is proved separately and never presumed for arbitrary kernels. -/
def originalOrientedCubeReflectedInputResponse
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (η : (Fin q → ℝ) → ℝ) (L : ℝ) (z x : Fin q → ℝ) : ℝ :=
  originalCubeReflectedInputResponse (η ∘ orthonormalPhysicalCubeMap b) (L / 2)
    ((orthonormalPhysicalCubeMap b).symm z) ((orthonormalPhysicalCubeMap b).symm x)

/-- For an actual Euclidean radial kernel, raw and oriented responses use the same eta. -/
theorem originalOrientedCubeReflectedInputResponse_of_radial
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {η : (Fin q → ℝ) → ℝ} (hηradial : IsOriginalEuclideanRadial η)
    (L : ℝ) (z x : Fin q → ℝ) :
    originalOrientedCubeReflectedInputResponse b η L z x =
      originalCubeReflectedInputResponse η (L / 2)
        ((orthonormalPhysicalCubeMap b).symm z) ((orthonormalPhysicalCubeMap b).symm x) := by
  rw [originalOrientedCubeReflectedInputResponse,
    euclideanRadial_comp_orthonormalPhysicalCubeMap b hηradial]

/-- The oriented response is exactly the physical reflected smoothing minus the unchanged
physical ordinary kernel, including the correct original input cube indicator. -/
theorem originalOrientedCubeReflectedInputResponse_eq_physical
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (η : (Fin q → ℝ) → ℝ) (L : ℝ) (z x : Fin q → ℝ) :
    originalOrientedCubeReflectedInputResponse b η L z x =
      (originalCenteredPhysicalCubeRegion b L).indicator
        (fun x ↦ ∑ a : Fin q → Fin 3, η (z - originalOrientedCubeReflectionImage b L a x)) x - η (z - x) := by
  have hm := mem_originalCenteredPhysicalCubeRegion_iff b L x
  by_cases hx : x ∈ originalCenteredPhysicalCubeRegion b L
  · rw [originalOrientedCubeReflectedInputResponse, originalCubeReflectedInputResponse,
      indicator_of_mem (hm.mp hx), indicator_of_mem hx]
    simp only [originalCubeReflectedKernel, Function.comp_apply, map_sub,
      ContinuousLinearEquiv.apply_symm_apply]
    rfl
  · rw [originalOrientedCubeReflectedInputResponse, originalCubeReflectedInputResponse,
      indicator_of_notMem (fun h ↦ hx (hm.mpr h)), indicator_of_notMem hx]
    simp only [Function.comp_apply, map_sub, ContinuousLinearEquiv.apply_symm_apply]

/-- Original physical observation-volume change of variables identifies every literal
response-test pairing with its raw-frame pairing, with no integral identity as a premise. -/
theorem integral_orientedCube_reflected_response_mul
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {η : (Fin q → ℝ) → ℝ} (hηradial : IsOriginalEuclideanRadial η)
    (L : ℝ) (x : Fin q → ℝ) (φ : (Fin q → ℝ) → ℝ) :
    (∫ z in originalCenteredPhysicalCubeRegion b L,
      originalOrientedCubeReflectedInputResponse b η L z x * φ z) =
      ∫ y in haarRootCube (Fin q) (L / 2),
        originalCubeReflectedInputResponse η (L / 2) y ((orthonormalPhysicalCubeMap b).symm x) *
          φ (orthonormalPhysicalCubeMap b y) := by
  rw [originalCenteredPhysicalCubeRegion,
    integral_orthonormalPhysicalCubeRegion b (fun _ ↦ -L / 2) (fun _ ↦ L / 2)]
  simp only [originalOrientedCubeReflectedInputResponse_of_radial b hηradial,
    ContinuousLinearEquiv.symm_apply_apply, haarRootCube, neg_div]

/-- The physical shell support is the actual orthogonal image of the original raw shell. -/
theorem originalOrientedCubeReflectedInputResponse_eq_zero_off_shell
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {η : (Fin q → ℝ) → ℝ}
    (hηsupport : ∀ v, 1 ≤ ‖(EuclideanSpace.equiv (Fin q) ℝ).symm v‖ → η v = 0)
    {L : ℝ} (hL : 2 ≤ L) {z x : Fin q → ℝ}
    (hz : z ∈ originalCenteredPhysicalCubeRegion b L)
    (hx : x ∉ orthonormalPhysicalCubeMap b '' originalInputBoundaryShell (ι := Fin q) (L / 2)) :
    originalOrientedCubeReflectedInputResponse b η L z x = 0 := by
  apply originalCubeReflectedInputResponse_eq_zero_off_shell
    (η := η ∘ orthonormalPhysicalCubeMap b)
  · intro v hv
    apply hηsupport
    rw [norm_euclidean_orthonormalPhysicalCubeMap]
    exact hv.trans (raw_norm_le_euclidean_norm v)
  · linarith
  · exact (mem_originalCenteredPhysicalCubeRegion_iff b L z).mp hz
  · intro h
    exact hx ⟨(orthonormalPhysicalCubeMap b).symm x, h,
      (orthonormalPhysicalCubeMap b).apply_symm_apply x⟩

/-- The genuine compact support for the original smooth test pulled to the chosen frame. -/
def originalOrientedCubeTestSupport
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (K : Compacts (Fin q → ℝ)) : Compacts (Fin q → ℝ) :=
  K.map (orthonormalPhysicalCubeMap b).symm (orthonormalPhysicalCubeMap b).symm.continuous

/-- The actual physical smooth test composed with the original physical frame map. -/
def originalOrientedCubeTestPullback
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {K : Compacts (Fin q → ℝ)} (φ : 𝓓_{K}(Fin q → ℝ, ℝ)) :
    𝓓_{originalOrientedCubeTestSupport b K}(Fin q → ℝ, ℝ) where
  toFun := φ ∘ orthonormalPhysicalCubeMap b
  contDiff' := φ.contDiff.comp (orthonormalPhysicalCubeMap b).contDiff
  zero_on_compl' := by
    intro y hy
    apply φ.zero_on_compl
    intro h
    exact hy ⟨orthonormalPhysicalCubeMap b y, h,
      (orthonormalPhysicalCubeMap b).symm_apply_apply y⟩

/-- The raw pulled test has precisely its original physical value at the actual frame point. -/
@[simp] theorem originalOrientedCubeTestPullback_apply
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {K : Compacts (Fin q → ℝ)} (φ : 𝓓_{K}(Fin q → ℝ, ℝ)) (y : Fin q → ℝ) :
    originalOrientedCubeTestPullback b φ y = φ (orthonormalPhysicalCubeMap b y) := rfl

/-- Actual physical zero mean becomes exactly raw zero mean under original Haar transport. -/
theorem originalOrientedCubeTestPullback_mean_zero
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (L : ℝ)
    {K : Compacts (Fin q → ℝ)} (φ : 𝓓_{K}(Fin q → ℝ, ℝ))
    (hmean : (∫ z in originalCenteredPhysicalCubeRegion b L, φ z) = 0) :
    (∫ y in haarRootCube (Fin q) (L / 2), originalOrientedCubeTestPullback b φ y) = 0 := by
  have h := integral_orthonormalPhysicalCubeRegion b (fun _ ↦ -L / 2) (fun _ ↦ L / 2) (φ : (Fin q → ℝ) → ℝ)
  simpa only [originalCenteredPhysicalCubeRegion, haarRootCube, neg_div,
    originalOrientedCubeTestPullback_apply] using h.symm.trans hmean

/-- The already proved true orthogonal Parseval and Haar transport give the original
physical full-coordinate gradient energy of the actual smooth pulled test exactly. -/
theorem originalOrientedCubeTestPullback_gradient_energy
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (L : ℝ)
    {K : Compacts (Fin q → ℝ)} (φ : 𝓓_{K}(Fin q → ℝ, ℝ)) :
    (∑ i : Fin q, ∫ y in haarRootCube (Fin q) (L / 2),
      (fderiv ℝ (originalOrientedCubeTestPullback b φ) y (Pi.single i 1))^2) =
      ∑ k : Fin q, ∫ z in originalCenteredPhysicalCubeRegion b L,
        (fderiv ℝ φ z (Pi.single k 1))^2 := by
  change (∑ i : Fin q, ∫ y in haarRootCube (Fin q) (L / 2),
    (fderiv ℝ ((φ : (Fin q → ℝ) → ℝ) ∘ orthonormalPhysicalCubeMap b) y (Pi.single i 1))^2) = _
  simpa only [originalCenteredPhysicalCubeRegion, haarRootCube, neg_div] using
    sum_integral_sq_fderiv_comp_orthonormalPhysicalCubeMap b (fun _ ↦ -L / 2) (fun _ ↦ L / 2)
      (φ.contDiff.of_le (by norm_num) : ContDiff ℝ 1 (φ : (Fin q → ℝ) → ℝ))

end OTSelector.Reconstruction
