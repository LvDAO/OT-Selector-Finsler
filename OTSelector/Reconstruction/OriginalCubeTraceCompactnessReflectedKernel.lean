import OTSelector.Reconstruction.OriginalInputBoundaryWeightVariance

/-! The literal finite coordinate-reflected cube kernel and its actual boundary-layer response. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The three images in each coordinate are the original point and its reflections across
both actual faces of the original centered cube of radius R. -/
def originalCubeReflectionImage (R : ℝ) (a : ι → Fin 3) (x : ι → ℝ) : ι → ℝ :=
  fun i ↦ if a i = 0 then x i else if a i = 1 then -2 * R - x i else 2 * R - x i

omit [Fintype ι] [DecidableEq ι] in
/-- The identity image retains the original physical point exactly. -/
theorem originalCubeReflectionImage_zero (R : ℝ) (x : ι → ℝ) :
    originalCubeReflectionImage R 0 x = x := by ext i; simp [originalCubeReflectionImage]

/-- The actual reflected kernel is the finite sum over all 3^q coordinate reflection images. -/
def originalCubeReflectedKernel (η : (ι → ℝ) → ℝ) (R : ℝ) (z x : ι → ℝ) : ℝ :=
  ∑ a : ι → Fin 3, η (z - originalCubeReflectionImage R a x)

omit [Fintype ι] [DecidableEq ι] in
/-- Every fixed reflection image depends continuously on the original physical point. -/
theorem continuous_originalCubeReflectionImage (R : ℝ) (a : ι → Fin 3) :
    Continuous (originalCubeReflectionImage R a) := by
  apply continuous_pi
  intro i
  dsimp only [originalCubeReflectionImage]
  split_ifs <;> fun_prop

/-- The actual reflected kernel is jointly measurable in both original physical arguments. -/
theorem measurable_originalCubeReflectedKernel
    {η : (ι → ℝ) → ℝ} (hη : Measurable η) (R : ℝ) :
    Measurable (Function.uncurry (originalCubeReflectedKernel η R)) := by
  apply Finset.measurable_sum
  intro a _
  exact hη.comp (measurable_fst.sub
    ((continuous_originalCubeReflectionImage R a).measurable.comp measurable_snd))

/-- Positivity is preserved by the genuine finite reflection sum. -/
theorem originalCubeReflectedKernel_nonneg {η : (ι → ℝ) → ℝ}
    (hη : ∀ x, 0 ≤ η x) (R : ℝ) (z x : ι → ℝ) :
    0 ≤ originalCubeReflectedKernel η R z x :=
  Finset.sum_nonneg (fun _ _ ↦ hη _)

/-- The original reflection sum has a uniform bound depending only on dimension and the
actual original kernel amplitude, with no cube-radius dependence. -/
theorem abs_originalCubeReflectedKernel_le {η : (ι → ℝ) → ℝ} {M : ℝ}
    (hη : ∀ x, |η x| ≤ M) (R : ℝ) (z x : ι → ℝ) :
    |originalCubeReflectedKernel η R z x| ≤ (3 : ℝ)^Fintype.card ι * M := by
  calc
    _ ≤ ∑ a : ι → Fin 3, |η (z - originalCubeReflectionImage R a x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : ι → Fin 3, M := Finset.sum_le_sum (fun _ _ ↦ hη _)
    _ = _ := by simp

omit [DecidableEq ι] in
/-- A nonidentity image of an inner-cube input is at least one unit away from every point
of the original cube. This is the actual geometry behind the boundary-layer restriction. -/
theorem one_le_norm_sub_originalCubeReflectionImage_of_inner
    {R : ℝ} {z x : ι → ℝ} (hz : z ∈ haarRootCube ι R)
    (hx : x ∈ haarRootCube ι (R - 1))
    {a : ι → Fin 3} (ha : a ≠ 0) :
    1 ≤ ‖z - originalCubeReflectionImage R a x‖ := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra! h
    exact ha (funext h)
  have hzi : -R ≤ z i ∧ z i ≤ R := ⟨hz.1 i, hz.2 i⟩
  have hxi : -(R - 1) ≤ x i ∧ x i ≤ R - 1 := ⟨hx.1 i, hx.2 i⟩
  have hn := norm_le_pi_norm (z - originalCubeReflectionImage R a x) i
  simp only [Real.norm_eq_abs, Pi.sub_apply, originalCubeReflectionImage, ite_eq_right hi] at hn
  by_cases h1 : a i = 1
  · rw [ite_eq_left h1] at hn
    have hab := le_abs_self (z i - (-2 * R - x i))
    linarith
  · rw [ite_eq_right h1] at hn
    have hab := neg_le_abs (z i - (2 * R - x i))
    linarith

omit [DecidableEq ι] in
/-- Reflection in either actual face cannot bring two points of the original cube closer
in the original coordinate norm. -/
theorem norm_sub_le_norm_sub_originalCubeReflectionImage
    {R : ℝ} {z x : ι → ℝ} (hz : z ∈ haarRootCube ι R) (hx : x ∈ haarRootCube ι R)
    (a : ι → Fin 3) : ‖z - x‖ ≤ ‖z - originalCubeReflectionImage R a x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  have hn := norm_le_pi_norm (z - originalCubeReflectionImage R a x) i
  simp only [Real.norm_eq_abs, Pi.sub_apply, originalCubeReflectionImage] at hn ⊢
  by_cases h0 : a i = 0
  · simpa only [ite_eq_left h0] using hn
  · rw [ite_eq_right h0] at hn
    by_cases h1 : a i = 1
    · rw [ite_eq_left h1] at hn
      have hi : |z i - x i| ≤ z i - (-2 * R - x i) :=
        abs_le.mpr ⟨by linarith [hz.1 i], by linarith [hx.1 i]⟩
      exact hi.trans ((le_abs_self _).trans hn)
    · rw [ite_eq_right h1] at hn
      have hi : |z i - x i| ≤ -(z i - (2 * R - x i)) :=
        abs_le.mpr ⟨by linarith [hx.2 i], by linarith [hz.2 i]⟩
      exact hi.trans ((neg_le_abs _).trans hn)

/-- The genuine reflected kernel retains the original unit-range spatial support. -/
theorem originalCubeReflectedKernel_eq_zero_of_one_le_norm_sub
    {η : (ι → ℝ) → ℝ} (hη : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    {R : ℝ} {z x : ι → ℝ} (hz : z ∈ haarRootCube ι R) (hx : x ∈ haarRootCube ι R)
    (hzx : 1 ≤ ‖z - x‖) : originalCubeReflectedKernel η R z x = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  exact hη _ (hzx.trans (norm_sub_le_norm_sub_originalCubeReflectionImage hz hx a))

/-- The actual reflected kernel equals the original kernel for inputs at least one unit
inside the cube. Unit-sphere vanishing holds for the paper's compact support in the open ball. -/
theorem originalCubeReflectedKernel_eq_kernel_of_inner
    {η : (ι → ℝ) → ℝ} (hη : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    {R : ℝ} {z x : ι → ℝ} (hz : z ∈ haarRootCube ι R)
    (hx : x ∈ haarRootCube ι (R - 1)) :
    originalCubeReflectedKernel η R z x = η (z - x) := by
  unfold originalCubeReflectedKernel
  calc
    _ = η (z - originalCubeReflectionImage R 0 x) :=
      Finset.sum_eq_single (0 : ι → Fin 3)
        (fun a _ ha ↦ hη (z - originalCubeReflectionImage R a x)
          (one_le_norm_sub_originalCubeReflectionImage_of_inner hz hx ha))
        (by simp)
    _ = _ := by rw [originalCubeReflectionImage_zero]

/-- The full-input response is the literal reflected smoothing inside the cube minus the
unchanged full-input ordinary kernel; it does not select or thin the original inputs. -/
def originalCubeReflectedInputResponse (η : (ι → ℝ) → ℝ) (R : ℝ) (z x : ι → ℝ) : ℝ :=
  (haarRootCube ι R).indicator (originalCubeReflectedKernel η R z) x - η (z - x)

/-- The full-input response is jointly measurable in the actual observation and input points. -/
theorem measurable_originalCubeReflectedInputResponse
    {η : (ι → ℝ) → ℝ} (hη : Measurable η) (R : ℝ) :
    Measurable (Function.uncurry (originalCubeReflectedInputResponse η R)) := by
  exact ((measurable_originalCubeReflectedKernel hη R).indicator
    (measurable_snd measurableSet_Icc)).sub (hη.comp (measurable_fst.sub measurable_snd))

/-- The true full-input response has a scale-independent uniform amplitude bound. -/
theorem abs_originalCubeReflectedInputResponse_le {η : (ι → ℝ) → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hη : ∀ x, |η x| ≤ M) (R : ℝ) (z x : ι → ℝ) :
    |originalCubeReflectedInputResponse η R z x| ≤ ((3 : ℝ)^Fintype.card ι + 1) * M := by
  unfold originalCubeReflectedInputResponse
  by_cases hx : x ∈ haarRootCube ι R
  · rw [indicator_of_mem hx]
    calc
      _ ≤ |originalCubeReflectedKernel η R z x| + |η (z - x)| := abs_sub _ _
      _ ≤ (3 : ℝ)^Fintype.card ι * M + M :=
        add_le_add (abs_originalCubeReflectedKernel_le hη R z x) (hη _)
      _ = _ := by ring
  · rw [indicator_of_notMem hx, zero_sub, abs_neg]
    exact (hη _).trans (by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (Fintype.card ι)])

/-- The full-input response at any original input is supported within its true unit
neighborhood on the original observation cube. -/
theorem originalCubeReflectedInputResponse_eq_zero_of_one_le_norm_sub
    {η : (ι → ℝ) → ℝ} (hη : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    {R : ℝ} {z x : ι → ℝ} (hz : z ∈ haarRootCube ι R) (hzx : 1 ≤ ‖z - x‖) :
    originalCubeReflectedInputResponse η R z x = 0 := by
  unfold originalCubeReflectedInputResponse
  by_cases hx : x ∈ haarRootCube ι R
  · rw [indicator_of_mem hx,
      originalCubeReflectedKernel_eq_zero_of_one_le_norm_sub hη hz hx hzx, hη _ hzx,
      sub_self]
  · rw [indicator_of_notMem hx, hη _ hzx, sub_self]

/-- Only original full-input points in the actual inner-and-outer unit boundary shell
contribute to the reflected discrepancy on the cube. -/
theorem originalCubeReflectedInputResponse_eq_zero_off_shell
    {η : (ι → ℝ) → ℝ} (hη : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    {R : ℝ} (hR : 1 ≤ R) {z x : ι → ℝ} (hz : z ∈ haarRootCube ι R)
    (hx : x ∉ originalInputBoundaryShell (ι := ι) R) :
    originalCubeReflectedInputResponse η R z x = 0 := by
  by_cases ho : x ∈ haarRootCube ι (R + 1)
  · have hi : x ∈ haarRootCube ι (R - 1) := by
      by_contra hn
      exact hx ⟨ho, hn⟩
    have hc : x ∈ haarRootCube ι R := by
      exact ⟨fun i ↦ by linarith [hi.1 i], fun i ↦ by linarith [hi.2 i]⟩
    rw [originalCubeReflectedInputResponse, indicator_of_mem hc,
      originalCubeReflectedKernel_eq_kernel_of_inner hη hz hi, sub_self]
  · have hc : x ∉ haarRootCube ι R := by
      intro hi
      apply ho
      exact ⟨fun i ↦ by linarith [hi.1 i], fun i ↦ by linarith [hi.2 i]⟩
    have hn : 1 ≤ ‖z - x‖ := by
      by_contra! hn
      apply ho
      apply (mem_haarRootCube_iff_norm_le (by linarith : 0 ≤ R + 1) x).mpr
      have hzn := (mem_haarRootCube_iff_norm_le (by linarith : 0 ≤ R) z).mp hz
      calc
        ‖x‖ = ‖z - (z - x)‖ := by congr 1; abel
        _ ≤ ‖z‖ + ‖z - x‖ := norm_sub_le _ _
        _ ≤ R + 1 := by linarith
    rw [originalCubeReflectedInputResponse, indicator_of_notMem hc, hη _ hn, sub_self]

end OTSelector.Reconstruction
