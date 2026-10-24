import OTSelector.Reconstruction.OriginalCubeTraceCompactnessReflectedKernel
import Mathlib.MeasureTheory.Integral.Pi

/-! Genuine reflected cube-kernel mass and constant-density preservation by finite image boxes. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Every literal coordinate reflection image is an actual involution. -/
theorem originalCubeReflectionImage_involutive (R : ℝ) (a : ι → Fin 3) :
    Function.Involutive (originalCubeReflectionImage R a) := by
  intro x
  ext i
  simp only [originalCubeReflectionImage]
  split_ifs <;> ring

/-- The actual finite-coordinate reflection is a homeomorphism of the original physical space. -/
def originalCubeReflectionHomeomorph (R : ℝ) (a : ι → Fin 3) : (ι → ℝ) ≃ₜ (ι → ℝ) where
  toFun := originalCubeReflectionImage R a
  invFun := originalCubeReflectionImage R a
  left_inv := originalCubeReflectionImage_involutive R a
  right_inv := originalCubeReflectionImage_involutive R a
  continuous_toFun := continuous_originalCubeReflectionImage R a
  continuous_invFun := continuous_originalCubeReflectionImage R a

omit [DecidableEq ι] in
/-- The actual coordinate reflection preserves original Haar volume. -/
theorem measurePreserving_originalCubeReflectionImage (R : ℝ) (a : ι → Fin 3) :
    MeasurePreserving (originalCubeReflectionImage R a) volume volume := by
  let f : ι → ℝ → ℝ := fun i t ↦ if a i = 0 then t else if a i = 1 then -2 * R - t else 2 * R - t
  have hf (i : ι) : MeasurePreserving (f i) volume volume := by
    by_cases h0 : a i = 0
    · simpa only [f, ite_eq_left h0, Function.id_def] using MeasurePreserving.id (volume : Measure ℝ)
    · by_cases h1 : a i = 1
      · simpa only [f, ite_eq_right h0, ite_eq_left h1] using
          volume.measurePreserving_sub_left (-2 * R)
      · simpa only [f, ite_eq_right h0, ite_eq_right h1] using
          volume.measurePreserving_sub_left (2 * R)
  exact measurePreserving_pi (fun _ : ι ↦ (volume : Measure ℝ))
    (fun _ : ι ↦ (volume : Measure ℝ)) hf

private def reflectionBoxLower (R : ℝ) (a : ι → Fin 3) : ι → ℝ :=
  fun i ↦ if a i = 0 then -R else if a i = 1 then -3 * R else R
private def reflectionBoxUpper (R : ℝ) (a : ι → Fin 3) : ι → ℝ :=
  fun i ↦ if a i = 0 then R else if a i = 1 then -R else 3 * R
private def reflectionBoxHalfOpen (R : ℝ) (a : ι → Fin 3) : Set (ι → ℝ) :=
  Set.univ.pi (fun i ↦ Ioc (reflectionBoxLower R a i) (reflectionBoxUpper R a i))

omit [Fintype ι] [DecidableEq ι] in
private theorem image_originalCubeReflectionImage_cube (R : ℝ) (a : ι → Fin 3) :
    originalCubeReflectionImage R a '' haarRootCube ι R =
      Icc (reflectionBoxLower R a) (reflectionBoxUpper R a) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor <;> intro i <;>
      simp only [originalCubeReflectionImage, reflectionBoxLower, reflectionBoxUpper] <;>
      split_ifs <;> linarith [hx.1 i, hx.2 i]
  · intro hy
    refine ⟨originalCubeReflectionImage R a y, ?_, originalCubeReflectionImage_involutive R a y⟩
    constructor <;> intro i
    all_goals
      have hl := hy.1 i
      have hu := hy.2 i
      simp only [originalCubeReflectionImage, reflectionBoxLower, reflectionBoxUpper] at hl hu ⊢
      split_ifs at hl hu ⊢ <;> linarith

omit [Fintype ι] [DecidableEq ι] in
private theorem iUnion_reflectionBoxHalfOpen {R : ℝ} (hR : 0 ≤ R) :
    (⋃ a : ι → Fin 3, reflectionBoxHalfOpen R a) =
      Set.univ.pi (fun _ : ι ↦ Ioc (-3 * R) (3 * R)) := by
  ext y
  simp only [mem_iUnion, reflectionBoxHalfOpen, mem_pi, mem_univ, true_implies]
  constructor
  · rintro ⟨a, ha⟩ i
    have hi := ha i
    simp only [reflectionBoxLower, reflectionBoxUpper] at hi
    split_ifs at hi <;> constructor <;> linarith [hi.1, hi.2]
  · intro hy
    refine ⟨fun i ↦ if y i ≤ -R then 1 else if y i ≤ R then 0 else 2, fun i ↦ ?_⟩
    have hi := hy i
    by_cases h1 : y i ≤ -R
    · simp only [ite_eq_left h1, reflectionBoxLower, reflectionBoxUpper,
        show ¬(1 : Fin 3) = 0 by decide, ite_false, ite_true, mem_Ioc]
      exact ⟨hi.1, h1⟩
    · by_cases h0 : y i ≤ R
      · simp only [ite_eq_right h1, ite_eq_left h0, reflectionBoxLower, reflectionBoxUpper,
          ite_true]
        exact ⟨lt_of_not_ge h1, h0⟩
      · simp only [ite_eq_right h1, ite_eq_right h0, reflectionBoxLower, reflectionBoxUpper,
          show ¬(2 : Fin 3) = 0 by decide, show ¬(2 : Fin 3) = 1 by decide, ite_false]
        exact ⟨lt_of_not_ge h0, hi.2⟩

omit [Fintype ι] [DecidableEq ι] in
private theorem pairwise_disjoint_reflectionBoxHalfOpen {R : ℝ} (_hR : 0 ≤ R) :
    Pairwise (Disjoint on (reflectionBoxHalfOpen R : (ι → Fin 3) → Set (ι → ℝ))) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro y ha hb
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
    by_contra! h
    exact hab (funext h)
  have hya := ha i (mem_univ i)
  have hyb := hb i (mem_univ i)
  dsimp only [reflectionBoxLower, reflectionBoxUpper] at hya hyb
  generalize hia : a i = ai at hi hya
  generalize hib : b i = bi at hi hyb
  fin_cases ai <;> fin_cases bi <;> simp_all <;> linarith


private theorem sum_integral_reflection_boxes {R : ℝ} (hR : 0 ≤ R)
    {f : (ι → ℝ) → ℝ} (hf : Integrable f volume) :
    (∑ a : ι → Fin 3, ∫ z in Icc (reflectionBoxLower R a) (reflectionBoxUpper R a), f z) =
      ∫ z in haarRootCube ι (3 * R), f z := by
  have hae (a : ι → Fin 3) :
      reflectionBoxHalfOpen R a =ᵐ[volume] Icc (reflectionBoxLower R a) (reflectionBoxUpper R a) :=
    Measure.univ_pi_Ioc_ae_eq_Icc
  calc
    _ = ∑ a : ι → Fin 3, ∫ z in reflectionBoxHalfOpen R a, f z := by
      apply Finset.sum_congr rfl
      intro a _
      exact setIntegral_congr_set (hae a).symm
    _ = ∫ z in ⋃ a : ι → Fin 3, reflectionBoxHalfOpen R a, f z :=
      (integral_iUnion_fintype (fun _ ↦ MeasurableSet.univ_pi (fun _ ↦ measurableSet_Ioc))
        (pairwise_disjoint_reflectionBoxHalfOpen hR) (fun _ ↦ hf.integrableOn)).symm
    _ = _ := by
      rw [iUnion_reflectionBoxHalfOpen hR]
      change (∫ z in Set.univ.pi (fun _ : ι ↦ Ioc (-3 * R) (3 * R)), f z) =
        ∫ z in Icc (fun _ : ι ↦ -(3 * R)) (fun _ ↦ 3 * R), f z
      simp only [neg_mul]
      exact setIntegral_congr_set Measure.univ_pi_Ioc_ae_eq_Icc

omit [Fintype ι] [DecidableEq ι] in
private theorem kernel_reflection_integrand_eq
    {η : (ι → ℝ) → ℝ}
    (hηeven : ∀ v w : ι → ℝ, (∀ i, |v i| = |w i|) → η v = η w)
    (R : ℝ) (a : ι → Fin 3) (z x : ι → ℝ) :
    η (z - originalCubeReflectionImage R a x) =
      η (originalCubeReflectionImage R a z - x) := by
  apply hηeven
  intro i
  simp only [Pi.sub_apply, originalCubeReflectionImage]
  by_cases h0 : a i = 0
  · simp only [ite_eq_left h0]
  · simp only [ite_eq_right h0]
    by_cases h1 : a i = 1
    · simp only [ite_eq_left h1]
      have he : z i - (-2 * R - x i) = -((-2 * R - z i) - x i) := by ring
      rw [he, abs_neg]
    · simp only [ite_eq_right h1]
      have he : z i - (2 * R - x i) = -((2 * R - z i) - x i) := by ring
      rw [he, abs_neg]

/-- The original coordinate-even kernel, in particular a radial mollifier, gives the actual
symmetric reflected cube kernel by the same finite image formula. -/
theorem originalCubeReflectedKernel_symmetric
    {η : (ι → ℝ) → ℝ}
    (hηeven : ∀ v w : ι → ℝ, (∀ i, |v i| = |w i|) → η v = η w)
    (R : ℝ) (z x : ι → ℝ) : originalCubeReflectedKernel η R z x =
      originalCubeReflectedKernel η R x z := by
  apply Finset.sum_congr rfl
  intro a _
  apply hηeven
  intro i
  simp only [Pi.sub_apply, originalCubeReflectionImage]
  split_ifs
  · exact abs_sub_comm _ _
  · congr 1
    ring
  · congr 1
    ring

/-- Actual finite reflection image boxes preserve the original mollifier mass on the cube.
The proof partitions a genuine larger box and uses the real compact-support cutoff. -/
theorem integral_originalCubeReflectedKernel_eq_one
    {η : (ι → ℝ) → ℝ} (hηI : Integrable η volume)
    (hηone : ∫ v, η v = 1) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    (hηeven : ∀ v w : ι → ℝ, (∀ i, |v i| = |w i|) → η v = η w)
    {R : ℝ} (hR : 1 ≤ R) {x : ι → ℝ} (hx : x ∈ haarRootCube ι R) :
    (∫ z in haarRootCube ι R, originalCubeReflectedKernel η R z x) = 1 := by
  have hint (a : ι → Fin 3) : Integrable
      (fun z ↦ η (z - originalCubeReflectionImage R a x)) volume :=
    hηI.comp_sub_right _
  calc
    _ = ∑ a : ι → Fin 3, ∫ z in haarRootCube ι R,
        η (z - originalCubeReflectionImage R a x) :=
      integral_finsetSum Finset.univ (fun a _ ↦ (hint a).integrableOn)
    _ = ∑ a : ι → Fin 3, ∫ z in Icc (reflectionBoxLower R a) (reflectionBoxUpper R a),
        η (z - x) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← image_originalCubeReflectionImage_cube R a]
      rw [(measurePreserving_originalCubeReflectionImage R a).setIntegral_image_emb
        (originalCubeReflectionHomeomorph R a).measurableEmbedding]
      apply setIntegral_congr_fun measurableSet_Icc
      intro z _
      exact kernel_reflection_integrand_eq hηeven R a z x
    _ = ∫ z in haarRootCube ι (3 * R), η (z - x) :=
      sum_integral_reflection_boxes (by linarith) (hηI.comp_sub_right x)
    _ = ∫ z, η (z - x) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      apply hηsupport
      by_contra! hn
      apply hz
      apply (mem_haarRootCube_iff_norm_le (by linarith : 0 ≤ 3 * R) z).mpr
      have hxn := (mem_haarRootCube_iff_norm_le (by linarith : 0 ≤ R) x).mp hx
      calc
        ‖z‖ = ‖(z - x) + x‖ := by congr 1; abel
        _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
        _ ≤ 3 * R := by linarith
    _ = 1 := by rw [integral_sub_right_eq_self, hηone]

/-- The same actual reflected kernel preserves constant input density at every cube point. -/
theorem integral_originalCubeReflectedKernel_input_eq_one
    {η : (ι → ℝ) → ℝ} (hηI : Integrable η volume)
    (hηone : ∫ v, η v = 1) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    (hηeven : ∀ v w : ι → ℝ, (∀ i, |v i| = |w i|) → η v = η w)
    {R : ℝ} (hR : 1 ≤ R) {z : ι → ℝ} (hz : z ∈ haarRootCube ι R) :
    (∫ x in haarRootCube ι R, originalCubeReflectedKernel η R z x) = 1 := by
  simp_rw [originalCubeReflectedKernel_symmetric hηeven R z]
  exact integral_originalCubeReflectedKernel_eq_one hηI hηone hηsupport hηeven hR hz

/-- The full-input response is integrable over the entire original input space, before
any Poisson sampling or spatial truncation of the original inputs. -/
theorem integrable_originalCubeReflectedInputResponse_input
    {η : (ι → ℝ) → ℝ} (hηI : Integrable η volume)
    (hηeven : ∀ v w : ι → ℝ, (∀ i, |v i| = |w i|) → η v = η w)
    (R : ℝ) (z : ι → ℝ) :
    Integrable (originalCubeReflectedInputResponse η R z) volume := by
  have hk : Integrable (fun x ↦ originalCubeReflectedKernel η R x z) volume :=
    integrable_finsetSum Finset.univ (fun a _ ↦ hηI.comp_sub_right
      (originalCubeReflectionImage R a z))
  have hs : Integrable (originalCubeReflectedKernel η R z) volume := by
    apply hk.congr
    exact ae_of_all _ (fun x ↦ (originalCubeReflectedKernel_symmetric hηeven R z x).symm)
  exact (hs.indicator measurableSet_Icc).sub (hηI.comp_sub_left z)

/-- The true full-input response has exactly zero Haar mean at every observation point
in the original cube, including for one color separately. -/
theorem integral_originalCubeReflectedInputResponse_input_eq_zero
    {η : (ι → ℝ) → ℝ} (hηI : Integrable η volume)
    (hηone : ∫ v, η v = 1) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    (hηeven : ∀ v w : ι → ℝ, (∀ i, |v i| = |w i|) → η v = η w)
    {R : ℝ} (hR : 1 ≤ R) {z : ι → ℝ} (hz : z ∈ haarRootCube ι R) :
    (∫ x, originalCubeReflectedInputResponse η R z x) = 0 := by
  have hk : Integrable (fun x ↦ originalCubeReflectedKernel η R x z) volume :=
    integrable_finsetSum Finset.univ (fun a _ ↦ hηI.comp_sub_right
      (originalCubeReflectionImage R a z))
  have hs : Integrable (originalCubeReflectedKernel η R z) volume := by
    apply hk.congr
    exact ae_of_all _ (fun x ↦ (originalCubeReflectedKernel_symmetric hηeven R z x).symm)
  change (∫ x, (haarRootCube ι R).indicator (originalCubeReflectedKernel η R z) x -
    η (z - x)) = 0
  have hi : Integrable ((haarRootCube ι R).indicator (originalCubeReflectedKernel η R z))
      volume := hs.indicator measurableSet_Icc
  rw [integral_sub hi (hηI.comp_sub_left z),
    integral_indicator (show MeasurableSet (haarRootCube ι R) from measurableSet_Icc),
    integral_originalCubeReflectedKernel_input_eq_one hηI hηone hηsupport hηeven hR hz,
    integral_sub_left_eq_self, hηone, sub_self]

end OTSelector.Reconstruction
