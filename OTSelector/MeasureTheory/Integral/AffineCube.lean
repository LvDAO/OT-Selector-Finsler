import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
## Lemma skeleton

* **Conditions:** A finite real coordinate type, arbitrary normed real vector-valued integrand and a positive affine scale R.
* **Objects:** Exact image/preimage unit-cube identities and Lebesgue cube integral scaling by R^dimension, including centered cubes.
* **Proof detail:** Solve the coordinate interval inequalities under positive scaling, transport volume through translation and scalar dilation, and cancel the nonzero Jacobian.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Theorem 263A, pp. 22–24: linear change of variables and absolute determinant.
  https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=22
* D. H. Fremlin, *Measure Theory, Volume 2*, Section 235G, integration along an inverse-measure-preserving map.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf
* D. H. Fremlin, *Measure Theory, Volume 2*, Exercises 253Y(f)(i)–(vii), 253Y(g)–(h), pp. 46–47: Banach-valued L1, bounded bilinear maps and section integrals.
  https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=46

**Relationship to the sources:** Affine special case of determinant change of variables. The Lean statements use totalized Bochner integrals without an integrability premise, and include the zero-dimensional finite product.
-/

/-! Literal affine cube coordinates and their actual Lebesgue area scaling. -/
open Set Function Filter MeasureTheory
open scoped ENNReal BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

/-- Positive affine cube coordinates have the exact original unit-cube preimage. -/
theorem preimage_affine_unit_cube_box {ι : Type*} [Fintype ι]
    (a : ι → ℝ) {R : ℝ} (hR : 0 < R) :
    (fun y : ι → ℝ ↦ a + R • y) ⁻¹' Icc a (a + R • (1 : ι → ℝ)) =
      Icc (0 : ι → ℝ) 1 := by
  ext y
  simp only [mem_preimage, mem_Icc, Pi.le_def, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Pi.one_apply, Pi.zero_apply, mul_one]
  constructor
  · rintro ⟨hl, hu⟩
    constructor
    · intro i
      apply (mul_le_mul_iff_right₀ hR).mp
      nlinarith [hl i]
    · intro i
      apply (mul_le_mul_iff_right₀ hR).mp
      nlinarith [hu i]
  · rintro ⟨hl, hu⟩
    constructor
    · intro i
      have hm := mul_nonneg hR.le (hl i)
      linarith
    · intro i
      have hm := mul_le_mul_of_nonneg_left (hu i) hR.le
      nlinarith

/-- The actual affine image is the full translated side-R cube, including its boundary. -/
theorem image_affine_unit_cube_box {ι : Type*} [Fintype ι]
    (a : ι → ℝ) {R : ℝ} (hR : 0 < R) :
    (fun y : ι → ℝ ↦ a + R • y) '' Icc (0 : ι → ℝ) 1 =
      Icc a (a + R • (1 : ι → ℝ)) := by
  have hsurj : Surjective (fun y : ι → ℝ ↦ a + R • y) := by
    intro z
    refine ⟨R⁻¹ • (z-a), ?_⟩
    change a + R • (R⁻¹ • (z-a)) = z
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul, add_sub_cancel]
  rw [← preimage_affine_unit_cube_box a hR]
  exact Set.image_preimage_eq _ hsurj

/-- The actual unit-face affine pullback has the true inverse Lebesgue area factor.
This follows from Haar dilation and translation; no Jacobian formula is an input. -/
theorem integral_affine_unit_cube_eq_inv_smul
    {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : (ι → ℝ) → F) (a : ι → ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ y in Icc (0 : ι → ℝ) 1, f (a + R • y)) =
      (R^(Fintype.card ι))⁻¹ • ∫ z in Icc a (a + R • (1 : ι → ℝ)), f z := by
  let D := Icc a (a + R • (1 : ι → ℝ))
  have hi : (fun y : ι → ℝ ↦ D.indicator f (a + R • y)) =
      (Icc (0 : ι → ℝ) 1).indicator (fun y ↦ f (a + R • y)) := by
    funext y
    have h := Set.indicator_comp_right (fun y : ι → ℝ ↦ a + R • y) (s := D) (g := f) (x := y)
    simpa only [D, preimage_affine_unit_cube_box a hR, Function.comp_def] using h.symm
  have h := Measure.integral_comp_smul_of_nonneg volume
    (fun z : ι → ℝ ↦ D.indicator f (a + z)) R (hR := hR.le)
  rw [hi, integral_indicator measurableSet_Icc, integral_add_left_eq_self,
    integral_indicator measurableSet_Icc, Module.finrank_pi] at h
  exact h

/-- Literal affine change of variables on any finite-coordinate translated cube,
with the genuine area factor R to the number of coordinates. -/
theorem integral_affine_cube_eq_pow_smul
    {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : (ι → ℝ) → F) (a : ι → ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ z in Icc a (a + R • (1 : ι → ℝ)), f z) =
      R^(Fintype.card ι) • ∫ y in Icc (0 : ι → ℝ) 1, f (a + R • y) := by
  rw [integral_affine_unit_cube_eq_inv_smul f a hR, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero _ hR.ne'), one_smul]

/-- The same genuine affine cube area formula for actual scalar readouts. -/
theorem integral_affine_cube_eq_pow_mul
    {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (a : ι → ℝ)
    {R : ℝ} (hR : 0 < R) :
    (∫ z in Icc a (a + R • (1 : ι → ℝ)), f z) =
      R^(Fintype.card ι) * ∫ y in Icc (0 : ι → ℝ) 1, f (a + R • y) := by
  simpa only [smul_eq_mul] using integral_affine_cube_eq_pow_smul f a hR

/-- The actual centered cube [-R,R] has side 2R and the corresponding full
Lebesgue area factor; its unit coordinates use the actual lower corner. -/
theorem integral_centered_cube_eq_two_mul_radius_pow_smul
    {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : (ι → ℝ) → F) {R : ℝ} (hR : 0 < R) :
    (∫ z in Icc (fun _ : ι ↦ -R) (fun _ ↦ R), f z) =
      (2*R)^(Fintype.card ι) •
        ∫ y in Icc (0 : ι → ℝ) 1, f ((fun _ : ι ↦ -R) + (2*R) • y) := by
  have hb : (fun _ : ι ↦ -R) + (2*R) • (1 : ι → ℝ) = fun _ : ι ↦ R := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
    ring
  simpa only [hb] using integral_affine_cube_eq_pow_smul f (fun _ : ι ↦ -R)
    (show 0 < 2*R by positivity)

end OTSelector.Reconstruction
