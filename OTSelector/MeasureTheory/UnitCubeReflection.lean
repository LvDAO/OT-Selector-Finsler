import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
## Lemma skeleton

* **Conditions:** A selected coordinate of a finite real product; derivative-energy identities additionally assume a C1 real potential.
* **Objects:** The affine unit-cube reflection, its explicit derivative, volume preservation, cube integral invariance and invariance of every coordinate squared-derivative integral.
* **Proof detail:** Reflect x_i to 1-x_i. Its derivative flips the corresponding basis sign and its determinant has absolute value one; the cube is preserved. Apply change of variables and the chain rule, then square away the sign.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Theorem 263A, pp. 22–24: linear change of variables and absolute determinant.
  https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=22
* D. H. Fremlin, *Measure Theory, Volume 2*, Section 235G, integration along an inverse-measure-preserving map.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf

**Relationship to the sources:** Explicit affine volume-preserving involution and derivative calculation. Energy invariance is proved for each coordinate, then summed; the normed-vector integral formula uses the totalized convention.
-/

/-! Actual unit-cube coordinate reflection, volume preservation and full derivative energy. -/

open Set Function MeasureTheory
open scoped BigOperators ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Reconstruction

/-- The literal affine reflection of one coordinate in the middle of the unit cube. -/
def unitCubeCoordinateReflection {q : ℕ} (i : Fin q) (x : Fin q → ℝ) : Fin q → ℝ :=
  Function.update x i (1 - x i)

/-- Reflecting the same coordinate twice returns the original point. -/
theorem unitCubeCoordinateReflection_involutive {q : ℕ} (i : Fin q) :
    Function.Involutive (unitCubeCoordinateReflection i) := by
  intro x
  ext k
  by_cases hk : k = i <;> simp [unitCubeCoordinateReflection, hk]

/-- The actual affine coordinate reflection is smooth. -/
theorem contDiff_unitCubeCoordinateReflection {q : ℕ} (i : Fin q) :
    ContDiff ℝ ∞ (unitCubeCoordinateReflection i) := by
  apply contDiff_pi.mpr
  intro k
  by_cases hk : k = i
  · subst k
    simpa only [unitCubeCoordinateReflection, Function.update_self] using
      (contDiff_const.sub (contDiff_apply ℝ ℝ i) :
        ContDiff ℝ ∞ (fun x : Fin q → ℝ ↦ (1 : ℝ) - x i))
  · simpa only [unitCubeCoordinateReflection, Function.update_of_ne hk] using
      (contDiff_apply ℝ ℝ k : ContDiff ℝ ∞ (fun x : Fin q → ℝ ↦ x k))

private def unitCubeReflectionLinear {q : ℕ} (i : Fin q) :
    (Fin q → ℝ) →L[ℝ] (Fin q → ℝ) :=
  ContinuousLinearMap.pi (fun k ↦ if k = i then
    -(ContinuousLinearMap.proj k : (Fin q → ℝ) →L[ℝ] ℝ) else ContinuousLinearMap.proj k)

private theorem hasFDerivAt_unitCubeCoordinateReflection {q : ℕ} (i : Fin q)
    (x : Fin q → ℝ) :
    HasFDerivAt (unitCubeCoordinateReflection i) (unitCubeReflectionLinear i) x := by
  apply hasFDerivAt_pi.mpr
  intro k
  by_cases hk : k = i
  · subst k
    simpa only [unitCubeCoordinateReflection, Function.update_self, unitCubeReflectionLinear,
      ContinuousLinearMap.pi_apply, ite_true, zero_sub, Pi.sub_def] using
      (hasFDerivAt_const (1 : ℝ) x).sub
        (hasFDerivAt_apply i x)
  · simpa only [unitCubeCoordinateReflection, Function.update_of_ne hk,
      unitCubeReflectionLinear, ContinuousLinearMap.pi_apply, ite_eq_right hk] using
      hasFDerivAt_apply k x

/-- The actual derivative changes only the reflected unit direction's sign. -/
theorem fderiv_unitCubeCoordinateReflection_apply_single {q : ℕ} (i k : Fin q)
    (x : Fin q → ℝ) :
    fderiv ℝ (unitCubeCoordinateReflection i) x (Pi.single k 1) =
      if k = i then -(Pi.single k 1) else Pi.single k 1 := by
  rw [(hasFDerivAt_unitCubeCoordinateReflection i x).fderiv]
  ext j
  by_cases hj : j = i
  · subst j
    by_cases hk : k = i
    · subst k
      simp [unitCubeReflectionLinear]
    · simp [unitCubeReflectionLinear, hk, Ne.symm hk, ContinuousLinearMap.proj_apply]
  · by_cases hk : k = i
    · subst k
      simp [unitCubeReflectionLinear, hj, ContinuousLinearMap.proj_apply]
    · simp [unitCubeReflectionLinear, hj, hk, ContinuousLinearMap.proj_apply]

/-- The actual reflection preserves full Lebesgue volume, by the true one-dimensional reflection
and the finite product measure theorem. -/
theorem measurePreserving_unitCubeCoordinateReflection {q : ℕ} (i : Fin q) :
    MeasurePreserving (unitCubeCoordinateReflection i) volume volume := by
  classical
  let f : Fin q → ℝ → ℝ := fun k r ↦ if k = i then 1 - r else r
  have hf (k : Fin q) : MeasurePreserving (f k) volume volume := by
    by_cases hk : k = i
    · simpa [f, hk] using volume.measurePreserving_sub_left (1 : ℝ)
    · change MeasurePreserving (fun r : ℝ ↦ if k = i then 1 - r else r) volume volume
      simp only [ite_eq_right hk]
      exact MeasurePreserving.id (volume : Measure ℝ)
  have hp := measurePreserving_pi (fun _ : Fin q ↦ (volume : Measure ℝ))
    (fun _ : Fin q ↦ (volume : Measure ℝ)) hf
  have heq : (fun x k ↦ f k (x k)) = unitCubeCoordinateReflection i := by
    funext x k
    by_cases hk : k = i <;> simp [f, unitCubeCoordinateReflection, hk]
  rw [heq] at hp
  simpa only [← volume_pi] using hp

/-- The whole closed unit cube, including its boundary, has exactly itself as preimage. -/
theorem preimage_unitCubeCoordinateReflection_unit {q : ℕ} (i : Fin q) :
    unitCubeCoordinateReflection i ⁻¹' Icc (0 : Fin q → ℝ) 1 = Icc 0 1 := by
  have hm : ∀ {x : Fin q → ℝ}, x ∈ Icc (0 : Fin q → ℝ) 1 →
      unitCubeCoordinateReflection i x ∈ Icc (0 : Fin q → ℝ) 1 := by
    intro x hx
    constructor <;> intro k
    · by_cases hk : k = i
      · subst k
        have h : x i ≤ (1 : ℝ) := hx.2 i
        simpa only [unitCubeCoordinateReflection, Function.update_self, Pi.zero_apply] using
          (sub_nonneg.mpr h)
      · simpa only [unitCubeCoordinateReflection, Function.update_of_ne hk] using hx.1 k
    · by_cases hk : k = i
      · subst k
        have h : (0 : ℝ) ≤ x i := hx.1 i
        simp only [unitCubeCoordinateReflection, Function.update_self, Pi.one_apply]
        linarith
      · simpa only [unitCubeCoordinateReflection, Function.update_of_ne hk] using hx.2 k
  ext x
  constructor
  · intro hx
    have h := hm hx
    simpa only [unitCubeCoordinateReflection_involutive i x] using h
  · exact hm

private def unitCubeCoordinateReflectionHomeomorph {q : ℕ} (i : Fin q) :
    (Fin q → ℝ) ≃ₜ (Fin q → ℝ) where
  toFun := unitCubeCoordinateReflection i
  invFun := unitCubeCoordinateReflection i
  left_inv := unitCubeCoordinateReflection_involutive i
  right_inv := unitCubeCoordinateReflection_involutive i
  continuous_toFun := (contDiff_unitCubeCoordinateReflection i).continuous
  continuous_invFun := (contDiff_unitCubeCoordinateReflection i).continuous

/-- Unit-cube reflection preserves the literal integral of any scalar or Bochner-valued function. -/
theorem integral_unitCubeCoordinateReflection {q : ℕ} (i : Fin q)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (g : (Fin q → ℝ) → Y) :
    (∫ x in Icc (0 : Fin q → ℝ) 1, g (unitCubeCoordinateReflection i x)) =
      ∫ x in Icc (0 : Fin q → ℝ) 1, g x := by
  have h := (measurePreserving_unitCubeCoordinateReflection i).setIntegral_preimage_emb
    (unitCubeCoordinateReflectionHomeomorph i).measurableEmbedding g (Icc 0 1)
  simpa only [preimage_unitCubeCoordinateReflection_unit] using h

/-- Each actual coordinate derivative energy is preserved by reflecting a C¹ scalar function. -/
theorem integral_sq_fderiv_comp_unitCubeCoordinateReflection {q : ℕ} (i k : Fin q)
    {Φ : (Fin q → ℝ) → ℝ} (hΦ : ContDiff ℝ 1 Φ) :
    (∫ x in Icc (0 : Fin q → ℝ) 1,
        (fderiv ℝ (Φ ∘ unitCubeCoordinateReflection i) x (Pi.single k 1))^2) =
      ∫ x in Icc (0 : Fin q → ℝ) 1, (fderiv ℝ Φ x (Pi.single k 1))^2 := by
  have heq (x : Fin q → ℝ) :
      (fderiv ℝ (Φ ∘ unitCubeCoordinateReflection i) x (Pi.single k 1))^2 =
        (fderiv ℝ Φ (unitCubeCoordinateReflection i x) (Pi.single k 1))^2 := by
    have hd := (hΦ.differentiable one_ne_zero _).hasFDerivAt.comp x
      (hasFDerivAt_unitCubeCoordinateReflection i x).differentiableAt.hasFDerivAt
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.comp_apply, fderiv_unitCubeCoordinateReflection_apply_single]
    split_ifs <;> simp
  simp_rw [heq]
  exact integral_unitCubeCoordinateReflection i (fun x ↦ (fderiv ℝ Φ x (Pi.single k 1))^2)

/-- The sum of all original partial-derivative L² energies is exactly reflection invariant. -/
theorem sum_integral_sq_fderiv_comp_unitCubeCoordinateReflection {q : ℕ} (i : Fin q)
    {Φ : (Fin q → ℝ) → ℝ} (hΦ : ContDiff ℝ 1 Φ) :
    (∑ k : Fin q, ∫ x in Icc (0 : Fin q → ℝ) 1,
        (fderiv ℝ (Φ ∘ unitCubeCoordinateReflection i) x (Pi.single k 1))^2) =
      ∑ k : Fin q, ∫ x in Icc (0 : Fin q → ℝ) 1,
        (fderiv ℝ Φ x (Pi.single k 1))^2 := by
  exact Finset.sum_congr rfl (fun k _ ↦ integral_sq_fderiv_comp_unitCubeCoordinateReflection i k hΦ)

/-- Reflection sends the literal lower coordinate-face embedding to the upper embedding. -/
theorem unitCubeCoordinateReflection_insertNth_zero {r : ℕ} (i : Fin (r + 1))
    (y : Fin r → ℝ) :
    unitCubeCoordinateReflection i (i.insertNth 0 y) = i.insertNth 1 y := by
  simp [unitCubeCoordinateReflection, Fin.update_insertNth]

end OTSelector.Reconstruction
