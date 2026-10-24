import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Analysis.Calculus.BoxGaussGreen

Conditions: A C1 vector field and scalar weight on the given finite-dimensional coordinate box.

Objects: Unweighted and weighted box Gauss–Green identities with an explicit coordinate-face boundary sum.

Proof detail: Apply interval FTC to every coordinate and Fubini to the remaining coordinates; use the product rule for the weighted divergence.

## Mathematical sources

- [Jiří Lebl, Basic Analysis I](https://www.jirka.org/ra/realanal.pdf#page=200): Section 5.3.1, Theorem 5.3.1, pp. 200–201.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf): Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini).
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=75): Theorem 475N, p. 75 (Divergence Theorem).

Source relation: The book divergence theorem gives context; this exact face-sum version is proved independently by coordinate FTC/Fubini.
-/

/-! The actual C¹ divergence theorem and weighted Gauss–Green formula on raw-coordinate boxes. -/

open Set Function MeasureTheory
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Reconstruction

/-- C¹ vector fields satisfy the genuine divergence theorem on any closed raw-coordinate box.
Continuity of the actual Fréchet derivative supplies compact-box integrability. -/
theorem smooth_box_integral_divergence
    {n : ℕ} (a b : Fin (n + 1) → ℝ) (hab : a ≤ b)
    {j : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)} (hj : ContDiff ℝ 1 j) :
    (∫ x in Icc a b, ∑ i : Fin (n + 1), fderiv ℝ j x (Pi.single i 1) i) =
      ∑ i : Fin (n + 1),
        ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            j (i.insertNth (b i) y) i) -
          ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            j (i.insertNth (a i) y) i) := by
  classical
  have hdiv : Continuous
      (fun x ↦ ∑ i : Fin (n + 1), fderiv ℝ j x (Pi.single i 1) i) := by
    fun_prop (disch := exact hj.continuous_fderiv (by norm_num))
  exact integral_divergence_of_hasFDerivAt_off_countable a b hab j (fderiv ℝ j)
    ∅ countable_empty hj.continuous.continuousOn
    (fun x _ ↦ (hj.differentiable (by norm_num) x).hasFDerivAt)
    hdiv.continuousOn.integrableOn_Icc

/-- The actual derivative of the weighted vector field expands into its two product-rule terms. -/
theorem smooth_weighted_divergence_eq
    {n : ℕ} {φ : (Fin (n + 1) → ℝ) → ℝ}
    {j : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)}
    (hφ : ContDiff ℝ 1 φ) (hj : ContDiff ℝ 1 j) (x : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), fderiv ℝ (fun z ↦ φ z • j z) x (Pi.single i 1) i) =
      φ x * (∑ i : Fin (n + 1), fderiv ℝ j x (Pi.single i 1) i) +
        ∑ i : Fin (n + 1), (fderiv ℝ φ x (Pi.single i 1)) * j x i := by
  rw [fderiv_fun_smul (hφ.differentiable (by norm_num) x)
    (hj.differentiable (by norm_num) x)]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, Finset.mul_sum]

/-- Weighted Gauss–Green for actual C¹ scalar and vector fields on a closed box. Every bulk
derivative and each signed face integral is explicit; integrability follows from C¹ regularity. -/
theorem smooth_box_weighted_gauss_green
    {n : ℕ} (a b : Fin (n + 1) → ℝ) (hab : a ≤ b)
    {φ : (Fin (n + 1) → ℝ) → ℝ}
    {j : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)}
    (hφ : ContDiff ℝ 1 φ) (hj : ContDiff ℝ 1 j) :
    (∫ x in Icc a b,
        φ x * (∑ i : Fin (n + 1), fderiv ℝ j x (Pi.single i 1) i) +
          ∑ i : Fin (n + 1), (fderiv ℝ φ x (Pi.single i 1)) * j x i) =
      ∑ i : Fin (n + 1),
        ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            φ (i.insertNth (b i) y) * j (i.insertNth (b i) y) i) -
          ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            φ (i.insertNth (a i) y) * j (i.insertNth (a i) y) i) := by
  have h := smooth_box_integral_divergence a b hab
    (j := fun z ↦ φ z • j z) (hφ.smul hj)
  simpa only [smooth_weighted_divergence_eq hφ hj, Pi.smul_apply, smul_eq_mul] using h

end OTSelector.Reconstruction
