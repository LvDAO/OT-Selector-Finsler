import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Analysis.Normed.CoordinateCovectorBound

## Lemma skeleton

* **Conditions:** A real continuous linear functional on the finite coordinate space, equipped with the stated raw coordinate norm.

* **Objects:** A covector operator-norm square bound by the sum of squared coordinate values and the norm-equivalence constant.

* **Proof detail:** Identify the covector with a Euclidean dual vector, apply finite Cauchy–Schwarz, and transfer the Euclidean norm estimate through the explicit coordinate equivalence.

## Mathematical sources

- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=57): Section 1.4, Lemma 1.4.7 (Cauchy–Schwarz inequality), p. 48.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (corollary): The norm-equivalence factor is retained explicitly; the raw coordinate norm is not silently replaced by a Euclidean norm.
-/

/-! A raw-coordinate covector estimate with its finite-dimensional norm constant. -/

noncomputable section

namespace OTSelector.Reconstruction

/-- The operator norm of a real covector on the raw coordinate space is controlled by the
sum of the squares of its coordinate values. The constant is the squared norm of the inverse
map from raw coordinates to Euclidean space. -/
theorem raw_covector_norm_sq_le_coord_sum {q : ℕ} (L : (Fin q → ℝ) →L[ℝ] ℝ) :
    ‖L‖ ^ 2 ≤ ‖(EuclideanSpace.equiv (Fin q) ℝ).symm.toContinuousLinearMap‖ ^ 2 *
      ∑ k, (L (Pi.single k 1)) ^ 2 := by
  let e := EuclideanSpace.equiv (Fin q) ℝ
  let M : EuclideanSpace ℝ (Fin q) →L[ℝ] ℝ := L.comp e.toContinuousLinearMap
  have hcoord (k : Fin q) :
      M ((EuclideanSpace.basisFun (Fin q) ℝ) k) = L (Pi.single k 1) := by
    simp only [M, ContinuousLinearMap.comp_apply, EuclideanSpace.basisFun_apply]
    rfl
  have hM : ‖M‖ ^ 2 = ∑ k, (L (Pi.single k 1)) ^ 2 := by
    simpa only [hcoord] using (EuclideanSpace.basisFun (Fin q) ℝ).norm_dual M
  have hcomp : L = M.comp e.symm.toContinuousLinearMap := by
    ext x
    change L x = L (e (e.symm x))
    rw [e.apply_symm_apply]
  have hnorm : ‖L‖ ≤ ‖M‖ * ‖e.symm.toContinuousLinearMap‖ := by
    calc
      ‖L‖ = ‖M.comp e.symm.toContinuousLinearMap‖ := congrArg norm hcomp
      _ ≤ ‖M‖ * ‖e.symm.toContinuousLinearMap‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
  calc
    ‖L‖ ^ 2 ≤ (‖M‖ * ‖e.symm.toContinuousLinearMap‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hnorm
    _ = ‖e.symm.toContinuousLinearMap‖ ^ 2 * ∑ k, (L (Pi.single k 1)) ^ 2 := by
      rw [mul_pow, hM]
      ring

end OTSelector.Reconstruction
