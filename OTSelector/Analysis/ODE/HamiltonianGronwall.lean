import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ExtendFrom
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.JacobiEndpoint.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.JacobiEndpoint`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual derivative is bounded by L times the state norm on an open interval; L is nonnegative.

Objects: Uniform exponential state bound and the explicit norm bound for a linear Hamiltonian matrix pair.

Proof detail: Apply Grönwall in either direction from the center; estimate the Hamiltonian blocks by submultiplicativity and the product norm.

Sources: Gerald Teschl, Section 2.4, Lemma 2.7 and Theorem 2.8, pp. 42–44, equations (2.38)–(2.43) (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=53); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15).
Relation: Local interval/matrix specialization of Grönwall; the exact sum of block norms is derived algebraically.
-/

/-!
# Continuous Jacobi endpoint extensions

An actual solution of `‖f'‖ ≤ L * ‖f‖` on a finite open interval has a uniform
Gronwall bound and hence a uniform derivative bound. The mean value theorem makes it
Lipschitz on the entire interval. Completeness then provides limits at both endpoints
and a continuous extension to the closed interval.

For the Hamiltonian matrix system, continuous coefficients on the closed interval
supply the growth bound by compactness. This extends both the original Jacobi pair
and the second pair constructed from the actual compliance integral. Determinant
cancellation consequently bounds `|det (1 ± T)| * |det J|` throughout the interior.
No endpoint inverse, nonsingularity, or finite endpoint limit of `T` is required.

This module proves continuous endpoint extension, not differentiability at the
endpoints or smooth extension to a larger interval. Identifying the matrix system
with genuine Finsler Jacobi data remains a separate geometric step.
-/

open Set Filter
open scoped Topology NNReal

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A differential linear-growth bound gives a uniform bound on a finite open interval. -/
theorem norm_le_exp_of_norm_deriv_le_mul
    {f f' : ℝ → E} {a b c L : ℝ}
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hL : 0 ≤ L) (hg : ∀ t ∈ Ioo a b, ‖f' t‖ ≤ L * ‖f t‖)
    (hc : c ∈ Ioo a b) {t : ℝ} (ht : t ∈ Ioo a b) :
    ‖f t‖ ≤ ‖f c‖ * Real.exp (L * (b - a)) := by
  let g : ℝ → ℝ := AffineMap.lineMap c t
  have hmaps : MapsTo g (Icc 0 1) (Ioo a b) := (convex_Ioo a b).mapsTo_lineMap hc ht
  have hd : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt (f ∘ g) ((t - c) • f' (g s)) s := by
    intro s hs
    exact (hf (g s) (hmaps hs)).scomp s AffineMap.hasDerivAt_lineMap
  have hcont : ContinuousOn (f ∘ g) (Icc (0 : ℝ) 1) :=
    fun s hs ↦ (hd s hs).continuousAt.continuousWithinAt
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1,
      ‖(t - c) • f' (g s)‖ ≤ (L * |t - c|) * ‖(f ∘ g) s‖ + 0 := by
    intro s hs
    rw [norm_smul, Real.norm_eq_abs, add_zero]
    calc
      |t - c| * ‖f' (g s)‖ ≤ |t - c| * (L * ‖f (g s)‖) :=
        mul_le_mul_of_nonneg_left (hg _ (hmaps (Ico_subset_Icc_self hs))) (abs_nonneg _)
      _ = (L * |t - c|) * ‖(f ∘ g) s‖ := by dsimp; ring
  have hbnd := norm_le_gronwallBound_of_norm_deriv_right_le hcont
    (fun s hs ↦ (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (le_refl ‖(f ∘ g) 0‖) hbound 1 (by simp)
  have hdist : |t - c| ≤ b - a := by
    rw [abs_le]
    constructor <;> linarith [hc.1, hc.2, ht.1, ht.2]
  have hpre : ‖f t‖ ≤ ‖f c‖ * Real.exp (L * |t - c|) := by
    simpa [g, gronwallBound_ε0] using hbnd
  exact hpre.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdist hL)) (norm_nonneg _))



variable [CompleteSpace E]





open Matrix
open scoped Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A direct operator-norm growth bound for the Hamiltonian matrix field. -/
theorem norm_hamiltonian_pair_le (A B C K R : Matrix n n ℝ) :
    ‖(B * K + C * R, -A * K - Bᵀ * R)‖ ≤
      (‖A‖ + ‖B‖ + ‖C‖ + ‖Bᵀ‖) * ‖(K, R)‖ := by
  have hK : ‖K‖ ≤ ‖(K, R)‖ := norm_fst_le (K, R)
  have hR : ‖R‖ ≤ ‖(K, R)‖ := norm_snd_le (K, R)
  rw [Prod.norm_def]
  apply max_le
  · calc
      ‖B * K + C * R‖ ≤ ‖B * K‖ + ‖C * R‖ := norm_add_le _ _
      _ ≤ ‖B‖ * ‖K‖ + ‖C‖ * ‖R‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (‖B‖ + ‖C‖) * ‖(K, R)‖ := by
        rw [add_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hK (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hR (norm_nonneg _))
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by linarith [norm_nonneg A, norm_nonneg B, norm_nonneg C, norm_nonneg Bᵀ])
        (norm_nonneg _)
  · calc
      ‖-A * K - Bᵀ * R‖ ≤ ‖-A * K‖ + ‖Bᵀ * R‖ := norm_sub_le _ _
      _ ≤ ‖-A‖ * ‖K‖ + ‖Bᵀ‖ * ‖R‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = ‖A‖ * ‖K‖ + ‖Bᵀ‖ * ‖R‖ := by rw [norm_neg]
      _ ≤ (‖A‖ + ‖Bᵀ‖) * ‖(K, R)‖ := by
        rw [add_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hK (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hR (norm_nonneg _))
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by linarith [norm_nonneg A, norm_nonneg B, norm_nonneg C, norm_nonneg Bᵀ])
        (norm_nonneg _)








end OTSelector.Geometry

end
