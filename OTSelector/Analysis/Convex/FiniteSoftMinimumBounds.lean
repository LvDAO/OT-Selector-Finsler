import OTSelector.Analysis.Convex.FiniteSoftMinimum
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FiniteSoftMinimumBounds.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FiniteSoftMinimumBounds`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FiniteSoftMinimumBounds

**Conditions:** A nonempty finite index set and positive smoothing ε.

**Objects:** The smooth minimum and its explicit ε log(card I) approximation error.

**Proof detail:** One exponential summand bounds the sum below, while a common lower value bounds every summand above; monotonicity of log and multiplication by −ε yields the two inequalities.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=86), Section 3.1.5, pp. 72–74, log-sum-exp example and derivative calculation.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Exact error bounds for the actual finite smooth minimum

The only smoothing loss is the explicit finite entropy term ε log(card I).
-/
open Finset
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1800000

variable {I : Type*} [Fintype I] [Nonempty I]

omit [Nonempty I] in
theorem finiteSoftMinimum_le_component {ε : ℝ} (hε : 0 < ε) (a : I → ℝ) (i : I) :
    finiteSoftMinimum ε a ≤ a i := by
  have hsum : Real.exp (-ε⁻¹ * a i) ≤ ∑ j, Real.exp (-ε⁻¹ * a j) :=
    Finset.single_le_sum (f := fun j ↦ Real.exp (-ε⁻¹ * a j))
      (fun j _ ↦ (Real.exp_pos _).le) (mem_univ i)
  have hm := mul_le_mul_of_nonneg_left
    (Real.log_le_log (Real.exp_pos _) hsum) hε.le
  rw [Real.log_exp] at hm
  have heq : ε * (-ε⁻¹ * a i) = -a i := by
    rw [neg_mul, mul_neg, ← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]
  rw [heq] at hm
  dsimp only [finiteSoftMinimum]
  linarith

theorem finiteSoftMinimum_lower {ε : ℝ} (hε : 0 < ε) (a : I → ℝ)
    {m : ℝ} (hm : ∀ i, m ≤ a i) :
    m - ε * Real.log (Fintype.card I) ≤ finiteSoftMinimum ε a := by
  have hsum : (∑ i, Real.exp (-ε⁻¹ * a i)) ≤
      (Fintype.card I : ℝ) * Real.exp (-ε⁻¹ * m) := by
    calc
      _ ≤ ∑ _ : I, Real.exp (-ε⁻¹ * m) := Finset.sum_le_sum fun i _ ↦
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hm i)
          (neg_nonpos.mpr (inv_nonneg.mpr hε.le)))
      _ = _ := by simp
  have hcard : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hlog := Real.log_le_log (finiteSoftMinimum_sum_exp_pos ε a) hsum
  rw [Real.log_mul hcard.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hε.le
  rw [mul_add, neg_mul, mul_neg, ← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul] at hmul
  dsimp only [finiteSoftMinimum]
  linarith

/-- Any already identified minimum value gives a uniform exact smoothing error. -/
theorem finiteSoftMinimum_error {ε : ℝ} (hε : 0 < ε) (a : I → ℝ)
    (i : I) (hmin : ∀ j, a i ≤ a j) :
    a i - ε * Real.log (Fintype.card I) ≤ finiteSoftMinimum ε a ∧
      finiteSoftMinimum ε a ≤ a i :=
  ⟨finiteSoftMinimum_lower hε a hmin, finiteSoftMinimum_le_component hε a i⟩

end OTSelector.Reconstruction

end
end
