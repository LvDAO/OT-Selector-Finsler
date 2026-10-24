import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalClasswiseStageCouplingBookkeeping.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalClasswiseStageCouplingBookkeeping`; the selected original proof blocks follow. -/
section

/-!
Conditions: The actual nonnegative residual/potential quantities satisfy the stated stage-weight inequality and additive split, with ordered positive stage indices.

Objects: A single weighted finite-stage quadratic potential comparison.

Proof detail: Substitute the additive split, apply the weighted comparison and use the remaining nonnegative coefficient to close the inequality.

Sources: Terence Tao, Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11 (https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean).
Relation: Elementary real-algebra bookkeeping lemma; it assumes no coupling existence by itself.
-/

/-! Scalar energy accounting for the actual finite-stage weighted splice. -/
namespace OTSelector.Reconstruction
set_option maxHeartbeats 160000

/-- The actual weighted joint estimate and exact target splitting propagate the
linear-length prefix energy potential. -/
theorem finiteStage_quadratic_prefix_potential_le
    {N k G A B C D A' X : ℝ} (hk : 0 < k) (hN : k + 1 ≤ N)
    (hX : 0 ≤ X) (hD : 0 ≤ D)
    (hweighted : C ≤ (k + 1) / k * A + (k + 1) * B)
    (hsplit : A' + X = C + D) :
    G + X + N / (k + 1) * A' ≤ G + N / k * A + N * (B + D) := by
  have hk₁ : 0 < k + 1 := by linarith
  have hN₀ : 0 ≤ N := by linarith
  let c := N / (k + 1)
  have hc₁ : 1 ≤ c := (le_div_iff₀ hk₁).mpr (by simpa using hN)
  have hc₀ : 0 ≤ c := le_trans zero_le_one hc₁
  have hcN : c ≤ N := by
    apply (div_le_iff₀ hk₁).mpr
    nlinarith [mul_nonneg hN₀ hk.le]
  have hcancel : c * ((k + 1) / k * A + (k + 1) * B + D) =
      N / k * A + N * B + c * D := by
    dsimp [c]
    field_simp
  calc
    _ ≤ G + c * (A' + X) := by nlinarith [mul_le_mul_of_nonneg_right hc₁ hX]
    _ = G + c * (C + D) := by rw [hsplit]
    _ ≤ G + c * ((k + 1) / k * A + (k + 1) * B + D) := by
      have := mul_le_mul_of_nonneg_left (add_le_add_right hweighted D) hc₀
      linarith
    _ = G + N / k * A + N * B + c * D := by rw [hcancel]; ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hcN hD]

end OTSelector.Reconstruction

end
