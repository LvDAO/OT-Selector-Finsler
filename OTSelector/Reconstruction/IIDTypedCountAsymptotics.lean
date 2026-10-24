import OTSelector.Reconstruction.IIDTypedCountRepair
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Mass attribution and high-dimensional count normalization

Finite deterministic type masses aggregate by concavity. The square-root
count correction vanishes under the paper normalization when q > 4.
-/

open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology

noncomputable section
namespace OTSelector.Reconstruction

/-- Concavity collects finitely many deterministic subplan masses without any
lower bound on the individual masses. -/
theorem sum_rpow_typeMass_le {T : Type*} [Fintype T] (p : T → ℝ)
    (hp : ∀ t, 0 ≤ p t) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    (∑ t, (p t) ^ γ) ≤ (Fintype.card T : ℝ) ^ (1 - γ) * (∑ t, p t) ^ γ := by
  classical
  by_cases hT : Fintype.card T = 0
  · have : IsEmpty T := Fintype.card_eq_zero_iff.mp hT
    simp [hγ0.ne', Real.zero_rpow]
  have hcard : (0 : ℝ) < Fintype.card T := by exact_mod_cast Nat.pos_of_ne_zero hT
  have h := (Real.concaveOn_rpow hγ0.le hγ1).le_map_sum
    (t := Finset.univ) (w := fun _ : T ↦ (Fintype.card T : ℝ)⁻¹)
    (p := p) (fun _ _ ↦ by positivity) (by simp [hcard.ne']) (fun t _ ↦ hp t)
  simp only [smul_eq_mul, ← Finset.mul_sum] at h
  have heq : (Fintype.card T : ℝ) *
      ((Fintype.card T : ℝ)⁻¹ * ∑ t, p t) ^ γ =
      (Fintype.card T : ℝ) ^ (1 - γ) * (∑ t, p t) ^ γ := by
    rw [Real.mul_rpow (inv_nonneg.mpr hcard.le) (Finset.sum_nonneg (fun t _ ↦ hp t)),
      Real.inv_rpow hcard.le, Real.rpow_sub hcard, Real.rpow_one]
    ring
  have hm := mul_le_mul_of_nonneg_left h hcard.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hcard.ne', one_mul, heq] using hm

/-- The square-root discrepancy remainder vanishes at the paper's normalization
precisely in the high-dimensional range used here. -/
theorem tendsto_normalized_typeCount_error {q : ℝ} (hq : 4 < q) (C ε : ℝ) :
    Tendsto (fun n : ℕ ↦ C * (n : ℝ) ^ (2 / q - 1 / 2) * Real.sqrt ε)
      atTop (𝓝 0) := by
  have hq0 : 0 < q := by linarith
  have he : 0 < (1 / 2 : ℝ) - 2 / q := by
    rw [sub_pos, div_lt_iff₀ hq0]
    linarith
  have ht := (tendsto_rpow_neg_atTop he).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  have heq : -((1 / 2 : ℝ) - 2 / q) = 2 / q - 1 / 2 := by ring
  simpa only [Function.comp_apply, heq, mul_zero, zero_mul] using (ht.const_mul C).mul_const (Real.sqrt ε)

/-- Exact normalization of the count bound for a nonempty original sample. -/
theorem normalized_count_sqrt_eq {n : ℕ} (hn : 0 < n) (q B : ℝ) :
    ((n : ℝ) ^ (2 / q) / n) * Real.sqrt ((n : ℝ) * B) =
      Real.sqrt B * (n : ℝ) ^ (2 / q - 1 / 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.sqrt_mul hnR.le, Real.sqrt_eq_rpow, Real.rpow_sub hnR]
  have hs : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) = n := by
    rw [← Real.rpow_add hnR]
    norm_num
  have hp : (n : ℝ) ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hnR _).ne'
  field_simp
  nlinarith [congrArg (fun t : ℝ ↦ t * Real.sqrt B) hs]

end OTSelector.Reconstruction
