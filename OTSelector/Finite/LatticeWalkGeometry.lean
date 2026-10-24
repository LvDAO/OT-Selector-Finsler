import OTSelector.Finite.LatticeWalkCodes
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.PhaseWalkGeometry.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.PhaseWalkGeometry`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.PhaseWalkGeometry

**Conditions:** A finite phase-walk code records a bounded integer root and unit coordinate steps.

**Objects:** Its literal lattice vertices and their root/step norm bounds.

**Proof detail:** Expand the finite accumulated steps, telescope consecutive vertices and use the coordinate supremum norm with step digits in {0,1,2}.

**Sources:** [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [OTSelector project, Finite phase-animal counting in the high-dimensional localization proof](main.tex#eq:highd-phase-animal-tail), main.tex label eq:highd-phase-animal-tail, line 3267.

Source relation (adapter): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Literal bounded-step phase vertices of the finite candidate codes

The finite code space is realized as coordinate lattice walks. Consecutive
vertices have coordinate norm at most one, and a radius-m root stays in the
radius-(m+n) box after n steps.
-/
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1600000

/-- The actual coordinate lattice vertex encoded after n steps. -/
def phaseWalkVertex {d m : ℕ} (code : PhaseWalkCode d m) (n : ℕ) : Fin d → ℝ :=
  fun i ↦ (code.1 i : ℝ) - (m : ℝ) +
    ∑ j : Fin m, if (j : ℕ) < n then (code.2 j i : ℝ) - 1 else 0

/-- Each encoded transition is precisely its original coordinate step. -/
theorem phaseWalkVertex_succ {d m : ℕ} (code : PhaseWalkCode d m)
    {n : ℕ} (hn : n < m) :
    phaseWalkVertex code (n + 1) = phaseWalkVertex code n +
      fun i ↦ (code.2 ⟨n, hn⟩ i : ℝ) - 1 := by
  ext i
  have hdiff :
      (∑ j : Fin m, if (j : ℕ) < n + 1 then (code.2 j i : ℝ) - 1 else 0) -
        (∑ j : Fin m, if (j : ℕ) < n then (code.2 j i : ℝ) - 1 else 0) =
        (code.2 ⟨n, hn⟩ i : ℝ) - 1 := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ = ∑ j : Fin m, if j = ⟨n, hn⟩ then (code.2 j i : ℝ) - 1 else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : (j : ℕ) < n
        · have hj' : (j : ℕ) < n + 1 := by omega
          have hjne : j ≠ ⟨n, hn⟩ := by
            intro heq
            have heqv := congrArg Fin.val heq
            change (j : ℕ) = n at heqv
            omega
          simp [hj, hj', hjne]
        · by_cases heq : j = ⟨n, hn⟩
          · subst j; simp
          · have hj' : ¬(j : ℕ) < n + 1 := by
              have hneq : (j : ℕ) ≠ n := fun h ↦ heq (Fin.ext h)
              omega
            simp [hj, hj', heq]
      _ = _ := by simp
  change (code.1 i : ℝ) - (m : ℝ) + _ = ((code.1 i : ℝ) - (m : ℝ) + _) + _
  linarith

/-- The encoded root lies in the original radius-m phase box. -/
theorem norm_phaseWalkVertex_zero_le {d m : ℕ} (code : PhaseWalkCode d m) :
    ‖phaseWalkVertex code 0‖ ≤ (m : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg m)).mpr
  intro i
  simp only [phaseWalkVertex, Nat.not_lt_zero, ite_false,
    Finset.sum_const_zero, add_zero, Real.norm_eq_abs]
  have hnonneg : 0 ≤ (code.1 i : ℝ) := Nat.cast_nonneg _
  have hupper : (code.1 i : ℝ) ≤ 2 * (m : ℝ) := by
    exact_mod_cast (Nat.le_of_lt_succ (code.1 i).isLt)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Every literal coded phase-walk step has coordinate norm at most one. -/
theorem norm_phaseWalkVertex_succ_sub_le {d m : ℕ} (code : PhaseWalkCode d m)
    {n : ℕ} (hn : n < m) :
    ‖phaseWalkVertex code (n + 1) - phaseWalkVertex code n‖ ≤ 1 := by
  rw [phaseWalkVertex_succ code hn, add_sub_cancel_left]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  change |(code.2 ⟨n, hn⟩ i : ℝ) - 1| ≤ 1
  have hlo : 0 ≤ (code.2 ⟨n, hn⟩ i : ℝ) := Nat.cast_nonneg _
  have hhi : (code.2 ⟨n, hn⟩ i : ℝ) ≤ 2 := by
    exact_mod_cast (Nat.le_of_lt_succ (code.2 ⟨n, hn⟩ i).isLt)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end OTSelector.Reconstruction

end
end
