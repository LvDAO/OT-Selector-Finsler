import OTSelector.Finite.LatticeWalkCodes
import OTSelector.Finite.LatticeWalkGeometry
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinitePhaseWalkEncoding.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinitePhaseWalkEncoding`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinitePhaseWalkEncoding

**Conditions:** An integer-coordinate finite path has a bounded root and all coordinate increments bounded by one.

**Objects:** An actual finite phase-walk code representing every original vertex exactly.

**Proof detail:** Shift the bounded root and each increment into their finite digit ranges; telescoping the encoded partial sums recovers the original integer vertices coordinate by coordinate.

**Sources:** [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [OTSelector project, Finite phase-animal counting in the high-dimensional localization proof](main.tex#eq:highd-phase-animal-tail), main.tex label eq:highd-phase-animal-tail, line 3267.

Source relation (adapter): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Every bounded-step coordinate lattice path has a finite phase-walk code

The representation is constructive from the original integer vertices. It is
the finite combinatorial link from sampled phase curves to the deterministic
candidate family, rather than an external cardinality assumption.
-/
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 2000000

/-- Every coordinate lattice path with a radius-m start and m unit steps is
represented exactly by one of the finitely many original phase-walk codes. -/
theorem exists_phaseWalkCode_of_integer_path {d m : ℕ}
    (v : Fin (m + 1) → Fin d → ℤ)
    (hroot : ∀ i, |v 0 i| ≤ (m : ℤ))
    (hstep : ∀ j : Fin m, ∀ i, |v j.succ i - v j.castSucc i| ≤ 1) :
    ∃ code : PhaseWalkCode d m, ∀ n : Fin (m + 1),
      phaseWalkVertex code n = fun i ↦ (v n i : ℝ) := by
  let root : Fin d → Fin (2 * m + 1) := fun i ↦
    ⟨(v 0 i + (m : ℤ)).toNat, (Int.toNat_lt (by
      have h := (abs_le.mp (hroot i)).1
      omega)).mpr (by
        have h := (abs_le.mp (hroot i)).2
        omega)⟩
  let step : Fin m → Fin d → Fin 3 := fun j i ↦
    ⟨(v j.succ i - v j.castSucc i + 1).toNat, (Int.toNat_lt (by
      have h := (abs_le.mp (hstep j i)).1
      omega)).mpr (by
        have h := (abs_le.mp (hstep j i)).2
        omega)⟩
  let code : PhaseWalkCode d m := (root, step)
  have hrootval (i : Fin d) : (root i : ℝ) = (v 0 i : ℝ) + (m : ℝ) := by
    have h0 : 0 ≤ v 0 i + (m : ℤ) := by
      have h := (abs_le.mp (hroot i)).1
      omega
    have h := Int.toNat_of_nonneg h0
    change ((root i : ℕ) : ℤ) = v 0 i + (m : ℤ) at h
    exact_mod_cast h
  have hstepval (j : Fin m) (i : Fin d) :
      (step j i : ℝ) = (v j.succ i : ℝ) - (v j.castSucc i : ℝ) + 1 := by
    have h0 : 0 ≤ v j.succ i - v j.castSucc i + 1 := by
      have h := (abs_le.mp (hstep j i)).1
      omega
    have h := Int.toNat_of_nonneg h0
    change ((step j i : ℕ) : ℤ) = v j.succ i - v j.castSucc i + 1 at h
    exact_mod_cast h
  have hvertices : ∀ n : ℕ, ∀ hn : n < m + 1,
      phaseWalkVertex code n = fun i ↦ (v ⟨n, hn⟩ i : ℝ) := by
    intro n
    induction n with
    | zero =>
      intro hn
      ext i
      simp only [phaseWalkVertex, Nat.not_lt_zero, ite_false, Finset.sum_const_zero, add_zero]
      change (root i : ℝ) - (m : ℝ) = (v 0 i : ℝ)
      rw [hrootval]
      ring
    | succ n ih =>
      intro hn
      have hnm : n < m := by omega
      rw [phaseWalkVertex_succ code hnm, ih (by omega)]
      ext i
      change (v ⟨n, _⟩ i : ℝ) + ((step ⟨n, hnm⟩ i : ℝ) - 1) = _
      rw [hstepval]
      change (v ⟨n, by omega⟩ i : ℝ) +
        ((v ⟨n + 1, hn⟩ i : ℝ) - (v ⟨n, by omega⟩ i : ℝ) + 1 - 1) =
        (v ⟨n + 1, hn⟩ i : ℝ)
      linarith
  exact ⟨code, fun n ↦ hvertices n n.isLt⟩

end OTSelector.Reconstruction

end
end
