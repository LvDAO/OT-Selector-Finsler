import OTSelector.Finite.LatticePathEncoding
import OTSelector.Finite.LatticeWalkCodes
import OTSelector.Finite.LatticeWalkGeometry
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.PhaseCurveSampledCover.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.PhaseCurveSampledCover`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.PhaseCurveSampledCover

**Conditions:** A finite real path has bounded root and unit sampled steps, or a curve on [0,1] has the explicit speed m with m≥1.

**Objects:** One actual finite phase-walk code covering the whole original curve within radius two.

**Proof detail:** Take coordinate floors of the sampled path to obtain integer unit steps, encode them exactly and bound the rounding error by one; nearest sample time and the speed bound supply the other unit.

**Sources:** [Thomas W. Judson, Abstract Algebra: Theory and Applications (author online edition)](https://twjudson.github.io/aata-files/aata-html/integers-section-division-algorithm.html), Section 2.2, Theorem 2.2.1 (Division Algorithm); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [OTSelector project, Finite phase-animal counting in the high-dimensional localization proof](main.tex#eq:highd-phase-animal-tail), main.tex label eq:highd-phase-animal-tail, line 3267.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Every bounded-speed phase curve has one finite original candidate cover

Coordinate floors of a sampled curve form an actual unit-step lattice path.
Its exact finite code gives a fixed-radius cover of the entire curve, with no
external finite-animal/cardinality assumption.
-/
open Set
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 2200000

/-- A real unit-step sampled path has a finite lattice code within coordinate distance one. -/
theorem exists_phaseWalkCode_of_real_path {d m : ℕ}
    (v : Fin (m + 1) → Fin d → ℝ) (hroot : ‖v 0‖ ≤ (m : ℝ))
    (hstep : ∀ j : Fin m, ‖v j.succ - v j.castSucc‖ ≤ 1) :
    ∃ code : PhaseWalkCode d m, ∀ n : Fin (m + 1),
      ‖v n - phaseWalkVertex code n‖ ≤ 1 := by
  let w : Fin (m + 1) → Fin d → ℤ := fun n i ↦ ⌊v n i⌋
  have hwroot (i : Fin d) : |w 0 i| ≤ (m : ℤ) := by
    have hi : |v 0 i| ≤ (m : ℝ) := (norm_le_pi_norm (v 0) i).trans hroot
    apply abs_le.mpr
    constructor
    · apply Int.le_floor.mpr
      simpa only [Int.cast_neg, Int.cast_natCast] using (abs_le.mp hi).1
    · have h := Int.floor_mono (abs_le.mp hi).2
      simpa only [Int.floor_natCast] using h
  have hwstep (j : Fin m) (i : Fin d) : |w j.succ i - w j.castSucc i| ≤ 1 := by
    have hi : |v j.succ i - v j.castSucc i| ≤ 1 :=
      (norm_le_pi_norm (v j.succ - v j.castSucc) i).trans (hstep j)
    have hu := Int.floor_mono (show v j.succ i ≤ v j.castSucc i + 1 by
      linarith [(abs_le.mp hi).2])
    have hl := Int.floor_mono (show v j.castSucc i ≤ v j.succ i + 1 by
      linarith [(abs_le.mp hi).1])
    rw [Int.floor_add_one] at hu hl
    exact abs_le.mpr ⟨by dsimp [w]; omega, by dsimp [w]; omega⟩
  obtain ⟨code, hcode⟩ := exists_phaseWalkCode_of_integer_path w hwroot hwstep
  refine ⟨code, fun n ↦ ?_⟩
  rw [hcode]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  change |v n i - (⌊v n i⌋ : ℝ)| ≤ 1
  exact abs_le.mpr ⟨by linarith [Int.floor_le (v n i)],
    by linarith [Int.lt_floor_add_one (v n i)]⟩

/-- A phase curve of speed at most m on the unit interval is covered by the vertices of
one of the finite m-step codes, with the same fixed coordinate radius two. -/
theorem exists_phaseWalkCode_cover_of_curve {d m : ℕ} (hm : 1 ≤ m)
    (γ : ℝ → Fin d → ℝ) (hroot : ‖γ 0‖ ≤ (m : ℝ))
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖γ s - γ t‖ ≤ (m : ℝ) * |s - t|) :
    ∃ code : PhaseWalkCode d m, ∀ t ∈ Icc (0 : ℝ) 1,
      ∃ n : Fin (m + 1), ‖γ t - phaseWalkVertex code n‖ ≤ 2 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hm0 := hmpos.le
  let v : Fin (m + 1) → Fin d → ℝ := fun n ↦ γ ((n : ℝ) / (m : ℝ))
  have htime (n : Fin (m + 1)) : (n : ℝ) / (m : ℝ) ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) hm0, (div_le_one hmpos).mpr ?_⟩
    exact_mod_cast Nat.le_of_lt_succ n.isLt
  have hvroot : ‖v 0‖ ≤ (m : ℝ) := by simpa [v] using hroot
  have hvstep (j : Fin m) : ‖v j.succ - v j.castSucc‖ ≤ 1 := by
    have h := hLip _ (htime j.succ) _ (htime j.castSucc)
    have hdiff : (j.succ : ℝ) / (m : ℝ) - (j.castSucc : ℝ) / (m : ℝ) = 1 / (m : ℝ) := by
      simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
      field_simp
      ring
    rw [hdiff, abs_of_nonneg (div_nonneg (by norm_num) hm0), mul_one_div_cancel hmpos.ne'] at h
    exact h
  obtain ⟨code, hcode⟩ := exists_phaseWalkCode_of_real_path v hvroot hvstep
  refine ⟨code, fun t ht ↦ ?_⟩
  let n : ℕ := ⌊(m : ℝ) * t⌋₊
  have hmt : 0 ≤ (m : ℝ) * t := mul_nonneg hm0 ht.1
  have hnlow : (n : ℝ) ≤ (m : ℝ) * t := Nat.floor_le hmt
  have hnup : (m : ℝ) * t < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hnle : n ≤ m := by
    have h := hnlow.trans (mul_le_mul_of_nonneg_left ht.2 hm0)
    have hnm : (n : ℝ) ≤ (m : ℝ) := by simpa only [mul_one] using h
    exact_mod_cast hnm
  let j : Fin (m + 1) := ⟨n, Nat.lt_succ_of_le hnle⟩
  have hnear : ‖γ t - v j‖ ≤ 1 := by
    have h := hLip t ht _ (htime j)
    have hnonneg : 0 ≤ t - (n : ℝ) / (m : ℝ) :=
      sub_nonneg.mpr ((div_le_iff₀ hmpos).mpr (by simpa only [mul_comm] using hnlow))
    change ‖γ t - v j‖ ≤ (m : ℝ) * |t - (n : ℝ) / (m : ℝ)| at h
    rw [abs_of_nonneg hnonneg] at h
    have heq : (m : ℝ) * (t - (n : ℝ) / (m : ℝ)) = (m : ℝ) * t - (n : ℝ) := by
      field_simp
    rw [heq] at h
    exact h.trans (by linarith)
  refine ⟨j, ?_⟩
  calc
    _ ≤ ‖γ t - v j‖ + ‖v j - phaseWalkVertex code j‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 1 + 1 := add_le_add hnear (hcode j)
    _ = 2 := by norm_num

end OTSelector.Reconstruction

end
end
