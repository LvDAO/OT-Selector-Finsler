import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
# Grid level selection and the repair error term

The pressure block comparison is applied at block count `m` together with a
hierarchy depth `J` satisfying `m ≤ 2 ^ J ≤ 2 * m`.  This module constructs such
a `J` (`Nat.clog 2 m`) and records the asymptotics of the resulting error term
`Kq * (C + |t| * G) * (L ^ (2 - q / 2) + L ^ (-q / 2))`, which is continuous at
every positive scale and tends to zero at infinity when `q > 4`.
-/

open Filter
open scoped Topology

noncomputable section
namespace OTSelector.Probability

/-- Every positive block count `m` admits a hierarchy depth `J` with
`m ≤ 2 ^ J ≤ 2 * m`. -/
theorem exists_gridLevel (m : ℕ) (hm : 0 < m) :
    ∃ J : ℕ, m ≤ 2 ^ J ∧ 2 ^ J ≤ 2 * m := by
  by_cases hm1 : m = 1
  · exact ⟨0, by simp [hm1]⟩
  · have hm2 : 2 ≤ m := by omega
    have hJ1 : 1 ≤ Nat.clog 2 m := by
      by_contra h
      have h0 : Nat.clog 2 m = 0 := by omega
      have hmle : m ≤ 2 ^ (0 : ℕ) := by
        rw [← h0]
        exact Nat.le_pow_clog (by norm_num) m
      simp at hmle
      omega
    refine ⟨Nat.clog 2 m, Nat.le_pow_clog (by norm_num) m, ?_⟩
    have hlt : 2 ^ (Nat.clog 2 m - 1) < m := by
      have hiff := Nat.clog_le_iff_le_pow (b := 2) (by norm_num : 1 < 2)
        (x := m) (y := Nat.clog 2 m - 1)
      have hnot : ¬ Nat.clog 2 m ≤ Nat.clog 2 m - 1 := by omega
      by_contra hge
      exact hnot (hiff.mpr (le_of_not_gt hge))
    have hpow : 2 ^ Nat.clog 2 m = 2 * 2 ^ (Nat.clog 2 m - 1) := by
      conv_lhs => rw [show Nat.clog 2 m = Nat.clog 2 m - 1 + 1 by omega]
      rw [pow_succ']
    omega

/-- The error term produced by the grid repair bound at scale `L`. -/
noncomputable def gridRepairError (q : ℕ) (Kq C G t : ℝ) (L : ℝ) : ℝ :=
  Kq * (C + |t| * G) *
    (Real.rpow L (2 - (q : ℝ) / 2) + Real.rpow L (-((q : ℝ) / 2)))

/-- The repair error is continuous at every positive scale. -/
theorem continuousAt_gridRepairError (q : ℕ) (Kq C G t : ℝ) {L : ℝ} (hL : 0 < L) :
    ContinuousAt (gridRepairError q Kq C G t) L := by
  unfold gridRepairError
  have h1 : ContinuousAt (fun L : ℝ => Real.rpow L (2 - (q : ℝ) / 2)) L :=
    Real.continuousAt_rpow_const L (2 - (q : ℝ) / 2) (Or.inl hL.ne')
  have h2 : ContinuousAt (fun L : ℝ => Real.rpow L (-((q : ℝ) / 2))) L :=
    Real.continuousAt_rpow_const L (-((q : ℝ) / 2)) (Or.inl hL.ne')
  have h := (h1.add h2).const_mul (Kq * (C + |t| * G))
  simpa only [Pi.add_apply, mul_assoc] using h

/-- When `q > 4` the repair error vanishes at infinity. -/
theorem tendsto_gridRepairError_atTop {q : ℕ} (hq : 4 < q) (Kq C G t : ℝ) :
    Tendsto (gridRepairError q Kq C G t) atTop (𝓝 0) := by
  have hqR : (4 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h1 : Tendsto (fun L : ℝ => Real.rpow L (2 - (q : ℝ) / 2)) atTop (𝓝 0) := by
    have hpos : 0 < (q : ℝ) / 2 - 2 := by linarith
    have := tendsto_rpow_neg_atTop hpos
    refine this.congr fun L => ?_
    congr 1
    ring
  have h2 : Tendsto (fun L : ℝ => Real.rpow L (-((q : ℝ) / 2))) atTop (𝓝 0) := by
    have hpos : 0 < (q : ℝ) / 2 := by linarith
    exact tendsto_rpow_neg_atTop hpos
  have hsum := h1.add h2
  simp only [add_zero] at hsum
  unfold gridRepairError
  simpa only [mul_assoc, mul_zero] using hsum.const_mul (Kq * (C + |t| * G))

end OTSelector.Probability
