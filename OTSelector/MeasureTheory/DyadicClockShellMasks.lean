import OTSelector.MeasureTheory.DyadicClockCells
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.DyadicClockShellMasks.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.DyadicClockShellMasks`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.DyadicClockShellMasks

Conditions: Positive collar scale for the shell partition identities; unrestricted real scales suffice for measurability and the pointwise indicator bound.
Objects: Half-open dyadic shell indicators and their arbitrary nonnegative extended-real weights.
Proof detail: Use the unique dyadic shell containing each positive collar point, prove pairwise disjointness, and collapse the countable indicator sum to the whole collar indicator.

## Mathematical sources

- OT-Selector project, *Empirical optimal transport selection on general Finsler manifolds, main.tex*: Subsection subsec:focal-traffic, proof of thm:focal-full-path-traffic; Births comparable to the focal time, between eq:focal-traffic-old-bound and eq:focal-traffic-birth-large. ../main.tex#L9624

Source relation: Exact indicator algebra for the manuscript’s dyadic endpoint decomposition. The Ioc convention and arbitrary pointwise weights are implementation adapters, with no stochastic independence assertion.
-/

/-! # Exact single-shell masks for old physical inward clocks -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- A single physical inward-clock shell, with the same exact endpoint convention. -/
def dyadicClockShellMask (ε : ℝ) (n : ℕ) : ℝ → ℝ≥0∞ :=
  (Ioc (birthDyadicShellScale ε n) (2 * birthDyadicShellScale ε n)).indicator 1

theorem measurable_dyadicClockShellMask (ε : ℝ) (n : ℕ) :
    Measurable (dyadicClockShellMask ε n) := measurable_const.indicator measurableSet_Ioc

theorem birthDyadicShell_subset_Ioc {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    Ioc (birthDyadicShellScale ε n) (2 * birthDyadicShellScale ε n) ⊆ Ioc 0 ε := by
  intro x hx
  have hupper : 2 * birthDyadicShellScale ε n ≤ ε := by
    rw [two_mul_birthDyadicShellScale]
    exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  exact ⟨(birthDyadicShellScale_pos hε n).trans hx.1, hx.2.trans hupper⟩

theorem pairwise_disjoint_birthDyadicShell {ε : ℝ} (hε : 0 < ε) :
    Pairwise (fun n m : ℕ ↦ Disjoint
      (Ioc (birthDyadicShellScale ε n) (2 * birthDyadicShellScale ε n))
      (Ioc (birthDyadicShellScale ε m) (2 * birthDyadicShellScale ε m))) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro x hn hm
  have hx := birthDyadicShell_subset_Ioc hε n hn
  obtain ⟨i, hi, huniq⟩ := existsUnique_birthDyadicShell hε hx.1 hx.2
  exact hnm ((huniq n hn).trans (huniq m hm).symm)

theorem dyadicClockShellMask_le_one (ε : ℝ) (n : ℕ) (x : ℝ) :
    dyadicClockShellMask ε n x ≤ 1 := by
  classical
  by_cases h : x ∈ Ioc (birthDyadicShellScale ε n) (2 * birthDyadicShellScale ε n)
  <;> simp [dyadicClockShellMask, h]

/-- Single-shell masks sum exactly to the whole physical inward collar indicator. -/
theorem tsum_dyadicClockShellMask {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    (∑' n : ℕ, dyadicClockShellMask ε n x) = (Ioc (0 : ℝ) ε).indicator 1 x := by
  classical
  by_cases hx : x ∈ Ioc 0 ε
  · obtain ⟨n, hn, huniq⟩ := existsUnique_birthDyadicShell hε hx.1 hx.2
    have hmem (m : ℕ) :
        x ∈ Ioc (birthDyadicShellScale ε m) (2 * birthDyadicShellScale ε m) ↔ m = n :=
      ⟨huniq m, fun h ↦ h ▸ hn⟩
    simp [dyadicClockShellMask, indicator_apply, hmem, hx]
  · have hnot (n : ℕ) :
        x ∉ Ioc (birthDyadicShellScale ε n) (2 * birthDyadicShellScale ε n) :=
      fun hn ↦ hx (birthDyadicShell_subset_Ioc hε n hn)
    simp [dyadicClockShellMask, hnot, hx]

theorem tsum_weighted_dyadicClockShellMask {ε : ℝ} (hε : 0 < ε)
    (θ : ℝ → ℝ≥0∞) (x : ℝ) :
    (∑' n : ℕ, θ x * dyadicClockShellMask ε n x) =
      θ x * (Ioc (0 : ℝ) ε).indicator 1 x := by
  rw [ENNReal.tsum_mul_left, tsum_dyadicClockShellMask hε]

end OTSelector.Reconstruction

end
end
