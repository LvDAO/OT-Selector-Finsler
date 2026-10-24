import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

/-! Integer uniform grids at a fixed microscopic scale. The original sample
size tends to infinity before the chosen microscopic side is varied. -/
open Filter
open scoped Topology
noncomputable section
namespace OTSelector.Probability

/-- Number of uniform grid intervals for original mass N and fixed microscopic
side L. Its physical mesh is the reciprocal integer. -/
def microscopicGridOrder (q : ℕ) (L N : ℝ) : ℕ := ⌈N ^ (1 / (q : ℝ)) / L⌉₊

def microscopicGridSide (q : ℕ) (L N : ℝ) : ℝ := (microscopicGridOrder q L N : ℝ)⁻¹

theorem microscopicGridOrder_pos (q : ℕ) {L N : ℝ} (hL : 0 < L) (hN : 0 < N) :
    0 < microscopicGridOrder q L N :=
  Nat.ceil_pos.mpr (div_pos (Real.rpow_pos_of_pos hN _) hL)

theorem microscopicGridSide_nonneg (q : ℕ) (L N : ℝ) :
    0 ≤ microscopicGridSide q L N := inv_nonneg.mpr (Nat.cast_nonneg _)

/-- Rounding up never enlarges the prescribed microscopic side. -/
theorem microscopicGrid_rescaled_side_le (q : ℕ) {L N : ℝ}
    (hL : 0 < L) (hN : 0 < N) :
    N ^ (1 / (q : ℝ)) * microscopicGridSide q L N ≤ L := by
  have hm : (0 : ℝ) < microscopicGridOrder q L N :=
    Nat.cast_pos.mpr (microscopicGridOrder_pos q hL hN)
  rw [microscopicGridSide, ← div_eq_mul_inv, div_le_iff₀ hm]
  have hc : N ^ (1 / (q : ℝ)) / L ≤ (microscopicGridOrder q L N : ℝ) := Nat.le_ceil _
  simpa only [mul_comm] using (div_le_iff₀ hL).mp hc

/-- The actual integer grid refines as the original sample mass diverges. -/
theorem tendsto_microscopicGridOrder {q : ℕ} (hq : 0 < q) {L : ℝ} (hL : 0 < L) :
    Tendsto (microscopicGridOrder q L) atTop atTop := by
  have he : (0 : ℝ) < 1 / (q : ℝ) := one_div_pos.mpr (by exact_mod_cast hq)
  exact tendsto_nat_ceil_atTop.comp ((tendsto_rpow_atTop he).atTop_div_const hL)

theorem tendsto_microscopicGridSide {q : ℕ} (hq : 0 < q) {L : ℝ} (hL : 0 < L) :
    Tendsto (microscopicGridSide q L) atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_microscopicGridOrder hq hL))

/-- Rounding to actual integer boxes preserves the chosen microscopic side. -/
theorem tendsto_microscopicGrid_rescaled_side {q : ℕ} (hq : 0 < q)
    {L : ℝ} (hL : 0 < L) :
    Tendsto (fun N : ℝ ↦ N ^ (1 / (q : ℝ)) * microscopicGridSide q L N)
      atTop (𝓝 L) := by
  have he : (0 : ℝ) < 1 / (q : ℝ) := one_div_pos.mpr (by exact_mod_cast hq)
  have hbase := (tendsto_rpow_atTop he).atTop_div_const hL
  have hr := (tendsto_nat_ceil_div_atTop (R := ℝ)).comp hbase
  have hinv := hr.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have h := hinv.const_mul L
  convert h using 1
  · funext N
    simp only [microscopicGridSide, microscopicGridOrder, Function.comp_def, inv_div]
    rw [← mul_div_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ hL.ne']
    exact (div_eq_mul_inv _ _).symm
  · simp

private theorem root_nat_pow {q : ℕ} (hq : 0 < q) {N : ℝ} (hN : 0 < N) :
    (N ^ (1 / (q : ℝ))) ^ q = N := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [one_div_mul_cancel hq0, Real.rpow_one]

private theorem root_sq (q : ℕ) {N : ℝ} (hN : 0 < N) :
    (N ^ (1 / (q : ℝ))) ^ 2 = N ^ (2 / (q : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
  congr 1
  ring

/-- Every positive original finite sample has count mass bounded at the same
fixed microscopic scale; this bound is independent of sample size. -/
theorem microscopicGrid_mass_le {q : ℕ} (hq : 0 < q) {L N : ℝ}
    (hL : 0 < L) (hN : 0 < N) : N * microscopicGridSide q L N ^ q ≤ L ^ q := by
  have hn : 0 ≤ N ^ (1 / (q : ℝ)) * microscopicGridSide q L N :=
    mul_nonneg (Real.rpow_pos_of_pos hN _).le (microscopicGridSide_nonneg q L N)
  have h := pow_le_pow_left₀ hn (microscopicGrid_rescaled_side_le q hL hN) q
  simpa only [mul_pow, root_nat_pow hq hN] using h

/-- The same rounded boxes also bound the true physical quadratic cost scale
uniformly over all positive original sample sizes. -/
theorem microscopicGrid_quadratic_le (q : ℕ) {L N : ℝ}
    (hL : 0 < L) (hN : 0 < N) :
    N ^ (2 / (q : ℝ)) * microscopicGridSide q L N ^ 2 ≤ L ^ 2 := by
  have hn : 0 ≤ N ^ (1 / (q : ℝ)) * microscopicGridSide q L N :=
    mul_nonneg (Real.rpow_pos_of_pos hN _).le (microscopicGridSide_nonneg q L N)
  have h := pow_le_pow_left₀ hn (microscopicGrid_rescaled_side_le q hL hN) 2
  simpa only [mul_pow, root_sq q hN] using h

/-- Original count intensity has a finite nonzero microscopic limit even
though the physical microbox shrinks to zero. -/
theorem tendsto_microscopicGrid_mass {q : ℕ} (hq : 0 < q) {L : ℝ} (hL : 0 < L) :
    Tendsto (fun N : ℝ ↦ N * microscopicGridSide q L N ^ q) atTop (𝓝 (L ^ q)) := by
  apply Tendsto.congr' _ ((tendsto_microscopicGrid_rescaled_side hq hL).pow q)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
  rw [mul_pow, root_nat_pow hq hN]

/-- The true quadratic physical prefactor converges to the square of the
microscopic side, separately from the original count density. -/
theorem tendsto_microscopicGrid_quadratic {q : ℕ} (hq : 0 < q) {L : ℝ} (hL : 0 < L) :
    Tendsto (fun N : ℝ ↦ N ^ (2 / (q : ℝ)) * microscopicGridSide q L N ^ 2)
      atTop (𝓝 (L ^ 2)) := by
  apply Tendsto.congr' _ ((tendsto_microscopicGrid_rescaled_side hq hL).pow 2)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
  rw [mul_pow, root_sq q hN]

/-- An actual frozen original density multiplies only the count intensity. -/
theorem tendsto_microscopicGrid_density_mass {q : ℕ} (hq : 0 < q)
    {L : ℝ} (hL : 0 < L) (density : ℝ) :
    Tendsto (fun N : ℝ ↦ N * density * microscopicGridSide q L N ^ q)
      atTop (𝓝 (density * L ^ q)) := by
  convert (tendsto_microscopicGrid_mass hq hL).const_mul density using 1
  funext N
  ring

end OTSelector.Probability
