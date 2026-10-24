import OTSelector.MeasureTheory.DyadicClockBandPartition
import OTSelector.MeasureTheory.DyadicClockCells
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.BirthFinitePhysicalClockWindows.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.BirthFinitePhysicalClockWindows`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.FiniteClockWindowPartition

Conditions: Positive cap and shell scales, explicit finite band membership and the interval inequalities in each theorem.
Objects: A scale-independent ceiling window count, equal physical widths, half-open masks and reference-clock separation bounds.
Proof detail: Use the Archimedean ceiling bound, partition the complete 9s/8 interval by a finite grid, then derive the displayed 7s/8 and 17s/8 reference bounds by endpoint arithmetic.

## Mathematical sources

- OT-Selector project, *Empirical optimal transport selection on general Finsler manifolds, main.tex*: Subsection subsec:focal-traffic, proof of thm:focal-full-path-traffic; Births comparable to the focal time, between eq:focal-traffic-old-bound and eq:focal-traffic-birth-large. ../main.tex#L9624

Source relation: The manuscript asks for a fixed finite number of relative windows; this code supplies one explicit ceiling construction and its constants. It is not a cited optimal-cover theorem.
-/

/-! A fixed finite physical-clock cover resolves every actual birth-band
window into the small windows required by the same Finsler geometry. The
number depends only on the fixed geometry fraction, not on either dyadic scale. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1200000

/-- The finite number of windows covers the full `9s/8` birth-clock interval. -/
def birthPhysicalClockWindowCount (cap : ℝ) : ℕ := Nat.ceil ((9 / 8 : ℝ) / cap)

def birthPhysicalClockWindowWidth (cap s : ℝ) : ℝ :=
  (9 / 8 : ℝ) * s / (birthPhysicalClockWindowCount cap : ℝ)

theorem birthPhysicalClockWindow_spec {cap s : ℝ} (hcap : 0 < cap) (hs : 0 < s) :
    0 < birthPhysicalClockWindowCount cap ∧
      0 < birthPhysicalClockWindowWidth cap s ∧
      birthPhysicalClockWindowWidth cap s ≤ cap * s ∧
      (birthPhysicalClockWindowCount cap : ℝ) * birthPhysicalClockWindowWidth cap s = 9 / 8 * s := by
  have hc : 0 < (9 / 8 : ℝ) / cap := div_pos (by norm_num) hcap
  have hN : 0 < birthPhysicalClockWindowCount cap := Nat.ceil_pos.mpr hc
  have hNr : (0 : ℝ) < birthPhysicalClockWindowCount cap := by exact_mod_cast hN
  have hceil : (9 / 8 : ℝ) / cap ≤ (birthPhysicalClockWindowCount cap : ℝ) := Nat.le_ceil _
  have hceil' : (9 / 8 : ℝ) ≤ (birthPhysicalClockWindowCount cap : ℝ) * cap :=
    (div_le_iff₀ hcap).mp hceil
  refine ⟨hN, div_pos (mul_pos (by norm_num) hs) hNr, ?_, ?_⟩
  · unfold birthPhysicalClockWindowWidth
    apply (div_le_iff₀ hNr).mpr
    nlinarith [mul_le_mul_of_nonneg_right hceil' hs.le]
  · unfold birthPhysicalClockWindowWidth
    exact mul_div_cancel₀ _ hNr.ne'

/-- Each finite physical window is a half-open original-clock interval. -/
def birthPhysicalClockWindowMask (cap base s : ℝ) (ell : ℕ) : ℝ → ℝ≥0∞ :=
  (clockGridBand base (birthPhysicalClockWindowWidth cap s) ell).indicator 1

theorem measurable_birthPhysicalClockWindowMask (cap base s : ℝ) (ell : ℕ) :
    Measurable (birthPhysicalClockWindowMask cap base s ell) :=
  measurable_const.indicator measurableSet_Ioc

theorem birthPhysicalClockWindowMask_le_one (cap base s : ℝ) (ell : ℕ) (x : ℝ) :
    birthPhysicalClockWindowMask cap base s ell x ≤ 1 := by
  classical
  by_cases hx : x ∈ clockGridBand base (birthPhysicalClockWindowWidth cap s) ell <;>
    simp [birthPhysicalClockWindowMask, hx]

/-- The finite window masks form an exact partition of the entire physical
birth interval. Endpoints are retained by the original Ioc convention. -/
theorem sum_birthPhysicalClockWindowMask {cap s : ℝ} (hcap : 0 < cap) (hs : 0 < s)
    (base x : ℝ) (hx : x ∈ Ioc base (base + 9 / 8 * s)) :
    (∑ ell ∈ Finset.range (birthPhysicalClockWindowCount cap),
      birthPhysicalClockWindowMask cap base s ell x) = 1 := by
  classical
  have hspec := birthPhysicalClockWindow_spec hcap hs
  have hcover := biUnion_clockGridBand base hspec.2.1.le (birthPhysicalClockWindowCount cap)
  rw [hspec.2.2.2] at hcover
  have hxU : x ∈ ⋃ ell ∈ Finset.range (birthPhysicalClockWindowCount cap),
      clockGridBand base (birthPhysicalClockWindowWidth cap s) ell := by rwa [hcover]
  obtain ⟨ell, hell, hxell⟩ := mem_iUnion₂.mp hxU
  rw [Finset.sum_eq_single ell]
  · exact indicator_of_mem hxell _
  · intro j _ hj
    have hjx : x ∉ clockGridBand base (birthPhysicalClockWindowWidth cap s) j := by
      intro hxj
      exact Set.disjoint_left.mp (pairwise_disjoint_clockGridBand base hspec.2.1.le hj) hxj hxell
    exact indicator_of_notMem hjx _
  · intro hn
    exact (hn hell).elim

/-- A real source/target birth cell puts the physical inward clock `y+d`
in a window of width exactly `9s/8`. -/
theorem birthClockCell_physical_clock_mem {u s y d : ℝ}
    (hy : y ∈ Ioc u (u + s / 8)) (hd : d ∈ Ioc s (2 * s)) :
    y + d ∈ Ioc (u + s) (u + s + 9 / 8 * s) := by
  constructor <;> linarith [hy.1, hy.2, hd.1, hd.2]

/-- The full finite physical subdivision retains any actual birth-cell
weight, with no change of source, target, physical clock or matching. -/
theorem sum_birthPhysicalClockWindowMask_on_cell {cap s u y d : ℝ}
    (hcap : 0 < cap) (hs : 0 < s)
    (hy : y ∈ Ioc u (u + s / 8)) (hd : d ∈ Ioc s (2 * s)) (θ : ℝ≥0∞) :
    (∑ ell ∈ Finset.range (birthPhysicalClockWindowCount cap),
      θ * birthPhysicalClockWindowMask cap (u + s) s ell (y + d)) = θ := by
  rw [← Finset.mul_sum, sum_birthPhysicalClockWindowMask hcap hs _ _
    (birthClockCell_physical_clock_mem hy hd), mul_one]

/-- Each starting reference clock remains uniformly separated from every
source/target endpoint in the same narrow band, at the original birth scale. -/
theorem birthPhysicalClockWindow_reference_elapsed_bounds {cap s u y : ℝ}
    (hcap : 0 < cap) (hs : 0 < s) (hy : y ∈ Ioc u (u + s / 8))
    {ell : ℕ} (hell : ell < birthPhysicalClockWindowCount cap) :
    7 / 8 * s ≤ (u + s + (ell : ℝ) * birthPhysicalClockWindowWidth cap s) - y ∧
      (u + s + (ell : ℝ) * birthPhysicalClockWindowWidth cap s) - y ≤ 17 / 8 * s := by
  have hspec := birthPhysicalClockWindow_spec hcap hs
  have he := clockGridBand_endpoints (u + s) hspec.2.1.le hell
  rw [hspec.2.2.2] at he
  have hwidth : 0 ≤ birthPhysicalClockWindowWidth cap s := hspec.2.1.le
  have hz : 0 ≤ (ell : ℝ) * birthPhysicalClockWindowWidth cap s := mul_nonneg (Nat.cast_nonneg _) hwidth
  constructor <;> nlinarith [hy.1, hy.2, he.1, he.2.1]

/-- Every finite closed physical window stays in the same actual endpoint
collar, including both endpoints used by the compact-clock producer. -/
theorem birthPhysicalClockWindow_inward_bounds {cap s u t : ℝ}
    (hcap : 0 < cap) (hs : 0 < s) (hst : s ≤ t)
    (hu : t ≤ u) (huend : u + s / 8 ≤ 2 * t)
    {ell : ℕ} (hell : ell < birthPhysicalClockWindowCount cap)
    {x : ℝ} (hx : x ∈ Icc
      (u + s + (ell : ℝ) * birthPhysicalClockWindowWidth cap s)
      (u + s + ((ell : ℝ) + 1) * birthPhysicalClockWindowWidth cap s)) :
    x ∈ Icc t (4 * t) := by
  have hspec := birthPhysicalClockWindow_spec hcap hs
  have he := clockGridBand_endpoints (u + s) hspec.2.1.le hell
  rw [hspec.2.2.2] at he
  constructor <;> linarith [hx.1, hx.2, he.1, he.2.1]

/-- The actual prescribed finite dyadic source/target band lies in its
original inward shell, with elapsed scale no larger than the shell scale. -/
theorem birthDyadicClockBand_base_bounds {ε : ℝ} (hε : 0 < ε) (n j i : ℕ)
    (hi : i < dyadicBirthBandCount j) :
    let t := birthDyadicShellScale ε n
    let s := birthDyadicElapsedScale ε n j
    let u := t + (i : ℝ) * (s / 8)
    0 < s ∧ s ≤ t ∧ t ≤ u ∧ u + s / 8 ≤ 2 * t := by
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  have ht : 0 < t := birthDyadicShellScale_pos hε n
  have hs : 0 < s := div_pos ht (by positivity)
  have hst : s ≤ t := div_le_self ht.le (one_le_pow₀ (by norm_num))
  have hwid := dyadicBirthBand_width_and_total ht j
  have he := clockGridBand_endpoints t hwid.1.le hi
  rw [hwid.2.2] at he
  rw [hwid.2.1] at he
  refine ⟨hs, hst, ?_, ?_⟩
  · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (by positivity))
  · dsimp [s, birthDyadicElapsedScale] at he ⊢
    linarith [he.2.1]

end OTSelector.Reconstruction

end
end
