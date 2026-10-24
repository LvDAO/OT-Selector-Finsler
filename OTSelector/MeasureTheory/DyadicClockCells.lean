import OTSelector.MeasureTheory.DyadicClockBandPartition
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.DyadicBirthClockCells.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.DyadicBirthClockCells`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.DyadicClockCells

## Lemma skeleton

* **Conditions:** A positive dyadic endpoint scale and positive inward/elapsed clocks inside the stated region.
* **Objects:** Unique dyadic shell and three-index cell membership, exact scales and region containment.
* **Proof detail:** Use successive powers of two to locate each positive value in one half-open shell, then use the elapsed scale and finite clock-grid partition for the narrow cell; prove uniqueness by disjoint endpoint order.

## Mathematical sources

- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean): Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.
- [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I](https://www.jirka.org/ra/realanal.pdf#page=31): Section 1.2.2, Theorem 1.2.4, p. 31.

Source relation (composition): Deterministic countable dyadic partition; no measure or stochastic selection assumption occurs.
-/

/-! # Exact disjoint dyadic inward/elapsed/narrow-clock cells -/
open Set MeasureTheory
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1000000

/-- Inward shell lower endpoint, with shells `(t_n, 2*t_n]` covering `(0, ε]`. -/
def birthDyadicShellScale (ε : ℝ) (n : ℕ) : ℝ := ε / (2 : ℝ) ^ (n + 1)

/-- Elapsed shell lower endpoint inside the inward shell. -/
def birthDyadicElapsedScale (ε : ℝ) (n j : ℕ) : ℝ :=
  birthDyadicShellScale ε n / (2 : ℝ) ^ j

theorem birthDyadicShellScale_pos {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    0 < birthDyadicShellScale ε n := by unfold birthDyadicShellScale; positivity

theorem two_mul_birthDyadicShellScale (ε : ℝ) (n : ℕ) :
    2 * birthDyadicShellScale ε n = ε / (2 : ℝ) ^ n := by
  unfold birthDyadicShellScale
  rw [pow_succ]
  field_simp

theorem birthDyadicShellScale_two_mul (t : ℝ) (j : ℕ) :
    birthDyadicShellScale (2 * t) j = t / (2 : ℝ) ^ j := by
  unfold birthDyadicShellScale
  rw [pow_succ]
  field_simp

/-- A later dyadic half-open shell lies below the earlier shell's lower endpoint. -/
theorem two_mul_birthDyadicShellScale_le_of_lt {ε : ℝ} (hε : 0 ≤ ε)
    {n m : ℕ} (hnm : n < m) :
    2 * birthDyadicShellScale ε m ≤ birthDyadicShellScale ε n := by
  rw [two_mul_birthDyadicShellScale, birthDyadicShellScale]
  exact div_le_div_of_nonneg_left hε (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.succ_le_of_lt hnm))

/-- Every strictly positive inward coordinate has exactly one half-open dyadic shell. -/
theorem existsUnique_birthDyadicShell {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x) (hxε : x ≤ ε) :
    ∃! n : ℕ, x ∈ Ioc (birthDyadicShellScale ε n) (2 * birthDyadicShellScale ε n) := by
  have hratio : 1 ≤ ε / x := (le_div_iff₀ hx).mpr (by simpa only [one_mul] using hxε)
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  have hnx : x ∈ Ioc (birthDyadicShellScale ε n) (2 * birthDyadicShellScale ε n) := by
    constructor
    · apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ (n + 1))).mpr
      simpa only [mul_comm] using (div_lt_iff₀ hx).mp hnhi
    · rw [two_mul_birthDyadicShellScale]
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mpr
      simpa only [mul_comm] using (le_div_iff₀ hx).mp hnlo
  refine ⟨n, hnx, ?_⟩
  intro m hmx
  by_contra hmn
  rcases lt_or_gt_of_ne hmn with hmn | hnm
  · have h := two_mul_birthDyadicShellScale_le_of_lt hε.le hmn
    linarith [hnx.2, hmx.1]
  · have h := two_mul_birthDyadicShellScale_le_of_lt hε.le hnm
    linarith [hmx.2, hnx.1]

/-- The strict-elapsed birth region in inward/elapsed coordinates. -/
def dyadicBirthClockRegion (ε : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 ≤ ε ∧ 0 < p.2 ∧ p.2 ≤ p.1}

/-- The index is `(inward shell, elapsed shell, narrow inward-clock band)`.
Invalid narrow-band indices give the empty cell. -/
def dyadicBirthClockCell (ε : ℝ) (k : ℕ × ℕ × ℕ) : Set (ℝ × ℝ) :=
  let t := birthDyadicShellScale ε k.1
  let s := birthDyadicElapsedScale ε k.1 k.2.1
  {p | p.1 ∈ Ioc t (2 * t) ∧ p.2 ∈ Ioc s (2 * s) ∧ p.2 ≤ p.1 ∧
    k.2.2 < dyadicBirthBandCount k.2.1 ∧
      p.1 ∈ clockGridBand t (s / 8) k.2.2}

theorem dyadicBirthClockCell_subset_region {ε : ℝ} (hε : 0 < ε) (k : ℕ × ℕ × ℕ) :
    dyadicBirthClockCell ε k ⊆ dyadicBirthClockRegion ε := by
  intro p hp
  have ht := birthDyadicShellScale_pos hε k.1
  have hs : 0 < birthDyadicElapsedScale ε k.1 k.2.1 := by
    unfold birthDyadicElapsedScale; positivity
  have hupper : 2 * birthDyadicShellScale ε k.1 ≤ ε := by
    rw [two_mul_birthDyadicShellScale]
    exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  exact ⟨ht.trans hp.1.1, hp.1.2.trans hupper, hs.trans hp.2.1.1, hp.2.2.1⟩

/-- The literal birth region has one and only one full triple index. -/
theorem existsUnique_dyadicBirthClockCell {ε : ℝ} (hε : 0 < ε)
    {p : ℝ × ℝ} (hp : p ∈ dyadicBirthClockRegion ε) :
    ∃! k : ℕ × ℕ × ℕ, p ∈ dyadicBirthClockCell ε k := by
  obtain ⟨n, hn, hnuniq⟩ := existsUnique_birthDyadicShell hε hp.1 hp.2.1
  let t := birthDyadicShellScale ε n
  have ht : 0 < t := birthDyadicShellScale_pos hε n
  obtain ⟨j, hj, hjuniq⟩ := existsUnique_birthDyadicShell (mul_pos (by norm_num) ht)
    hp.2.2.1 (hp.2.2.2.trans hn.2)
  have hscale : birthDyadicShellScale (2 * t) j = birthDyadicElapsedScale ε n j :=
    birthDyadicShellScale_two_mul t j
  rw [hscale] at hj
  have hcover := biUnion_dyadicBirthBands 0 ht j
  simp only [zero_add, (dyadicBirthBand_width_and_total ht j).2.1] at hcover
  have hband : p.1 ∈ ⋃ i ∈ Finset.range (dyadicBirthBandCount j),
      clockGridBand t (birthDyadicElapsedScale ε n j / 8) i := by
    change p.1 ∈ ⋃ i ∈ Finset.range (dyadicBirthBandCount j),
      clockGridBand t (t / (2 : ℝ) ^ j / 8) i
    rw [hcover]
    exact hn
  obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp hband
  refine ⟨(n, j, i), ⟨hn, hj, hp.2.2.2, Finset.mem_range.mp hi, hpi⟩, ?_⟩
  rintro ⟨n', j', i'⟩ hk
  have hnn : n' = n := hnuniq n' hk.1
  subst n'
  have hjj : j' = j := hjuniq j' (by
    change p.2 ∈ Ioc (birthDyadicShellScale (2 * t) j')
      (2 * birthDyadicShellScale (2 * t) j')
    rw [birthDyadicShellScale_two_mul]
    exact hk.2.1)
  subst j'
  have hii : i' = i := by
    by_contra hii
    exact Set.disjoint_left.mp
      (pairwise_disjoint_clockGridBand t (by
        unfold birthDyadicElapsedScale
        positivity) hii) hk.2.2.2.2 hpi
  subst i'
  rfl

end OTSelector.Reconstruction

end
end
