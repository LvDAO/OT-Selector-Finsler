import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Transport.CyclicMonotonicity.ClockTwoCycleExhaustion

## Lemma skeleton

* **Conditions:** An increasing countable exhaustion of the edge space and zero mass for every positive rational-scale legal two-cycle improvement event.

* **Objects:** Almost-everywhere two-cycle cost monotonicity, including a parameterized plan-law version.

* **Proof detail:** Any strict legal violation has positive clock gaps and positive gain, so some reciprocal-natural thresholds and one exhaustion index detect it. Take a countable union of the null events and unpack the cost inequality.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106): Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf): Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini).
- [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf): Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing.

Source relation (composition): A local countable-exhaustion argument; no continuity of cost/support and no general optimal-transport uniqueness theorem is imported.
-/

/-! A countable family of local improvement events detects every legal
two-cycle violation. This uses only the original cost and clock; continuity
of the cost or support is unnecessary for this measure-level conclusion. -/

open Set MeasureTheory
noncomputable section
namespace OTSelector.Probability

variable {X : Type*}

/-- All original and exchanged edges have a prescribed positive clock gap. -/
def clockTwoCycleLegal (clock : X → ℝ) (gap : ℝ) : Set ((X × X) × (X × X)) :=
  {p | gap < clock p.1.2 - clock p.1.1 ∧
    gap < clock p.2.2 - clock p.2.1 ∧
    gap < clock p.2.2 - clock p.1.1 ∧
    gap < clock p.1.2 - clock p.2.1}

/-- Positive gain means that exchanging the two original partners decreases
the cost. The same cost is evaluated on all four endpoint pairs. -/
def clockTwoCycleGain (cost : X → X → ℝ) (p : (X × X) × (X × X)) : ℝ :=
  cost p.1.1 p.1.2 + cost p.2.1 p.2.2 - cost p.1.1 p.2.2 - cost p.2.1 p.1.2

/-- A local two-edge improvement witness at fixed clock and gain thresholds. -/
def clockTwoCycleImprovement (clock : X → ℝ) (cost : X → X → ℝ)
    (K : Set (X × X)) (gap accuracy : ℝ) : Set ((X × X) × (X × X)) :=
  {p | p.1 ∈ K ∧ p.2 ∈ K ∧ p ∈ clockTwoCycleLegal clock gap ∧
    accuracy < clockTwoCycleGain cost p}

theorem clockTwoCycleImprovement_subset_prod
    (clock : X → ℝ) (cost : X → X → ℝ) (K : Set (X × X)) (gap accuracy : ℝ) :
    clockTwoCycleImprovement clock cost K gap accuracy ⊆ K ×ˢ K :=
  fun _ h ↦ ⟨h.1, h.2.1⟩

variable [MeasurableSpace X]

/-- Exhausting the edge space and both positive thresholds gives one
almost-everywhere event excluding every strictly legal improvement. The measure
may be any original joint two-edge law. -/
theorem ae_clockTwoCycleGain_nonpos_of_exhaustion
    (ρ : Measure ((X × X) × (X × X))) (clock : X → ℝ) (cost : X → X → ℝ)
    (K : ℕ → Set (X × X)) (hmono : Monotone K)
    (hcover : ∀ e, ∃ n, e ∈ K n)
    (hnull : ∀ n k m : ℕ, ρ (clockTwoCycleImprovement clock cost (K n)
      (1 / ((k : ℝ) + 1)) (1 / ((m : ℝ) + 1))) = 0) :
    ∀ᵐ p ∂ρ, p ∈ clockTwoCycleLegal clock 0 → clockTwoCycleGain cost p ≤ 0 := by
  have hall : ∀ᵐ p ∂ρ, ∀ n k m : ℕ,
      p ∉ clockTwoCycleImprovement clock cost (K n)
        (1 / ((k : ℝ) + 1)) (1 / ((m : ℝ) + 1)) :=
    ae_all_iff.mpr fun n ↦ ae_all_iff.mpr fun k ↦ ae_all_iff.mpr fun m ↦
      measure_eq_zero_iff_ae_notMem.mp (hnull n k m)
  filter_upwards [hall] with p hp
  intro hlegal
  by_contra hbad
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (lt_of_not_ge hbad)
  simp only [clockTwoCycleLegal, mem_ofPred_eq] at hlegal
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt
    (lt_min hlegal.1 (lt_min hlegal.2.1 (lt_min hlegal.2.2.1 hlegal.2.2.2)))
  have hscreen : p ∈ clockTwoCycleLegal clock (1 / ((k : ℝ) + 1)) :=
    ⟨hk.trans_le (min_le_left _ _),
      hk.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
      hk.trans_le ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))),
      hk.trans_le ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))⟩
  obtain ⟨n₀, hn₀⟩ := hcover p.1
  obtain ⟨n₁, hn₁⟩ := hcover p.2
  exact hp (max n₀ n₁) k m
    ⟨hmono (Nat.le_max_left _ _) hn₀, hmono (Nat.le_max_right _ _) hn₁, hscreen, hm⟩

/-- Applied to the product of the same full plan, the countable local null
events imply the original cost inequality for almost every legal pair. -/
theorem ae_twoCycle_cost_le_of_clock_improvement_null
    (π : Measure (X × X)) (clock : X → ℝ) (cost : X → X → ℝ)
    (K : ℕ → Set (X × X)) (hmono : Monotone K)
    (hcover : ∀ e, ∃ n, e ∈ K n)
    (hnull : ∀ n k m : ℕ, (π.prod π) (clockTwoCycleImprovement clock cost (K n)
      (1 / ((k : ℝ) + 1)) (1 / ((m : ℝ) + 1))) = 0) :
    ∀ᵐ p ∂π.prod π,
      (clock p.1.1 < clock p.1.2 ∧ clock p.2.1 < clock p.2.2 ∧
        clock p.1.1 < clock p.2.2 ∧ clock p.2.1 < clock p.1.2) →
      cost p.1.1 p.1.2 + cost p.2.1 p.2.2 ≤
        cost p.1.1 p.2.2 + cost p.2.1 p.1.2 := by
  filter_upwards [ae_clockTwoCycleGain_nonpos_of_exhaustion
    (π.prod π) clock cost K hmono hcover hnull] with p hp
  intro hclock
  have hlegal : p ∈ clockTwoCycleLegal clock 0 :=
    ⟨sub_pos.mpr hclock.1, sub_pos.mpr hclock.2.1,
      sub_pos.mpr hclock.2.2.1, sub_pos.mpr hclock.2.2.2⟩
  have h := hp hlegal
  dsimp only [clockTwoCycleGain] at h
  linarith

/-- All countably many witness nullness statements may be proved separately
on one fixed scene law. They then hold simultaneously and exclude legal
two-cycle improvements for the full plan of almost every scene. -/
theorem ae_ae_twoCycle_cost_le_of_clock_improvement_null
    {S : Type*} [MeasurableSpace S] (R : Measure S)
    (plan : S → Measure (X × X)) (clock : X → ℝ) (cost : S → X → X → ℝ)
    (K : ℕ → Set (X × X)) (hmono : Monotone K)
    (hcover : ∀ e, ∃ n, e ∈ K n)
    (hnull : ∀ n k m : ℕ, ∀ᵐ s ∂R,
      ((plan s).prod (plan s)) (clockTwoCycleImprovement clock (cost s) (K n)
        (1 / ((k : ℝ) + 1)) (1 / ((m : ℝ) + 1))) = 0) :
    ∀ᵐ s ∂R, ∀ᵐ p ∂(plan s).prod (plan s),
      (clock p.1.1 < clock p.1.2 ∧ clock p.2.1 < clock p.2.2 ∧
        clock p.1.1 < clock p.2.2 ∧ clock p.2.1 < clock p.1.2) →
      cost s p.1.1 p.1.2 + cost s p.2.1 p.2.2 ≤
        cost s p.1.1 p.2.2 + cost s p.2.1 p.1.2 := by
  have hall : ∀ᵐ s ∂R, ∀ n k m : ℕ,
      ((plan s).prod (plan s)) (clockTwoCycleImprovement clock (cost s) (K n)
        (1 / ((k : ℝ) + 1)) (1 / ((m : ℝ) + 1))) = 0 :=
    ae_all_iff.mpr fun n ↦ ae_all_iff.mpr fun k ↦ ae_all_iff.mpr fun m ↦ hnull n k m
  filter_upwards [hall] with s hs
  exact ae_twoCycle_cost_le_of_clock_improvement_null (plan s) clock (cost s)
    K hmono hcover hs

end OTSelector.Probability
