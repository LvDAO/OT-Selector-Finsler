import OTSelector.Reconstruction.FinslerOriginalFiniteIndexSelection
import OTSelector.Reconstruction.FinslerOriginalReserveRepairPalm

/-!
# Reserve cost comparison for the actual finite legal pressure

This module proves the feasibility half of the box limit: the actual finite
legal minimum value at fixed colored counts is at most the retained core tilted
value plus the explicit reserve budget, and hence so is its expectation over the
unchanged independent marked-cloud law.

1. **Pointwise reserve cost comparison.**  The finite legal maximum-cardinality
   minimum at fixed counts m, n is bounded by the tilted value of any feasible
   maximum-cardinality legal matching.  The measurable reserve-repair completion
   of the retained core is such a matching, so
   legalMarkedFixedValue <= core.cost + (m - core.card) * B
   with the uniform edge bound B = r^(2/q)(C q) + |t| G
   (legalMarkedFixedValue_le_core_add_reserve).  This is the direction in which
   the legal minimum is compared with the reserve comparator.

2. **Expectation over the marked-cloud law.**  Integrating the pointwise
   comparison over the unchanged independent marked-cloud law gives
   E[legalMarkedFixedValue] <= E[core.cost] + m * B
   (integral_legalMarkedFixedValue_le_core_add_reserve).

## Remaining gap

The box limit has two remaining identifications: (i) the normalized fixed-count
legal expectations converge to the legal pressure limit p_A(t), and (ii) the
retained core expectation at the dilated tilt equals
(1-rho)^(1-2/q) I_w(t (1-rho)^(2/q)) up to boundary losses.  With these, the
comparison above becomes FiniteValueComparisonWithReserveCost and yields
I_w = I_2.  The finite-sample feasibility comparison and its expectation are
proved here.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped BigOperators Topology ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Probability

set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {α : Measure A} [IsProbabilityMeasure α] {β : Measure B} [IsProbabilityMeasure β]

/-- The uniform tilted edge bound of the marked cloud at intensity r. -/
def markedEdgeBound (q : ℕ) (r C G : ℝ) : ℝ :=
  r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + G

/-- **Pointwise reserve cost comparison for the actual finite legal value.**
Under the exact residual-capacity identity, the finite legal maximum-cardinality
minimum at fixed colored counts is at most the retained core tilted value plus
the explicit reserve budget (m - core.card) times the uniform edge bound. -/
theorem legalMarkedFixedValue_le_core_add_reserve
    (q m n : ℕ)
    (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (hsource : Measurable sourceClock) (htarget : Measurable targetClock)
    (core : TwoMarkedCloudSpace q A B → OTSelector.PartialMatching m n)
    (hcore_meas : ∀ S : OTSelector.PartialMatching m n,
      MeasurableSet {ω | core ω = S})
    (hcore_legal : ∀ ω, PartialMatching.IsLegal
      (legalMarkedGraph q m n sourceClock targetClock ω) (core ω))
    (hcapacity : ∀ ω, (core ω).card + PartialMatching.legalMaximumCard
      (PartialMatching.residualAllowed
        (legalMarkedGraph q m n sourceClock targetClock ω) (core ω)) =
        PartialMatching.legalMaximumCard
          (legalMarkedGraph q m n sourceClock targetClock ω))
    {r C G : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ}
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    ∃ τ : TwoMarkedCloudSpace q A B → OTSelector.PartialMatching m n,
      (∀ S : OTSelector.PartialMatching m n, MeasurableSet {ω | τ ω = S}) ∧
      (∀ ω, PartialMatching.IsLegal
          (legalMarkedGraph q m n sourceClock targetClock ω) (τ ω) ∧
        (τ ω).card = PartialMatching.legalMaximumCard
          (legalMarkedGraph q m n sourceClock targetClock ω) ∧
        (core ω).edges ⊆ (τ ω).edges) ∧
      ∀ ω, legalMarkedFixedValue q m n sourceClock targetClock r kin g t ω ≤
        OTSelector.PartialMatching.cost
          (markedTiltedEdgeCost q r kin g t ω) (core ω) +
          ((m - (core ω).card : ℕ) : ℝ) *
            (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) := by
  classical
  obtain ⟨τ, hτmeas, hτ⟩ := OTSelector.Reconstruction.PartialMatching.exists_measurable_legal_completion
    (m := m) (n := n)
    (fun ω => legalMarkedGraph q m n sourceClock targetClock ω)
    (fun E => measurableSet_legalMarkedGraph_eq q m n hsource htarget E)
    core hcore_meas hcore_legal hcapacity
  refine ⟨τ, hτmeas, hτ, ?_⟩
  have hB0 : 0 ≤ r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G := by
    have h1 : 0 ≤ r ^ (2 / (q : ℝ)) := Real.rpow_nonneg hr _
    have h2 : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
    have h3 : 0 ≤ C * (q : ℝ) := mul_nonneg hC h2
    have h4 : 0 ≤ |t| * G := mul_nonneg (abs_nonneg t) hG
    exact add_nonneg (mul_nonneg h1 h3) h4
  intro ω
  obtain ⟨hlegal, hcard, hsub⟩ := hτ ω
  have hmin : legalMarkedFixedValue q m n sourceClock targetClock r kin g t ω ≤
      OTSelector.PartialMatching.cost
        (markedTiltedEdgeCost q r kin g t ω) (τ ω) :=
    PartialMatching.legalMaximumValue_le
      (markedTiltedEdgeCost q r kin g t ω) hlegal hcard
  have hsplit : OTSelector.PartialMatching.cost
      (markedTiltedEdgeCost q r kin g t ω) (τ ω) =
      OTSelector.PartialMatching.cost
        (markedTiltedEdgeCost q r kin g t ω) (core ω) +
      ∑ e ∈ ((τ ω).edges \ (core ω).edges),
        markedTiltedEdgeCost q r kin g t ω e.1 e.2 :=
    PartialMatching.cost_eq_add_cost_sdiff hsub (markedTiltedEdgeCost q r kin g t ω)
  have hb : ∀ (i : Fin m) (j : Fin n), markedTiltedEdgeCost q r kin g t ω i j ≤
      r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G := by
    intro i j
    have h := abs_legalMarkedEdge_le q hr hC hkin_bound hgb t ω (i : ℕ) (j : ℕ)
    exact (abs_le.mp h).2
  have hadded : ∑ e ∈ ((τ ω).edges \ (core ω).edges),
      markedTiltedEdgeCost q r kin g t ω e.1 e.2 ≤
      (((τ ω).edges \ (core ω).edges).card : ℝ) *
        (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) :=
    PartialMatching.cost_le_card_mul (markedTiltedEdgeCost q r kin g t ω)
      { edges := (τ ω).edges \ (core ω).edges
        row_inj := fun e he e' he' hrow =>
          (τ ω).row_inj e (Finset.mem_sdiff.mp he).1 e'
            (Finset.mem_sdiff.mp he').1 hrow
        col_inj := fun e he e' he' hcol =>
          (τ ω).col_inj e (Finset.mem_sdiff.mp he).1 e'
            (Finset.mem_sdiff.mp he').1 hcol }
      hb
  have hcount : ((τ ω).edges \ (core ω).edges).card =
      PartialMatching.legalMaximumCard
        (legalMarkedGraph q m n sourceClock targetClock ω) - (core ω).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
    change (τ ω).card - (core ω).card = _
    rw [hcard]
  have hle : ((PartialMatching.legalMaximumCard
        (legalMarkedGraph q m n sourceClock targetClock ω) - (core ω).card : ℕ) : ℝ) ≤
      ((m - (core ω).card : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le_sub_right
      (PartialMatching.legalMaximumCard_le_min
        (legalMarkedGraph q m n sourceClock targetClock ω) |>.trans (min_le_left m n))
      ((core ω).card)
  have hbudget : ∑ e ∈ ((τ ω).edges \ (core ω).edges),
      markedTiltedEdgeCost q r kin g t ω e.1 e.2 ≤
      ((m - (core ω).card : ℕ) : ℝ) *
        (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) := by
    refine hadded.trans ?_
    rw [hcount]
    exact mul_le_mul_of_nonneg_right hle hB0
  rw [hsplit] at hmin
  linarith

/-- **Expectation form of the reserve cost comparison for the actual finite legal
value.**  Over the unchanged independent marked-cloud law, the expected finite
legal value at fixed colored counts is at most the expected retained core tilted
value plus the explicit reserve budget m times the uniform edge bound. -/
theorem integral_legalMarkedFixedValue_le_core_add_reserve
    (q m n : ℕ)
    (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (hsource : Measurable sourceClock) (htarget : Measurable targetClock)
    (core : TwoMarkedCloudSpace q A B → OTSelector.PartialMatching m n)
    (hcore_meas : ∀ S : OTSelector.PartialMatching m n,
      MeasurableSet {ω | core ω = S})
    (hcore_legal : ∀ ω, PartialMatching.IsLegal
      (legalMarkedGraph q m n sourceClock targetClock ω) (core ω))
    (hcapacity : ∀ ω, (core ω).card + PartialMatching.legalMaximumCard
      (PartialMatching.residualAllowed
        (legalMarkedGraph q m n sourceClock targetClock ω) (core ω)) =
        PartialMatching.legalMaximumCard
          (legalMarkedGraph q m n sourceClock targetClock ω))
    {r C G : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ}
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) (rr : ℝ≥0)
    (hI : Integrable (fun ω => legalMarkedFixedValue q m n sourceClock
      targetClock r kin g t ω) (twoMarkedCloudLaw (q := q) A B α β rr))
    (hcI : Integrable (fun ω => OTSelector.PartialMatching.cost
      (markedTiltedEdgeCost q r kin g t ω) (core ω))
      (twoMarkedCloudLaw (q := q) A B α β rr)) :
    (∫ ω, legalMarkedFixedValue q m n sourceClock targetClock r kin g t ω
        ∂(twoMarkedCloudLaw (q := q) A B α β rr)) ≤
      (∫ ω, OTSelector.PartialMatching.cost
        (markedTiltedEdgeCost q r kin g t ω) (core ω)
        ∂(twoMarkedCloudLaw (q := q) A B α β rr)) +
        (m : ℝ) * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) := by
  classical
  obtain ⟨τ, hτmeas, hτ, hbound⟩ :=
    legalMarkedFixedValue_le_core_add_reserve q m n sourceClock targetClock
      hsource htarget core hcore_meas hcore_legal hcapacity hr hC hG hkin_bound
      hgb t
  have hB0 : 0 ≤ r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G := by
    have h1 : 0 ≤ r ^ (2 / (q : ℝ)) := Real.rpow_nonneg hr _
    have h2 : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
    have h3 : 0 ≤ C * (q : ℝ) := mul_nonneg hC h2
    have h4 : 0 ≤ |t| * G := mul_nonneg (abs_nonneg t) hG
    exact add_nonneg (mul_nonneg h1 h3) h4
  have hae : ∀ᵐ ω ∂(twoMarkedCloudLaw (q := q) A B α β rr),
      legalMarkedFixedValue q m n sourceClock targetClock r kin g t ω ≤
        OTSelector.PartialMatching.cost
          (markedTiltedEdgeCost q r kin g t ω) (core ω) +
          (m : ℝ) * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) := by
    filter_upwards with ω
    have h := hbound ω
    have hcard : ((m - (core ω).card : ℕ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast Nat.sub_le m ((core ω).card)
    have hmul := mul_le_mul_of_nonneg_right hcard hB0
    linarith
  exact OTSelector.Reconstruction.integral_le_add_of_ae_reserveBound
    (twoMarkedCloudLaw (q := q) A B α β rr) hcI hI hae

end OTSelector.Reconstruction
