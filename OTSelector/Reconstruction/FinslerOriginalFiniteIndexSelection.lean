import OTSelector.Reconstruction.FinslerOriginalReserveRepairSelection
import OTSelector.Reconstruction.MarkedStationaryValueLegalCloud

/-!
# Finite-index selection on the actual marked-cloud legal graph and its value

This module instantiates the measurable reserve-repair selection on the actual
finite marked cloud, where the legal graph, clocks, kinetic cost and probe are
the concrete measurable objects of the legal pressure, and proves the
finite-sample value comparison.

1. **Measurable selection on the actual finite legal graph.**  On the marked
   cloud space the legal graph omega -> legalMarkedGraph q m n sourceClock
   targetClock omega is finite-valued and measurable, and the tilted edge cost
   mKineticCost + t * mProbe is measurable and uniformly bounded by
   r^(2/q) (C q) + |t| G.  The measurable reserve-repair selection therefore
   produces, measurably in the cloud, a maximum-cardinality legal completion of
   any measurable retained core with the explicit added-cost bound
   (exists_measurable_legalMarkedCompletion).

2. **Finite-sample value comparison.**  Integrating the pointwise reserve bound
   over the actual independent marked-cloud law gives
   E[repaired tilted value] <= E[retained core tilted value]
     + m * (r^(2/q)(C q) + |t| G)
   (integral_legalMarkedCompletion_le_core_add_reserve).  This is the
   finite-sample comparison with explicit reserve budget on the unchanged
   original independent inputs.

## Remaining gap

The box limit: identifying the normalized legal pressure limit with the
expectation of the repaired finite value (and the retained core expectation with
the dilated weighted stationary value), which turns the finite-sample comparison
above into FiniteValueComparisonWithReserveCost and hence I_w = I_2.
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

/-- The concrete tilted edge cost of the marked cloud on finite index edges. -/
def markedTiltedEdgeCost (q : ℕ) (r : ℝ) (kin : A → B → (Fin q → ℝ) → ℝ)
    (g : A → B → ℝ) (t : ℝ) {m n : ℕ}
    (ω : TwoMarkedCloudSpace q A B) (i : Fin m) (j : Fin n) : ℝ :=
  mKineticCost q r kin ω (i : ℕ) (j : ℕ) + t * mProbe g ω (i : ℕ) (j : ℕ)

/-- **Measurable reserve-repair selection on the actual finite legal graph.**
For the concrete legal graph of the marked cloud, any measurable retained core
which is legal and satisfies the exact residual-capacity identity extends
measurably to a maximum-cardinality legal completion, with explicit added tilted
cost at most (m - core.card) times the uniform edge bound
r^(2/q)(C q) + |t| G. -/
theorem exists_measurable_legalMarkedCompletion
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
    (hmaxcard : ∀ ω, PartialMatching.legalMaximumCard
      (legalMarkedGraph q m n sourceClock targetClock ω) = m)
    {r C G : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    ∃ τ : TwoMarkedCloudSpace q A B → OTSelector.PartialMatching m n,
      (∀ S : OTSelector.PartialMatching m n, MeasurableSet {ω | τ ω = S}) ∧
      (∀ ω, PartialMatching.IsLegal
          (legalMarkedGraph q m n sourceClock targetClock ω) (τ ω) ∧
        (τ ω).card = PartialMatching.legalMaximumCard
          (legalMarkedGraph q m n sourceClock targetClock ω) ∧
        (core ω).edges ⊆ (τ ω).edges) ∧
      Measurable (fun ω => OTSelector.PartialMatching.cost
        (markedTiltedEdgeCost q r kin g t ω) (τ ω)) ∧
      ∀ ω, OTSelector.PartialMatching.cost
          (markedTiltedEdgeCost q r kin g t ω) (τ ω) ≤
        OTSelector.PartialMatching.cost
          (markedTiltedEdgeCost q r kin g t ω) (core ω) +
          ((m - (core ω).card : ℕ) : ℝ) *
            (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) := by
  classical
  refine OTSelector.Reconstruction.PartialMatching.exists_measurable_legal_completion_with_cost
    (m := m) (n := n)
    (fun ω => legalMarkedGraph q m n sourceClock targetClock ω)
    (fun E => measurableSet_legalMarkedGraph_eq q m n hsource htarget E)
    core hcore_meas hcore_legal hcapacity hmaxcard
    (fun ω i j => markedTiltedEdgeCost q r kin g t ω i j) ?_
    (B := r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) ?_
  · intro i j
    exact (measurable_mKineticCost q r hkin (i : ℕ) (j : ℕ)).add
      ((measurable_mProbe q hg (i : ℕ) (j : ℕ)).const_mul t)
  · intro ω i j
    exact (abs_le.mp
      (abs_legalMarkedEdge_le q hr hC hkin_bound hgb t ω (i : ℕ) (j : ℕ))).2

/-- **Finite-sample value comparison with explicit reserve budget.**  For the
actual independent marked-cloud law, the expected tilted value of any measurable
maximum-cardinality completion satisfying the pointwise reserve bound is at most
the expected tilted value of the retained core plus the explicit reserve budget
m * (r^(2/q)(C q) + |t| G). -/
theorem integral_legalMarkedCompletion_le_core_add_reserve
    (q m n : ℕ)
    (core : TwoMarkedCloudSpace q A B → OTSelector.PartialMatching m n)
    (τ : TwoMarkedCloudSpace q A B → OTSelector.PartialMatching m n)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (rr : ℝ≥0)
    {r C G : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hrep : Integrable (fun ω => OTSelector.PartialMatching.cost
      (markedTiltedEdgeCost q r kin g t ω) (τ ω))
      (twoMarkedCloudLaw (q := q) A B α β rr))
    (hcore : Integrable (fun ω => OTSelector.PartialMatching.cost
      (markedTiltedEdgeCost q r kin g t ω) (core ω))
      (twoMarkedCloudLaw (q := q) A B α β rr))
    (hpointwise : ∀ ω, OTSelector.PartialMatching.cost
        (markedTiltedEdgeCost q r kin g t ω) (τ ω) ≤
      OTSelector.PartialMatching.cost
        (markedTiltedEdgeCost q r kin g t ω) (core ω) +
        ((m - (core ω).card : ℕ) : ℝ) *
          (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G)) :
    (∫ ω, OTSelector.PartialMatching.cost
        (markedTiltedEdgeCost q r kin g t ω) (τ ω)
        ∂(twoMarkedCloudLaw (q := q) A B α β rr)) ≤
      (∫ ω, OTSelector.PartialMatching.cost
        (markedTiltedEdgeCost q r kin g t ω) (core ω)
        ∂(twoMarkedCloudLaw (q := q) A B α β rr)) +
        (m : ℝ) * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) := by
  have hB0 : 0 ≤ r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G := by
    have h1 : 0 ≤ r ^ (2 / (q : ℝ)) := Real.rpow_nonneg hr _
    have h2 : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
    have h3 : 0 ≤ C * (q : ℝ) := mul_nonneg hC h2
    have h4 : 0 ≤ |t| * G := mul_nonneg (abs_nonneg t) hG
    exact add_nonneg (mul_nonneg h1 h3) h4
  have hae : ∀ᵐ ω ∂(twoMarkedCloudLaw (q := q) A B α β rr),
      OTSelector.PartialMatching.cost (markedTiltedEdgeCost q r kin g t ω) (τ ω) ≤
        OTSelector.PartialMatching.cost (markedTiltedEdgeCost q r kin g t ω) (core ω) +
          (m : ℝ) * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) := by
    filter_upwards with ω
    have h := hpointwise ω
    have hcard : ((m - (core ω).card : ℕ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast Nat.sub_le m ((core ω).card)
    have hmul := mul_le_mul_of_nonneg_right hcard hB0
    linarith
  exact OTSelector.Reconstruction.integral_le_add_of_ae_reserveBound
    (twoMarkedCloudLaw (q := q) A B α β rr) hcore hrep hae

end OTSelector.Reconstruction
