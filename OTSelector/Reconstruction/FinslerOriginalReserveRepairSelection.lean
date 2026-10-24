import OTSelector.Reconstruction.FinslerOriginalCollarValueDensity
import OTSelector.Reconstruction.FinslerOriginalReserveRepairPalm

/-!
# Measurable reserve-repair selection and the a.e. reserve cost bound

This module proves the measurable selection of the reserve-repair completion and
the a.e. finite-sample reserve cost bound.

1. **Measurable selection of the maximum-cardinality legal completion.**
   The finite completion of FinslerOriginalCollarValueDensity exists scene by
   scene.  Since the legal graph and the retained core take only finitely many
   values, a canonical selection is obtained by choosing one completion on each
   of the finitely many measurable cells.  The resulting map is measurable into
   the finite type of partial matchings
   (exists_measurable_legal_completion) and preserves legality, maximum
   cardinality, the retained core and the explicit added-cost bound.

2. **Measurable repaired cost and the a.e. reserve bound.**  The repaired tilted
   cost of the selected completion is measurable
   (measurable cost clause of exists_measurable_legal_completion_with_cost), and
   wherever the reserve slack supplies the legal capacity it is at most the
   retained cost plus the explicit reserve budget (the number of added edges times
   the ambient edge bound B).  Combined with a probability law on the finite
   scenes this gives the expectation inequality
   (integral_le_add_of_ae_reserveBound), i.e. the a.e. finite-sample reserve cost
   bound integrated over the sample law.

## Remaining gap

The finite scene here is the index scene with clocks (Fin m, Fin n).  The
remaining steps are the measurable reindexing from the original Poisson scene and
the identification of the normalized legal pressure limit with the expectation of
the repaired finite value (the box limit), which together produce
FiniteValueComparisonWithReserveCost.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped BigOperators Topology ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

namespace PartialMatching

variable {m n : ℕ}

/-- **Measurable selection of the maximum-cardinality legal completion.**  If the
legal graph and the retained legal core are measurable finite-valued functions of
the scene, and the exact residual-capacity identity holds at every scene, then
there is a measurable selection of a full legal completion which keeps every
retained edge. -/
theorem exists_measurable_legal_completion
    {Ω : Type*} [MeasurableSpace Ω]
    (allowed : Ω → Finset (Fin m × Fin n))
    (hallowed : ∀ E : Finset (Fin m × Fin n), MeasurableSet {ω | allowed ω = E})
    (σ : Ω → PartialMatching m n)
    (hσ : ∀ S : PartialMatching m n, MeasurableSet {ω | σ ω = S})
    (hσlegal : ∀ ω, IsLegal (allowed ω) (σ ω))
    (hcapacity : ∀ ω, (σ ω).card +
      legalMaximumCard (residualAllowed (allowed ω) (σ ω)) = legalMaximumCard (allowed ω)) :
    ∃ τ : Ω → PartialMatching m n,
      (∀ T : PartialMatching m n, MeasurableSet {ω | τ ω = T}) ∧
      ∀ ω, IsLegal (allowed ω) (τ ω) ∧
        (τ ω).card = legalMaximumCard (allowed ω) ∧ (σ ω).edges ⊆ (τ ω).edges := by
  classical
  let Tfun : Finset (Fin m × Fin n) → PartialMatching m n → PartialMatching m n :=
    fun E S => if h : ∃ T : PartialMatching m n,
        IsLegal E T ∧ T.card = legalMaximumCard E ∧ S.edges ⊆ T.edges
      then Classical.choose h else S
  have hTfun : ∀ (E : Finset (Fin m × Fin n)) (S : PartialMatching m n),
      (∃ T : PartialMatching m n,
        IsLegal E T ∧ T.card = legalMaximumCard E ∧ S.edges ⊆ T.edges) →
      IsLegal E (Tfun E S) ∧ (Tfun E S).card = legalMaximumCard E ∧
        S.edges ⊆ (Tfun E S).edges := by
    intro E S hex
    simp only [Tfun]
    rw [dite_eq_left hex]
    exact Classical.choose_spec hex
  refine ⟨fun ω => Tfun (allowed ω) (σ ω), ?_, ?_⟩
  · intro T
    have hset : {ω | Tfun (allowed ω) (σ ω) = T} =
        ⋃ (p : Finset (Fin m × Fin n) × PartialMatching m n),
          {ω | allowed ω = p.1 ∧ σ ω = p.2 ∧ Tfun p.1 p.2 = T} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro h
        exact ⟨(allowed ω, σ ω), rfl, rfl, h⟩
      · rintro ⟨⟨E, S⟩, hE, hS, hTS⟩
        simpa only [hE, hS] using hTS
    rw [hset]
    refine MeasurableSet.iUnion fun p => ?_
    by_cases hTS : Tfun p.1 p.2 = T
    · rw [show {ω | allowed ω = p.1 ∧ σ ω = p.2 ∧ Tfun p.1 p.2 = T} =
          {ω | allowed ω = p.1 ∧ σ ω = p.2} from by
        ext ω
        simp only [Set.mem_ofPred_eq]
        tauto]
      exact (hallowed p.1).inter (hσ p.2)
    · rw [show {ω | allowed ω = p.1 ∧ σ ω = p.2 ∧ Tfun p.1 p.2 = T} = ∅ from by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
        tauto]
      exact MeasurableSet.empty
  · intro ω
    have hex : ∃ T : PartialMatching m n, IsLegal (allowed ω) T ∧
        T.card = legalMaximumCard (allowed ω) ∧ (σ ω).edges ⊆ T.edges := by
      have h := hcapacity ω
      exact (residual_capacity_iff_exists_legal_completion (σ ω) (hσlegal ω)).mp h
    exact hTfun (allowed ω) (σ ω) hex

/-- **The a.e. reserve cost bound for the measurable completion.**  If in addition
the legal maximum is the full source count and every edge cost is bounded by B,
the selected completion has added tilted cost at most the number of added edges
times B. -/
theorem exists_measurable_legal_completion_with_cost
    {Ω : Type*} [MeasurableSpace Ω]
    (allowed : Ω → Finset (Fin m × Fin n))
    (hallowed : ∀ E : Finset (Fin m × Fin n), MeasurableSet {ω | allowed ω = E})
    (σ : Ω → PartialMatching m n)
    (hσ : ∀ S : PartialMatching m n, MeasurableSet {ω | σ ω = S})
    (hσlegal : ∀ ω, IsLegal (allowed ω) (σ ω))
    (hcapacity : ∀ ω, (σ ω).card +
      legalMaximumCard (residualAllowed (allowed ω) (σ ω)) = legalMaximumCard (allowed ω))
    (hmax : ∀ ω, legalMaximumCard (allowed ω) = m)
    (cost : Ω → Fin m → Fin n → ℝ) (hcost : ∀ i j, Measurable (fun ω => cost ω i j))
    {B : ℝ} (hB : ∀ ω i j, cost ω i j ≤ B) :
    ∃ τ : Ω → PartialMatching m n,
      (∀ T : PartialMatching m n, MeasurableSet {ω | τ ω = T}) ∧
      (∀ ω, IsLegal (allowed ω) (τ ω) ∧
        (τ ω).card = legalMaximumCard (allowed ω) ∧ (σ ω).edges ⊆ (τ ω).edges) ∧
      Measurable (fun ω => OTSelector.PartialMatching.cost (cost ω) (τ ω)) ∧
      ∀ ω, OTSelector.PartialMatching.cost (cost ω) (τ ω) ≤
        OTSelector.PartialMatching.cost (cost ω) (σ ω) +
          ((m - (σ ω).card : ℕ) : ℝ) * B := by
  classical
  obtain ⟨τ, hτmeas, hτ⟩ := exists_measurable_legal_completion allowed hallowed σ hσ
    hσlegal hcapacity
  refine ⟨τ, hτmeas, hτ, ?_, ?_⟩
  · have hrepr : (fun ω => OTSelector.PartialMatching.cost (cost ω) (τ ω)) =
        fun ω => ∑ e ∈ (τ ω).edges, cost ω e.1 e.2 := rfl
    rw [hrepr]
    have hfin : (fun ω => ∑ e ∈ (τ ω).edges, cost ω e.1 e.2) =
        fun ω => ∑ T : PartialMatching m n,
          if τ ω = T then ∑ e ∈ T.edges, cost ω e.1 e.2 else 0 := by
      funext ω'
      symm
      rw [Finset.sum_ite_eq Finset.univ (τ ω') (fun T => ∑ e ∈ T.edges, cost ω' e.1 e.2)]
      simp
    rw [hfin]
    exact Finset.measurable_sum _ fun T _ =>
      Measurable.ite (hτmeas T)
        (Finset.measurable_sum _ fun e _ => hcost e.1 e.2) measurable_const
  · intro ω
    obtain ⟨hlegal, hcard, hsub⟩ := hτ ω
    have hcardm : (τ ω).card = m := hcard.trans (hmax ω)
    have hsplit : OTSelector.PartialMatching.cost (cost ω) (τ ω) =
        OTSelector.PartialMatching.cost (cost ω) (σ ω) +
          ∑ e ∈ ((τ ω).edges \ (σ ω).edges), cost ω e.1 e.2 :=
      cost_eq_add_cost_sdiff hsub (cost ω)
    have hadded : ∑ e ∈ ((τ ω).edges \ (σ ω).edges), cost ω e.1 e.2 ≤
        (((τ ω).edges \ (σ ω).edges).card : ℝ) * B :=
      OTSelector.PartialMatching.cost_le_card_mul (fun i j => cost ω i j)
        { edges := (τ ω).edges \ (σ ω).edges
          row_inj := fun e he e' he' hrow =>
            (τ ω).row_inj e (Finset.mem_sdiff.mp he).1 e'
              (Finset.mem_sdiff.mp he').1 hrow
          col_inj := fun e he e' he' hcol =>
            (τ ω).col_inj e (Finset.mem_sdiff.mp he).1 e'
              (Finset.mem_sdiff.mp he').1 hcol }
        (fun i j => hB ω i j)
    have hcount : ((τ ω).edges \ (σ ω).edges).card = m - (σ ω).card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
      change (τ ω).card - (σ ω).card = m - (σ ω).card
      rw [hcardm]
    rw [hsplit]
    have h := hadded
    rw [hcount] at h
    linarith

end PartialMatching

/-! ## The a.e. reserve bound integrated over the sample law -/

section ReserveExpectation

/-- **The expectation form of the a.e. finite-sample reserve cost bound.**  If the
repaired finite value is at most the retained finite value plus the explicit
reserve budget almost surely, and both are integrable, then the expected repaired
value is at most the expected retained value plus the same budget. -/
theorem integral_le_add_of_ae_reserveBound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {retained repaired : Ω → ℝ}
    (hret : Integrable retained P) (hrep : Integrable repaired P)
    {B : ℝ} (hbound : ∀ᵐ ω ∂P, repaired ω ≤ retained ω + B) :
    (∫ ω, repaired ω ∂P) ≤ (∫ ω, retained ω ∂P) + B := by
  have hmono : (∫ ω, repaired ω ∂P) ≤ ∫ ω, retained ω + B ∂P :=
    integral_mono_ae hrep (hret.add (integrable_const B)) hbound
  rw [integral_add hret (integrable_const B)] at hmono
  simpa using hmono

end ReserveExpectation

end OTSelector.Reconstruction
