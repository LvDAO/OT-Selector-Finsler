import Mathlib.Data.Nat.Choose.Multinomial
import OTSelector.Finite.CapacityAssignment
import OTSelector.Transport.Semidiscrete.CavityCells

/-!
Conditions: An s-finite retained-data measure, an independent finite product of a probability source law and measurable retained/new-row costs; disjointness and count probabilities keep the stated a.e. no-score-ties assumption.

Objects: Measurable prescribed allocation events, their product-of-cell-masses integrals, grouped natural powers and the exact count-event measure with its feasible-word cardinality factor.

Proof detail: Use Tonelli after fixing retained data, factor each independent row event, group factors by finite label fibers and sum the a.e. disjoint word events.

References: Rick Durrett: Section 1.7, Theorem 1.7.2, p. 38; Rick Durrett: Section 2.1.2, Theorems 2.1.11–2.1.12, p. 48.
Relation: A local conditional multinomial calculation retaining the original product law. It does not assume a Dirichlet law for the retained-data-dependent cell probabilities.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavityDirichletMoments.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavityDirichletMoments`; the selected original proof blocks follow. -/
section

/-!
# Exact finite insertion-count probabilities for cavity moments

For the actual retained-data law and an independent finite iid complement, a prescribed
word of cavity labels has probability equal to the corresponding product of cell masses.
Atomless pairwise differences make different words almost everywhere disjoint. Consequently
the probability of prescribed target counts is the number of feasible words times the mixed
moment of the actual cavity masses. This is the conditional multinomial step of the
Dirichlet moment argument; the target-tree uniqueness of a successful retained subset is
a separate combinatorial input and is not assumed here as a distributional law.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Probability

variable {n : ℕ} {κ W S : Type*} [Fintype κ]
  [MeasurableSpace W] [MeasurableSpace S]

/-- All original complementary sources fall in the indicated actual cavity cells. -/
def cavityAllocationEvent
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (a : κ → Fin (n + 1)) : Set (W × (κ → S)) :=
  {z | ∀ k, (z.1, z.2 k) ∈ cavityCell retained row i (a k)}

/-- The original complement has exactly the prescribed cavity-label counts. -/
def cavityAllocationCounts
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (r : Fin (n + 1) → ℕ) : Set (W × (κ → S)) :=
  ⋃ a : {a : κ → Fin (n + 1) // CapacityFeasible r a},
    cavityAllocationEvent retained row i a.val

/-- Prescribed insertion labels are a jointly measurable event. -/
theorem measurableSet_cavityAllocationEvent
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ)
    (hret : ∀ k l, Measurable (fun w ↦ retained w k l))
    (hrow : ∀ j, Measurable (fun z ↦ row z j))
    (i : Fin (n + 1)) (a : κ → Fin (n + 1)) :
    MeasurableSet (cavityAllocationEvent retained row i a) := by
  simp only [cavityAllocationEvent, ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  exact (measurableSet_cavityCell retained row hret hrow i (a k)).preimage
    (measurable_fst.prodMk ((measurable_pi_apply k).comp measurable_snd))

/-- A fixed label word has its exact original product-cell probability. -/
theorem measure_cavityAllocationEvent
    (ν : Measure W) [SFinite ν] (μ : Measure S) [IsProbabilityMeasure μ]
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ)
    (hret : ∀ k l, Measurable (fun w ↦ retained w k l))
    (hrow : ∀ j, Measurable (fun z ↦ row z j))
    (i : Fin (n + 1)) (a : κ → Fin (n + 1)) :
    (ν.prod (Measure.pi (fun _ : κ ↦ μ))) (cavityAllocationEvent retained row i a) =
      ∫⁻ w, ∏ k, cavityCellMass μ retained row i (a k) w ∂ν := by
  rw [Measure.prod_apply (measurableSet_cavityAllocationEvent retained row hret hrow i a)]
  apply lintegral_congr
  intro w
  have heq : {x : κ → S | (w, x) ∈ cavityAllocationEvent retained row i a} =
      Set.pi Set.univ (fun k ↦ {s | (w, s) ∈ cavityCell retained row i (a k)}) := by
    ext x
    simp [cavityAllocationEvent]
  change Measure.pi (fun _ : κ ↦ μ) {x | (w, x) ∈ cavityAllocationEvent retained row i a} = _
  rw [heq, Measure.pi_pi]
  rfl

omit [MeasurableSpace W] [MeasurableSpace S] in
/-- Grouping a word by its actual target fibers gives the mixed-moment monomial. -/
theorem prod_eq_prod_pow_of_capacityFeasible
    {B : Type*} [CommMonoid B] (p : Fin (n + 1) → B)
    (r : Fin (n + 1) → ℕ) (a : κ → Fin (n + 1)) (ha : CapacityFeasible r a) :
    ∏ k, p (a k) = ∏ j, p j ^ r j := by
  classical
  rw [← Fintype.prod_fiberwise' a p]
  apply Finset.prod_congr rfl
  intro j _
  simp [ha j]

/-- Different prescribed words are almost everywhere disjoint under the original laws. -/
theorem aedisjoint_cavityAllocationEvent
    (ν : Measure W) [SFinite ν] (μ : Measure S) [IsProbabilityMeasure μ]
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ)
    (hret : ∀ k l, Measurable (fun w ↦ retained w k l))
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i : Fin (n + 1))
    (hno : ∀ᵐ w ∂ν, ∀ j l, j ≠ l →
      μ {s | cavityScore retained row i (w, s) j = cavityScore retained row i (w, s) l} = 0) :
    Pairwise (fun a b : κ → Fin (n + 1) ↦ AEDisjoint
      (ν.prod (Measure.pi (fun _ : κ ↦ μ)))
      (cavityAllocationEvent retained row i a) (cavityAllocationEvent retained row i b)) := by
  intro a b hab
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hab
  apply Measure.measure_prod_null_of_ae_null
    ((measurableSet_cavityAllocationEvent retained row hret hrow i a).inter
      (measurableSet_cavityAllocationEvent retained row hret hrow i b))
  filter_upwards [hno] with w hw
  let T := {s | cavityScore retained row i (w, s) (a k) =
    cavityScore retained row i (w, s) (b k)}
  have hT : MeasurableSet T := measurableSet_eq_fun
    ((measurable_cavityScore retained row hret hrow i (a k)).comp measurable_prodMk_left)
    ((measurable_cavityScore retained row hret hrow i (b k)).comp measurable_prodMk_left)
  have hnull : (Measure.pi (fun _ : κ ↦ μ)) ((fun x ↦ x k) ⁻¹' T) = 0 := by
    rw [← Measure.map_apply (measurable_pi_apply k) hT,
      (measurePreserving_eval (fun _ : κ ↦ μ) k).map_eq]
    exact hw (a k) (b k) hk
  apply measure_mono_null _ hnull
  intro x hx
  exact le_antisymm (hx.1 k (b k)) (hx.2 k (a k))

/-- The exact finite-count probability is its combinatorial multiplicity times the actual
cavity mixed moment. No target-mass distribution or predetermined balancing is assumed. -/
theorem measure_cavityAllocationCounts
    (ν : Measure W) [SFinite ν] (μ : Measure S) [IsProbabilityMeasure μ]
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ)
    (hret : ∀ k l, Measurable (fun w ↦ retained w k l))
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i : Fin (n + 1))
    (hno : ∀ᵐ w ∂ν, ∀ j l, j ≠ l →
      μ {s | cavityScore retained row i (w, s) j = cavityScore retained row i (w, s) l} = 0)
    (r : Fin (n + 1) → ℕ) :
    (ν.prod (Measure.pi (fun _ : κ ↦ μ))) (cavityAllocationCounts retained row i r) =
      (Nat.card {a : κ → Fin (n + 1) // CapacityFeasible r a} : ℝ≥0∞) *
        ∫⁻ w, ∏ j, cavityCellMass μ retained row i j w ^ r j ∂ν := by
  classical
  have hd := aedisjoint_cavityAllocationEvent (κ := κ) ν μ retained row hret hrow i hno
  unfold cavityAllocationCounts
  rw [measure_iUnion₀ (fun a b hab ↦ hd (Subtype.val_injective.ne hab))
    (fun a ↦ (measurableSet_cavityAllocationEvent retained row hret hrow i a.val).nullMeasurableSet),
    tsum_fintype]
  simp_rw [measure_cavityAllocationEvent ν μ retained row hret hrow i]
  have hprod (a : {a : κ → Fin (n + 1) // CapacityFeasible r a}) (w : W) :
      ∏ k, cavityCellMass μ retained row i (a.val k) w =
        ∏ j, cavityCellMass μ retained row i j w ^ r j :=
    prod_eq_prod_pow_of_capacityFeasible (fun j ↦ cavityCellMass μ retained row i j w)
      r a.val a.property
  simp_rw [hprod]
  simp [nsmul_eq_mul, Nat.card_eq_fintype_card]



end OTSelector.Probability

end
end
