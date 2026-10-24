import OTSelector.Finite.CapacityAssignment
import OTSelector.Finite.TargetTreeCanonicalSuccess
import OTSelector.Finite.TargetTreeRestriction
import OTSelector.Probability.Dirichlet.CavitySplit
import OTSelector.Probability.Dirichlet.CavityStrictCounts
import OTSelector.Probability.Dirichlet.CavitySuccess
import OTSelector.Probability.Dirichlet.CavityWordCount
import OTSelector.Transport.Semidiscrete.CavityCells

/-!
Conditions: A probability source law, measurable finitely many costs and atomless pairwise cost differences; finite capacities and row counts retain their explicit sum identities.

Objects: The number of feasible label words, measurable retained costs, the successful-subset probability as a multinomial cell-mass moment and its exact exchangeability normalization.

Proof detail: Relabel finite source coordinates, split a retained subset from its independent complement and apply the unique-successful-subset partition. Count complement labelings by their capacity fibers and sum equal subset probabilities.

References: OTSelector project: main.tex label thm:iid-cavity-dirichlet, line 4290; Rick Durrett: Section 2.1.2, Theorems 2.1.11–2.1.12, p. 48.
Relation: This is part of the project’s distribution-free cavity argument. The probability book supports product independence and the finite text supports counting, while the cavity uniqueness/exchangeability identity is proved in the project.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavityDirichletExchangeability.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavityDirichletExchangeability`; the selected original proof blocks follow. -/
section

/-!
# Exact cavity mixed moments from original iid subset exchangeability

Every candidate retained subset has the same successful-count probability: its actual
coordinate split has the ordinary iid retained/complement product law. The probability is
the multinomial coefficient times the actual cavity mixed moment. Summing over the unique
successful subset supplies its exact normalization.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Probability

variable {m K : ℕ} {S : Type*} [MeasurableSpace S]

/-- Feasible-word multiplicity depends only on the actual number of complementary rows. -/
theorem card_capacityFeasible_eq_multinomial_of_card {κ : Type*} [Fintype κ]
    (r : Fin (m + 1) → ℕ) (hr : ∑ j, r j = Fintype.card κ) :
    Nat.card {a : κ → Fin (m + 1) // CapacityFeasible r a} = Nat.multinomial Finset.univ r := by
  classical
  let e := Fintype.equivFin κ
  let E : {a : κ → Fin (m + 1) // CapacityFeasible r a} ≃
      {a : Fin (Fintype.card κ) → Fin (m + 1) // CapacityFeasible r a} :=
    { toFun := fun a ↦ ⟨a.1 ∘ e.symm, capacityFeasible_reindex r a.1 e.symm a.2⟩
      invFun := fun a ↦ ⟨a.1 ∘ e, capacityFeasible_reindex r a.1 e a.2⟩
      left_inv := fun a ↦ Subtype.ext (funext fun k ↦ by simp)
      right_inv := fun a ↦ Subtype.ext (funext fun k ↦ by simp) }
  rw [Nat.card_congr E]
  exact card_capacityFeasible_eq_multinomial r hr

/-- The ordinary retained iid cavity matrix is measurable in every entry. -/
theorem measurable_iidCavityRetained (c : Fin (m + 1) → S → ℝ)
    (hc : ∀ j, Measurable (c j)) (k j : Fin (m + 1)) :
    Measurable (fun w : Fin m → S ↦ iidCapacityInputCost c (fun l w ↦ w l) w k j) := by
  refine Fin.succAboveCases 0 ?_ (fun l ↦ ?_) k
  · simp only [iidCapacityInputCost, Fin.insertNth_apply_same]
    exact measurable_const
  · simpa only [iidCapacityInputCost_retained, Function.comp_def] using
      (hc j).comp (measurable_pi_apply l)

/-- Each actual candidate's success probability is the same original iid cavity mixed
moment times its exact multinomial coefficient. -/
theorem measure_capacitySuccessfulSubset_eq_multinomial_moment
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c : Fin (m + 1) → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c j s - c l s)))
    (r : Fin (m + 1) → ℕ) (hr : ∑ j, r j = K)
    (I : {I : Finset (Fin (m + K)) // I.card = m}) :
    (Measure.pi (fun _ : Fin (m + K) ↦ μ))
        {x | CapacitySuccessfulSubset (fun j ↦ r j + 1) (by simp)
          (iidCapacityInputCost c (fun k x ↦ x k) x) 0 I} =
      (Nat.multinomial Finset.univ r : ℝ≥0∞) *
        ∫⁻ w, ∏ j, cavityCellMass μ (iidCapacityInputCost c (fun k w ↦ w k))
          (fun z j ↦ c j z.2) 0 j w ^ r j ∂Measure.pi (fun _ : Fin m ↦ μ) := by
  classical
  let retained := iidCapacityInputCost c (fun (k : Fin m) (w : Fin m → S) ↦ w k)
  let row : (Fin m → S) × S → Fin (m + 1) → ℝ := fun z j ↦ c j z.2
  have hret := measurable_iidCavityRetained c hc
  have hrow (j : Fin (m + 1)) : Measurable (fun z ↦ row z j) := (hc j).comp measurable_snd
  let E := cavityStrictAllocationCounts
    (κ := {k : Fin (m + K) // k ∉ I.1}) retained row 0 r
  have hE : MeasurableSet E := measurableSet_cavityStrictAllocationCounts retained row hret hrow 0 r
  have heq : {x | CapacitySuccessfulSubset (fun j ↦ r j + 1) (by simp)
      (iidCapacityInputCost c (fun k x ↦ x k) x) 0 I} = cavitySubsetSplit I ⁻¹' E := by
    ext x
    simpa only [Nat.add_sub_cancel, mem_preimage, mem_ofPred_eq, E, retained, row] using
      capacitySuccessfulSubset_iff_split_strict_counts c (fun j ↦ r j + 1) I x
  rw [heq, ← Measure.map_apply (cavitySubsetSplit I).measurable hE,
    (measurePreserving_cavitySubsetSplit μ I).map_eq]
  have hno : ∀ᵐ w ∂Measure.pi (fun _ : Fin m ↦ μ), ∀ j l, j ≠ l →
      μ {s | cavityScore retained row 0 (w, s) j = cavityScore retained row 0 (w, s) l} = 0 := by
    apply Eventually.of_forall
    intro w j l hjl
    have := hatom j l hjl
    exact measure_cavityScore_eq_zero_of_atomless μ retained row hrow 0 j l w
  rw [measure_cavityStrictAllocationCounts _ μ retained row hret hrow 0 hno r]
  have hcard : Fintype.card {k : Fin (m + K) // k ∉ I.1} = K := by
    rw [Fintype.card_subtype_compl (fun k : Fin (m + K) ↦ k ∈ I.1)]
    simp only [Fintype.card_fin, Fintype.card_coe, I.2, Nat.add_sub_cancel_left]
  rw [card_capacityFeasible_eq_multinomial_of_card r (hr.trans hcard.symm)]

/-- The exact mixed-moment normalization from the constructed unique successful subset.
It holds for the original iid cavity cell masses and arbitrary nonnegative integer powers. -/
theorem iid_cavity_mixed_moment_normalization
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c : Fin (m + 1) → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c j s - c l s)))
    (r : Fin (m + 1) → ℕ) :
    ((m + ∑ j, r j).choose m : ℝ≥0∞) * (Nat.multinomial Finset.univ r : ℝ≥0∞) *
      (∫⁻ w, ∏ j, cavityCellMass μ (iidCapacityInputCost c (fun k w ↦ w k))
        (fun z j ↦ c j z.2) 0 j w ^ r j ∂Measure.pi (fun _ : Fin m ↦ μ)) = 1 := by
  classical
  let K := ∑ j, r j
  let P := Measure.pi (fun _ : Fin (m + K) ↦ μ)
  let X : Fin (m + K) → (Fin (m + K) → S) → S := fun k x ↦ x k
  have hX (k : Fin (m + K)) : Measurable (X k) := measurable_pi_apply k
  have hi : iIndepFun X P := iIndepFun_pi (fun _ ↦ aemeasurable_id)
  have hlaw (k : Fin (m + K)) : P.map (X k) = μ :=
    (measurePreserving_eval (fun _ : Fin (m + K) ↦ μ) k).map_eq
  have htotal : (∑ j, (r j + 1)) = m + K + 1 := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]
    dsimp [K]
    omega
  have hsum := sum_measure_capacitySuccessfulSubset_eq_one_of_iid_atomless
    P μ X hX hi hlaw c hc hatom (fun j ↦ r j + 1) (fun _ ↦ Nat.zero_lt_succ _) htotal
  have heach (I : {I : Finset (Fin (m + K)) // I.card = m}) :=
    measure_capacitySuccessfulSubset_eq_multinomial_moment μ c hc hatom r (rfl : ∑ j, r j = K) I
  change (∑ I : {I : Finset (Fin (m + K)) // I.card = m},
    (Measure.pi (fun _ : Fin (m + K) ↦ μ))
      {x | CapacitySuccessfulSubset (fun j ↦ r j + 1) (by simp)
        (iidCapacityInputCost c (fun k x ↦ x k) x) 0 I}) = 1 at hsum
  have heqsum : (∑ I : {I : Finset (Fin (m + K)) // I.card = m},
      (Measure.pi (fun _ : Fin (m + K) ↦ μ))
        {x | CapacitySuccessfulSubset (fun j ↦ r j + 1) (by simp)
          (iidCapacityInputCost c (fun k x ↦ x k) x) 0 I}) =
      ∑ _I : {I : Finset (Fin (m + K)) // I.card = m},
        (Nat.multinomial Finset.univ r : ℝ≥0∞) *
          (∫⁻ w, ∏ j, cavityCellMass μ (iidCapacityInputCost c (fun k w ↦ w k))
            (fun z j ↦ c j z.2) 0 j w ^ r j ∂Measure.pi (fun _ : Fin m ↦ μ)) := by
    apply Finset.sum_congr rfl
    intro I _
    exact heach I
  rw [heqsum] at hsum
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin,
    nsmul_eq_mul, ← mul_assoc] at hsum
  exact hsum

end OTSelector.Probability

end
end
