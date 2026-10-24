import OTSelector.Transport.Coupling.OrderedStageChain
import OTSelector.Transport.Coupling.OrderedStageQuadraticStep
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalClasswiseStageCouplingOrderedQuadratic.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalClasswiseStageCouplingOrderedQuadratic`; the selected original proof blocks follow. -/
section

/-!
Conditions: Finite actual couplings have successive residual-plus-source/target marginals, vanish at the two terminal residuals and have finite quadratic cost.

Objects: An ordered finite-stage prefix and final coupling with exact labeled marginals and cost at most N times the summed stage cost.

Proof detail: Iteratively disintegrate/glue completed and active parts, track the weighted active potential and use the terminal zero residual to remove the active part.

Sources: Gabriel Peyré, Section 10.1, Remark 10.2, p. 181, gluing lemma preceding (10.4) (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=185); D. H. Fremlin, 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary (https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=25); Terence Tao, Section 1.4, Lemma 1.4.7 (Cauchy–Schwarz inequality), p. 48 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=57).
Relation: Constructive finite-stage gluing with explicit cost bookkeeping; the supplied stage couplings are preserved as inputs.
-/

/-! Genuine ordered finite chains have a linear-length quadratic cost bound. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 600000
variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [StandardBorelSpace E] [Nonempty E]

/-- Every actual prefix has finite endpoint square costs and the linear-length
energy potential. Both completed and active plans are the genuine ordered plans. -/
theorem exists_finiteOrderedQuadraticStagePrefix
    (ν S T : ℕ → Measure E) (π : ℕ → Measure (E × E)) (N n : ℕ)
    [∀ k, IsFiniteMeasure (ν k)] [∀ k, IsFiniteMeasure (S k)]
    [∀ k, IsFiniteMeasure (T k)] [∀ k, IsFiniteMeasure (π k)]
    (hν₀ : ν 0 = 0) (hnN : n ≤ N)
    (hπ₁ : ∀ k < n, (π k).fst = ν k + S k)
    (hπ₂ : ∀ k < n, (π k).snd = ν (k + 1) + T k)
    (hcost : ∀ k < n, Integrable (fun p ↦ dist p.1 p.2 ^ 2) (π k)) :
    ∃ w : FiniteOrderedStagePrefix ν S T n,
      Integrable (fun p ↦ dist p.1.2 p.2 ^ 2) w.active ∧
      Integrable (fun p ↦ dist p.1.2 p.2.2 ^ 2) w.completed ∧
      (∫ p, dist p.1.2 p.2.2 ^ 2 ∂w.completed) +
          (N : ℝ) / n * (∫ p, dist p.1.2 p.2 ^ 2 ∂w.active) ≤
        (N : ℝ) * ∑ k ∈ Finset.range n, ∫ p, dist p.1 p.2 ^ 2 ∂π k := by
  revert hnN hπ₁ hπ₂ hcost
  induction n with
  | zero =>
      intro _ _ _ _
      let w : FiniteOrderedStagePrefix ν S T 0 :=
        { completed := 0
          active := 0
          completed_finite := inferInstance
          active_finite := inferInstance
          source_balance := by simp
          target_balance := by simp
          active_target := by simpa using hν₀.symm
          completed_order := by simp
          active_birth := by simp }
      refine ⟨w, ?_, ?_, ?_⟩ <;> simp [w]
  | succ n ih =>
      intro hnN hπ₁ hπ₂ hcost
      obtain ⟨w, hactive, hcompleted, hbound⟩ := ih (Nat.le_trans (Nat.le_succ n) hnN)
        (fun k hk ↦ hπ₁ k (Nat.lt_succ_of_lt hk))
        (fun k hk ↦ hπ₂ k (Nat.lt_succ_of_lt hk))
        (fun k hk ↦ hcost k (Nat.lt_succ_of_lt hk))
      obtain ⟨v⟩ := exists_finiteOrderedStageStep ν S T n w (π n)
        (hπ₁ n (Nat.lt_succ_self n)) (hπ₂ n (Nat.lt_succ_self n))
      by_cases hn : n = 0
      · subst n
        obtain ⟨hnext, hcomp, hstep⟩ := v.quadratic_prefix_zero_le N hnN hν₀
          (hcost 0 (Nat.lt_succ_self 0))
        refine ⟨v.toPrefix, hnext, hcomp, ?_⟩
        simpa only [Nat.zero_add, Nat.cast_one, div_one, Finset.sum_range_one] using hstep
      · obtain ⟨hnext, hcomp, hstep⟩ := v.quadratic_prefix_le N (Nat.pos_of_ne_zero hn) hnN
          hactive hcompleted (hcost n (Nat.lt_succ_self n))
        refine ⟨v.toPrefix, hnext, hcomp, ?_⟩
        calc
          _ ≤ (∫ p, dist p.1.2 p.2.2 ^ 2 ∂w.completed) +
              (N : ℝ) / n * (∫ p, dist p.1.2 p.2 ^ 2 ∂w.active) +
              (N : ℝ) * (∫ p, dist p.1 p.2 ^ 2 ∂π n) := hstep
          _ ≤ (N : ℝ) * (∑ k ∈ Finset.range n, ∫ p, dist p.1 p.2 ^ 2 ∂π k) +
              (N : ℝ) * (∫ p, dist p.1 p.2 ^ 2 ∂π n) := add_le_add hbound le_rfl
          _ = _ := by rw [Finset.sum_range_succ, mul_add]

/-- The supplied genuine finite stages yield an actual ordered coupling of all
labelled sources and targets. Its quadratic cost is at most the number of
stages times the exact sum of actual stage costs, including the empty chain. -/
theorem exists_finiteOrderedQuadraticClasswiseCoupling
    (ν S T : ℕ → Measure E) (π : ℕ → Measure (E × E)) (N : ℕ)
    [∀ k, IsFiniteMeasure (ν k)] [∀ k, IsFiniteMeasure (S k)]
    [∀ k, IsFiniteMeasure (T k)] [∀ k, IsFiniteMeasure (π k)]
    (hν₀ : ν 0 = 0) (hνN : ν N = 0)
    (hπ₁ : ∀ k < N, (π k).fst = ν k + S k)
    (hπ₂ : ∀ k < N, (π k).snd = ν (k + 1) + T k)
    (hcost : ∀ k < N, Integrable (fun p ↦ dist p.1 p.2 ^ 2) (π k)) :
    ∃ Γ : Measure ((ℕ × E) × (ℕ × E)), IsFiniteMeasure Γ ∧
      Vlasov.IsCoupling Γ (finiteStageLabelledPrefix S N) (finiteStageLabelledPrefix T N) ∧
      (∀ᵐ z ∂Γ, z.1.1 ≤ z.2.1) ∧
      Integrable (fun p ↦ dist p.1.2 p.2.2 ^ 2) Γ ∧
      (∫ p, dist p.1.2 p.2.2 ^ 2 ∂Γ) ≤
        (N : ℝ) * ∑ k ∈ Finset.range N, ∫ p, dist p.1 p.2 ^ 2 ∂π k := by
  obtain ⟨w, _, hcompleted, hbound⟩ :=
    exists_finiteOrderedQuadraticStagePrefix ν S T π N N hν₀ le_rfl hπ₁ hπ₂ hcost
  have hactive : w.active = 0 := by
    apply (Measure.map_eq_zero_iff measurable_snd.aemeasurable).mp
    exact w.active_target.trans hνN
  refine ⟨w.completed, w.completed_finite, ⟨?_, w.target_balance⟩,
    w.completed_order, hcompleted, ?_⟩
  · simpa only [Measure.fst, hactive, Measure.map_zero, add_zero] using w.source_balance
  · simpa only [hactive, integral_zero_measure, mul_zero, add_zero] using hbound

end OTSelector.Reconstruction

end
end
