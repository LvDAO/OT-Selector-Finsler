import OTSelector.Finite.FractionalOptimal
import OTSelector.Probability.IndependentRandomRegion
import OTSelector.Transport.Semidiscrete.CavityCells
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavityMeanPlan.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavityMeanPlan`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual optimal fractional row, a unique cavity cell and the stated independent environment/row law and integrable readouts.

Objects: Indicator identification of that row and its exact expected cavity readout.

Proof detail: Positive row entries must lie in cavity minima, uniqueness makes the row a single indicator; integrate the same indicator against the product law.

Sources: Gabriel Peyré, Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20) (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31); D. H. Fremlin, Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25 (https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19); Rick Durrett, Section 2.1.2, Theorems 2.1.11–2.1.13, pp. 48–49 (https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=56); Project manuscript, Section “Exact iid cavity disintegration”, Theorem thm:iid-cavity-dirichlet and Proposition prop:iid-cavity-mean, equation eq:iid-cavity-mean-plan (main.tex).
Relation: Local row/mean-plan identity; main.tex prop:iid-cavity-mean is the project-level assembly, not a textbook assertion about arbitrary selected plans.
-/

/-!
# Exact mean readouts of the full optimal face through cavity cells

An independent original source is inserted into its actual retained assignment problem.
Whenever the inserted cavity cell is unique, every optimal fractional matrix has the same
unit row. Fubini then identifies expectations of arbitrary integrable endpoint tests with
the mean of the actual cell allocations. No measurable optimizer selection is needed.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

noncomputable section
namespace OTSelector.Probability

variable {n : ℕ} {W S Ω : Type*}
  [MeasurableSpace W] [MeasurableSpace S] [MeasurableSpace Ω]

omit [MeasurableSpace W] [MeasurableSpace S] in
/-- A unique cavity cell forces the whole optimal fractional row to its indicator. -/
theorem optimalFractional_row_eq_cavity_indicator
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ) (i : Fin (n + 1)) (z : W × S)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : OptimalFractionalAssignment (Function.update (retained z.1) i (row z)) A)
    (huniq : ∃! j, z ∈ cavityCell retained row i j) (j : Fin (n + 1)) :
    A i j = (cavityCell retained row i j).indicator (fun _ ↦ (1 : ℝ)) z := by
  classical
  obtain ⟨k, hk, hku⟩ := huniq
  have hz (l : Fin (n + 1)) (hl : l ≠ k) : A i l = 0 := by
    apply le_antisymm _ (nonneg_of_mem_doublyStochastic hA.1)
    by_contra hpos
    exact hl (hku l (mem_cavityCell_of_optimalFractional_pos retained row i l z A hA
      (lt_of_not_ge hpos)))
  have hk1 : A i k = 1 := by
    have hs := sum_row_of_mem_doublyStochastic hA.1 i
    rw [Finset.sum_eq_single k (fun l _ hl ↦ hz l hl) (by simp)] at hs
    exact hs
  by_cases hj : j = k
  · subst j
    simp [hk, hk1]
  · have hjnot : z ∉ cavityCell retained row i j := fun hjmem ↦ hj (hku j hjmem)
    simp [hz j hj, hjnot]

/-- A full endpoint test integrated against the actual cell allocation of one source. -/
def cavityMeanReadout (μ : Measure S)
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (g : W × S → Fin (n + 1) → ℝ) (w : W) : ℝ :=
  ∑ j, ∫ s in {s | (w, s) ∈ cavityCell retained row i j}, g (w, s) j ∂μ

/-- Each original optimal fractional row has exactly the cavity allocation's mean readout.
The test may depend on the retained data, source, and target label. The optimizer is arbitrary;
its almost-everywhere equality to measurable cell indicators also supplies integrability. -/
theorem integral_optimalFractional_row_eq_cavityMeanReadout_of_unique
    (P : Measure Ω) [IsFiniteMeasure P] (μ : Measure S) [SFinite μ]
    (W₀ : Ω → W) (X : Ω → S) (hW : Measurable W₀) (hX : Measurable X)
    (hindep : IndepFun W₀ X P) (hlaw : P.map X = μ)
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ)
    (hret : ∀ k l, Measurable (fun w ↦ retained w k l))
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i : Fin (n + 1))
    (huniq : ∀ᵐ ω ∂P, ∃! j, (W₀ ω, X ω) ∈ cavityCell retained row i j)
    (A : Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : ∀ᵐ ω ∂P, OptimalFractionalAssignment
      (Function.update (retained (W₀ ω)) i (row (W₀ ω, X ω))) (A ω))
    (g : W × S → Fin (n + 1) → ℝ)
    (hg : ∀ j, Integrable (fun z ↦ g z j) ((P.map W₀).prod μ)) :
    Integrable (fun ω ↦ ∑ j, A ω i j * g (W₀ ω, X ω) j) P ∧
      (∫ ω, ∑ j, A ω i j * g (W₀ ω, X ω) j ∂P) =
        ∫ w, cavityMeanReadout μ retained row i g w ∂P.map W₀ := by
  classical
  let f (j : Fin (n + 1)) : W × S → ℝ :=
    (cavityCell retained row i j).indicator (fun z ↦ g z j)
  have hm j := measurableSet_cavityCell retained row hret hrow i j
  have hf j : Integrable (f j) ((P.map W₀).prod μ) := (hg j).indicator (hm j)
  have hmap : P.map (fun ω ↦ (W₀ ω, X ω)) = (P.map W₀).prod μ := by
    rw [hindep.map_prod_eq_prod_map_map hW.aemeasurable hX.aemeasurable, hlaw]
  have hcomp j : Integrable (fun ω ↦ f j (W₀ ω, X ω)) P := by
    have hfmap : Integrable (f j) (P.map (fun ω ↦ (W₀ ω, X ω))) := by
      rw [hmap]
      exact hf j
    exact hfmap.comp_measurable (hW.prodMk hX)
  have heq : (fun ω ↦ ∑ j, A ω i j * g (W₀ ω, X ω) j) =ᵐ[P]
      (fun ω ↦ ∑ j, f j (W₀ ω, X ω)) := by
    filter_upwards [hA, huniq] with ω hAω huω
    apply Finset.sum_congr rfl
    intro j _
    rw [optimalFractional_row_eq_cavity_indicator retained row i (W₀ ω, X ω)
      (A ω) hAω huω j]
    by_cases hj : (W₀ ω, X ω) ∈ cavityCell retained row i j <;> simp [f, hj]
  have hsum := integrable_finsetSum Finset.univ (fun j _ ↦ hcomp j)
  refine ⟨hsum.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_finsetSum _ (fun j _ ↦ hcomp j)]
  have hiter j : Integrable (fun w ↦ ∫ s, f j (w, s) ∂μ) (P.map W₀) :=
    (hf j).integral_prod_left
  calc
    _ = ∑ j, ∫ w, ∫ s, f j (w, s) ∂μ ∂P.map W₀ := by
      apply Finset.sum_congr rfl
      intro j _
      have h := integral_indepFun_pair_eq_integral_prod hW hX hindep
        (F := f j) (by simpa [hlaw] using hf j)
      rw [hlaw] at h
      exact h.trans (integral_prod (f j) (hf j))
    _ = ∫ w, ∑ j, ∫ s, f j (w, s) ∂μ ∂P.map W₀ :=
      (integral_finsetSum _ (fun j _ ↦ hiter j)).symm
    _ = ∫ w, cavityMeanReadout μ retained row i g w ∂P.map W₀ := by
      apply integral_congr_ae
      filter_upwards with w
      apply Finset.sum_congr rfl
      intro j _
      have hsec : MeasurableSet {s | (w, s) ∈ cavityCell retained row i j} :=
        (hm j).preimage measurable_prodMk_left
      rw [← integral_indicator (μ := μ) (f := fun s ↦ g (w, s) j) hsec]
      apply integral_congr_ae
      filter_upwards with s
      by_cases hs : (w, s) ∈ cavityCell retained row i j <;> simp [f, hs]

/-- Atomless original pairwise row differences provide the unique-cell hypothesis for the
mean-plan identity on the entire optimal fractional face. -/
theorem integral_optimalFractional_row_eq_cavityMeanReadout
    (P : Measure Ω) [IsFiniteMeasure P] (μ : Measure S) [SFinite μ]
    (W₀ : Ω → W) (X : Ω → S) (hW : Measurable W₀) (hX : Measurable X)
    (hindep : IndepFun W₀ X P) (hlaw : P.map X = μ)
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ)
    (hret : ∀ k l, Measurable (fun w ↦ retained w k l))
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i : Fin (n + 1))
    (hatom : ∀ᵐ w ∂P.map W₀, ∀ j k, j ≠ k →
      NullSingletonClass (μ.map (fun s ↦ row (w, s) j - row (w, s) k)))
    (A : Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : ∀ᵐ ω ∂P, OptimalFractionalAssignment
      (Function.update (retained (W₀ ω)) i (row (W₀ ω, X ω))) (A ω))
    (g : W × S → Fin (n + 1) → ℝ)
    (hg : ∀ j, Integrable (fun z ↦ g z j) ((P.map W₀).prod μ)) :
    Integrable (fun ω ↦ ∑ j, A ω i j * g (W₀ ω, X ω) j) P ∧
      (∫ ω, ∑ j, A ω i j * g (W₀ ω, X ω) j ∂P) =
        ∫ w, cavityMeanReadout μ retained row i g w ∂P.map W₀ :=
  integral_optimalFractional_row_eq_cavityMeanReadout_of_unique P μ W₀ X hW hX hindep hlaw
    retained row hret hrow i
    (ae_existsUnique_mem_cavityCell_of_indepFun_atomless P μ W₀ X hW hX hindep hlaw
      retained row hret hrow i hatom) A hA g hg



end OTSelector.Probability

end
end
