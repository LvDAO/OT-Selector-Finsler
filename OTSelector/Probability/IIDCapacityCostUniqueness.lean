import Mathlib.Probability.Independence.Basic
import OTSelector.Finite.CapacityAssignment

/-!
Conditions: Finite families of measurable iid rows with the stated common law and measurable costs whose pairwise target differences have atomless image laws; the first conditioning lemma only needs a finite ambient measure.

Objects: Zero probability of an independent atomless difference plus an arbitrary measurable remainder vanishing, hence distinct finite assignments have distinct total costs almost surely.

Proof detail: Choose one row where assignments differ. Split that row from the other independent rows, integrate its atomless difference at the fixed remainder, then remove the finite union of assignment-pair ties.

References: Rick Durrett: Section 2.1.2, Theorems 2.1.11–2.1.12, p. 48; Rick Durrett: Section 1.7, Theorem 1.7.2, p. 38.
Relation: This is the local generic iid no-ties input to the project cavity proof. It assumes atomlessness of cost differences explicitly and does not assert it for arbitrary geometric distances.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.IIDCapacityAssignmentUniqueness.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.IIDCapacityAssignmentUniqueness`; the selected original proof blocks follow. -/
section

/-!
# Actual iid capacity allocations have unique optima

An atomless target-cost difference in one source row remains atomless after adding
the independent cost difference of all other original rows. Hence distinct label
allocations have distinct total costs almost surely, simultaneously for every
capacity vector. Repeated slots do not require distinct slot costs: uniqueness
concerns the actual target labels.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

namespace OTSelector.Probability

variable {ι α S Ω : Type*} [Fintype ι] [Fintype α]
  [MeasurableSpace S] [MeasurableSpace Ω]

/-- An independent retained array and an atomless inserted difference cannot tie
after addition of any measurable retained cost. -/
theorem measure_independent_difference_add_eq_zero
    {W : Type*} [MeasurableSpace W]
    (P : Measure Ω) [IsFiniteMeasure P] (μ : Measure S)
    (W₀ : Ω → W) (X : Ω → S) (hW : Measurable W₀) (hX : Measurable X)
    (hindep : IndepFun W₀ X P) (hlaw : P.map X = μ)
    (d : S → ℝ) (hd : Measurable d) [NullSingletonClass (μ.map d)]
    (q : W → ℝ) (hq : Measurable q) :
    P {ω | d (X ω) + q (W₀ ω) = 0} = 0 := by
  have hE : MeasurableSet {z : W × S | d z.2 + q z.1 = 0} :=
    measurableSet_eq_fun ((hd.comp measurable_snd).add (hq.comp measurable_fst))
      measurable_const
  change P ((fun ω ↦ (W₀ ω, X ω)) ⁻¹' {z : W × S | d z.2 + q z.1 = 0}) = 0
  rw [← Measure.map_apply (hW.prodMk hX) hE,
    hindep.map_prod_eq_prod_map_map hW.aemeasurable hX.aemeasurable, hlaw]
  apply Measure.measure_prod_null_of_ae_null hE
  apply Eventually.of_forall
  intro w
  have heq : Prod.mk w ⁻¹' {z : W × S | d z.2 + q z.1 = 0} = d ⁻¹' {-q w} := by
    ext s
    simp only [mem_preimage, mem_ofPred_eq, mem_singleton_iff]
    exact eq_neg_iff_add_eq_zero.symm
  change μ (Prod.mk w ⁻¹' {z : W × S | d z.2 + q z.1 = 0}) = 0
  rw [heq, ← Measure.map_apply hd (measurableSet_singleton _), measure_singleton]

omit [Fintype α] in
/-- Different actual label allocations have a null total-cost tie under the
original independent iid rows. The allocations need not have the same quotas. -/
theorem measure_capacityAssignmentCost_eq_zero_of_iid_atomless
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure S)
    (X : ι → Ω → S) (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = μ)
    (c : α → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hatom : ∀ j k, j ≠ k → NullSingletonClass (μ.map (fun s ↦ c j s - c k s)))
    (a b : ι → α) (hab : a ≠ b) :
    P {ω | capacityAssignmentCost (fun i j ↦ c j (X i ω)) a =
      capacityAssignmentCost (fun i j ↦ c j (X i ω)) b} = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
    by_contra h
    push Not at h
    exact hab (funext h)
  let W := {k : ι // k ≠ i} → S
  let W₀ : Ω → W := fun ω k ↦ X k.1 ω
  let q : W → ℝ := fun w ↦ ∑ k : {k : ι // k ≠ i},
    (c (a k.1) (w k) - c (b k.1) (w k))
  have hW : Measurable W₀ := measurable_pi_lambda _ fun k ↦ hX k.1
  have hq : Measurable q :=
    Finset.measurable_sum _ fun k _ ↦
      ((hc (a k)).comp (measurable_pi_apply k)).sub
        ((hc (b k)).comp (measurable_pi_apply k))
  have hind : IndepFun W₀ (X i) P := by
    let A : Finset ι := Finset.univ.erase i
    have hdis : Disjoint A {i} := by simp [A]
    have h := hindep.indepFun_finset A {i} hdis hX
    have hleft : Measurable
        (fun w : (k : A) → S ↦ fun k : {k : ι // k ≠ i} ↦
          w ⟨k.1, by simp [A, k.2]⟩) :=
      measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
    exact h.comp hleft (measurable_pi_apply ⟨i, by simp⟩)
  let := hatom (a i) (b i) hi
  have hnull := measure_independent_difference_add_eq_zero P μ W₀ (X i) hW (hX i)
    hind (hlaw i) (fun s ↦ c (a i) s - c (b i) s)
    ((hc (a i)).sub (hc (b i))) q hq
  apply Eq.trans _ hnull
  congr 1
  ext ω
  have hsum := Fintype.sum_eq_add_sum_subtype_ne
    (fun k ↦ c (a k) (X k ω) - c (b k) (X k ω)) i
  simp only [capacityAssignmentCost, mem_ofPred_eq]
  dsimp [q, W₀] at hsum ⊢
  rw [← hsum, Finset.sum_sub_distrib, sub_eq_zero]

/-- All original label-allocation costs are distinct on one event of full
probability, independent of the later choice of capacity vector. -/
theorem ae_injective_capacityAssignmentCost_of_iid_atomless
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure S)
    (X : ι → Ω → S) (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = μ)
    (c : α → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hatom : ∀ j k, j ≠ k → NullSingletonClass (μ.map (fun s ↦ c j s - c k s))) :
    ∀ᵐ ω ∂P, Function.Injective (capacityAssignmentCost (fun i j ↦ c j (X i ω))) := by
  classical
  apply ae_all_iff.mpr
  intro a
  apply ae_all_iff.mpr
  intro b
  by_cases hab : a = b
  · exact Eventually.of_forall fun _ _ ↦ hab
  · have hne : ∀ᵐ ω ∂P, capacityAssignmentCost (fun i j ↦ c j (X i ω)) a ≠
        capacityAssignmentCost (fun i j ↦ c j (X i ω)) b := by
      apply ae_iff.mpr
      simpa only [not_not] using
        measure_capacityAssignmentCost_eq_zero_of_iid_atomless P μ X hX hindep hlaw
          c hc hatom a b hab
    exact hne.mono fun _ h hEq ↦ (h hEq).elim







end OTSelector.Probability

end
