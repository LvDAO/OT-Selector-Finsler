import Mathlib.Probability.Independence.Integration
import OTSelector.Finite.AssignmentCavity
import OTSelector.Finite.FractionalOptimal
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavityCells.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavityCells`; the selected original proof blocks follow. -/
section

/-!
Conditions: Finite assignment costs with measurable retained rows/new row; no-tie, independence and product-law hypotheses occur only in the corresponding almost-everywhere variants.

Objects: Actual cavity scores/cells/masses, measurability, coverage and unique cell selection almost everywhere.

Proof detail: Use finite assignment cavity minima for scores, measurable comparisons for cells, and Fubini/independence to transfer pairwise atomless score differences to a unique minimizer.

Sources: Gabriel Peyré, Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20) (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31); Gabriel Peyré, Section 5.2, equations (5.6)–(5.8), pp. 94–96 (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=98); D. H. Fremlin, Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25 (https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19); Rick Durrett, Section 2.1.2, Theorems 2.1.11–2.1.13, pp. 48–49 (https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=56); Project manuscript, Section “Exact iid cavity disintegration”, Theorem thm:iid-cavity-dirichlet and Proposition prop:iid-cavity-mean, equation eq:iid-cavity-mean-plan (main.tex).
Relation: Finite row-deletion and no-tie cell calculations, also used in main.tex thm:iid-cavity-dirichlet. The distribution-free Dirichlet theorem is not inferred from these cells alone.
-/

/-!
# Measurable finite cavity cells under the original insertion law

Exact vacancy prices depend only on the retained input. Their measurable row envelopes define
cells containing every possible optimal partner, with all ties retained. Atomless pairwise
row-cost differences imply that these cells partition the insertion space almost everywhere.
For an independent insertion on the original probability space, cell masses give the allocation
probabilities after restriction to any measurable retained-input event. No new samples or
uniqueness of the full assignment are assumed. The atomless condition remains explicit; no
Dirichlet law or geometric verification of that condition is claimed here.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace OTSelector.Probability

variable {n : ℕ} {W S Ω : Type*}
  [MeasurableSpace W] [MeasurableSpace S] [MeasurableSpace Ω]

/-- Inserting a new row is scored against the exact retained-input vacancy prices. -/
noncomputable def cavityScore
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (z : W × S) (j : Fin (n + 1)) : ℝ :=
  row z j + assignmentCavityValue (retained z.1) i j

/-- The full argmin cell for a target, including its tied boundary. -/
def cavityCell (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ) (i j : Fin (n + 1)) : Set (W × S) :=
  {z | ∀ k, cavityScore retained row i z j ≤ cavityScore retained row i z k}

/-- Cell masses use the original insertion law and are functions of retained input. -/
noncomputable def cavityCellMass (μ : Measure S)
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ) (i j : Fin (n + 1)) (w : W) : ℝ≥0∞ :=
  μ {s | (w, s) ∈ cavityCell retained row i j}



/-- Measurable retained data and row costs give jointly measurable cavity scores. -/
theorem measurable_cavityScore
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ)
    (hret : ∀ k l, Measurable (fun w ↦ retained w k l))
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i j : Fin (n + 1)) :
    Measurable (fun z ↦ cavityScore retained row i z j) :=
  (hrow j).add ((measurable_assignmentCavityValue retained hret i j).comp measurable_fst)

/-- The full cells are measurable, including all tied minimizers. -/
theorem measurableSet_cavityCell
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ)
    (hret : ∀ k l, Measurable (fun w ↦ retained w k l))
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i j : Fin (n + 1)) :
    MeasurableSet (cavityCell retained row i j) := by
  simp only [cavityCell, ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  exact measurableSet_le (measurable_cavityScore retained row hret hrow i j)
    (measurable_cavityScore retained row hret hrow i k)

/-- Cell masses are measurable functions of the retained input. -/
theorem measurable_cavityCellMass (μ : Measure S) [SFinite μ]
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ)
    (hret : ∀ k l, Measurable (fun w ↦ retained w k l))
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i j : Fin (n + 1)) :
    Measurable (cavityCellMass μ retained row i j) :=
  measurable_measure_prodMk_left (measurableSet_cavityCell retained row hret hrow i j)

omit [MeasurableSpace W] [MeasurableSpace S] in
/-- At every retained input and insertion, at least one cell contains the pair. -/
theorem exists_mem_cavityCell
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ) (i : Fin (n + 1)) (z : W × S) :
    ∃ j, z ∈ cavityCell retained row i j := by
  obtain ⟨j, _, hj⟩ := Finset.univ.exists_min_image (cavityScore retained row i z)
    Finset.univ_nonempty
  exact ⟨j, fun k ↦ hj k (Finset.mem_univ _)⟩





omit [MeasurableSpace W] [MeasurableSpace S] in
/-- Every positive partner of every full fractional optimum lies in the same cell. -/
theorem mem_cavityCell_of_optimalFractional_pos
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ) (i j : Fin (n + 1)) (z : W × S)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : OptimalFractionalAssignment (Function.update (retained z.1) i (row z)) A)
    (hij : 0 < A i j) : z ∈ cavityCell retained row i j := by
  have h := optimalFractionalAssignment_pos_cavity_min _ A hA i j hij
  simpa [cavityCell, cavityScore, assignmentRowEnvelope] using h

/-- Atomlessness of a pairwise cost difference makes its priced score tie null. -/
theorem measure_cavityScore_eq_zero_of_atomless
    (μ : Measure S) (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ)
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i j k : Fin (n + 1)) (w : W)
    [NullSingletonClass (μ.map (fun s ↦ row (w, s) j - row (w, s) k))] :
    μ {s | cavityScore retained row i (w, s) j = cavityScore retained row i (w, s) k} = 0 := by
  have hm : Measurable (fun s ↦ row (w, s) j - row (w, s) k) :=
    ((hrow j).comp measurable_prodMk_left).sub ((hrow k).comp measurable_prodMk_left)
  have heq : {s | cavityScore retained row i (w, s) j = cavityScore retained row i (w, s) k} =
      (fun s ↦ row (w, s) j - row (w, s) k) ⁻¹'
        {assignmentCavityValue (retained w) i k - assignmentCavityValue (retained w) i j} := by
    ext s
    simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff, cavityScore]
    constructor <;> intro h <;> linarith
  rw [heq, ← Measure.map_apply hm (measurableSet_singleton _), measure_singleton]

omit [MeasurableSpace W] in
/-- The direct no-tie condition makes different cell sections almost everywhere disjoint. -/
theorem aedisjoint_cavityCell_sections
    (μ : Measure S) (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ) (i : Fin (n + 1)) (w : W)
    (hno : ∀ j k, j ≠ k →
      μ {s | cavityScore retained row i (w, s) j = cavityScore retained row i (w, s) k} = 0) :
    Pairwise (fun j k ↦ AEDisjoint μ
      {s | (w, s) ∈ cavityCell retained row i j} {s | (w, s) ∈ cavityCell retained row i k}) := by
  intro j k hjk
  apply measure_mono_null _ (hno j k hjk)
  intro s hs
  exact le_antisymm (hs.1 k) (hs.2 j)

/-- With no ties, the measurable cell masses sum to the full insertion mass. -/
theorem sum_cavityCellMass
    (μ : Measure S) (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ)
    (hret : ∀ k l, Measurable (fun w ↦ retained w k l))
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i : Fin (n + 1)) (w : W)
    (hno : ∀ j k, j ≠ k →
      μ {s | cavityScore retained row i (w, s) j = cavityScore retained row i (w, s) k} = 0) :
    ∑ j, cavityCellMass μ retained row i j w = μ Set.univ := by
  have hcover : (⋃ j, {s | (w, s) ∈ cavityCell retained row i j}) = Set.univ := by
    ext s
    simp only [mem_iUnion, mem_ofPred_eq, mem_univ, iff_true]
    exact exists_mem_cavityCell retained row i (w, s)
  have hmeas (j : Fin (n + 1)) : MeasurableSet {s | (w, s) ∈ cavityCell retained row i j} :=
    (measurableSet_cavityCell retained row hret hrow i j).preimage measurable_prodMk_left
  rw [← hcover, measure_iUnion₀ (aedisjoint_cavityCell_sections μ retained row i w hno)
    (fun j ↦ (hmeas j).nullMeasurableSet), tsum_fintype]
  rfl

omit [MeasurableSpace W] [MeasurableSpace S] in
/-- Distinct priced scores give a unique cell, without uniqueness of the remainder assignment. -/
theorem existsUnique_mem_cavityCell_of_pairwise_ne
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ) (i : Fin (n + 1)) (z : W × S)
    (h : Pairwise (fun j k ↦ cavityScore retained row i z j ≠ cavityScore retained row i z k)) :
    ∃! j, z ∈ cavityCell retained row i j := by
  obtain ⟨j, hj⟩ := exists_mem_cavityCell retained row i z
  refine ⟨j, hj, fun k hk ↦ ?_⟩
  by_contra hkj
  exact h hkj (le_antisymm (hk j) (hj k))

private theorem ae_pairwise_ne_of_eq_null {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (score : A → Fin (n + 1) → ℝ)
    (hno : ∀ j k, j ≠ k → μ {a | score a j = score a k} = 0) :
    ∀ᵐ a ∂μ, Pairwise (fun j k ↦ score a j ≠ score a k) := by
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro k
  by_cases hjk : j = k
  · exact Eventually.of_forall fun _ h ↦ (h hjk).elim
  · have hne : ∀ᵐ a ∂μ, score a j ≠ score a k := by
      apply ae_iff.mpr
      simpa only [not_not] using hno j k hjk
    exact hne.mono fun _ h _ ↦ h

omit [MeasurableSpace W] in
/-- The no-tie condition gives an almost-everywhere cell partition at each retained input. -/
theorem ae_existsUnique_mem_cavityCell
    (μ : Measure S) (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ) (i : Fin (n + 1)) (w : W)
    (hno : ∀ j k, j ≠ k →
      μ {s | cavityScore retained row i (w, s) j = cavityScore retained row i (w, s) k} = 0) :
    ∀ᵐ s ∂μ, ∃! j, (w, s) ∈ cavityCell retained row i j := by
  filter_upwards [ae_pairwise_ne_of_eq_null μ (fun s ↦ cavityScore retained row i (w, s)) hno]
    with s hs
  exact existsUnique_mem_cavityCell_of_pairwise_ne retained row i (w, s) hs

/-- Under independence, fiberwise no ties hold for the original random insertion pair. -/
theorem ae_existsUnique_mem_cavityCell_of_indepFun
    (P : Measure Ω) [IsFiniteMeasure P] (μ : Measure S)
    (W₀ : Ω → W) (X : Ω → S) (hW : Measurable W₀) (hX : Measurable X)
    (hindep : IndepFun W₀ X P) (hlaw : P.map X = μ)
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ)
    (hret : ∀ k l, Measurable (fun w ↦ retained w k l))
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i : Fin (n + 1))
    (hno : ∀ᵐ w ∂P.map W₀, ∀ j k, j ≠ k →
      μ {s | cavityScore retained row i (w, s) j = cavityScore retained row i (w, s) k} = 0) :
    ∀ᵐ ω ∂P, ∃! j, (W₀ ω, X ω) ∈ cavityCell retained row i j := by
  have hnull (j k : Fin (n + 1)) (hjk : j ≠ k) :
      P {ω | cavityScore retained row i (W₀ ω, X ω) j =
        cavityScore retained row i (W₀ ω, X ω) k} = 0 := by
    have heq : MeasurableSet {z | cavityScore retained row i z j = cavityScore retained row i z k} :=
      measurableSet_eq_fun (measurable_cavityScore retained row hret hrow i j)
        (measurable_cavityScore retained row hret hrow i k)
    change P ((fun ω ↦ (W₀ ω, X ω)) ⁻¹'
      {z | cavityScore retained row i z j = cavityScore retained row i z k}) = 0
    rw [← Measure.map_apply (hW.prodMk hX) heq,
      hindep.map_prod_eq_prod_map_map hW.aemeasurable hX.aemeasurable, hlaw]
    apply Measure.measure_prod_null_of_ae_null heq
    exact hno.mono fun w hw ↦ hw j k hjk
  filter_upwards [ae_pairwise_ne_of_eq_null P
    (fun ω ↦ cavityScore retained row i (W₀ ω, X ω)) hnull] with ω hω
  exact existsUnique_mem_cavityCell_of_pairwise_ne retained row i (W₀ ω, X ω) hω

/-- Atomless difference laws give the required original-pair no-tie result. -/
theorem ae_existsUnique_mem_cavityCell_of_indepFun_atomless
    (P : Measure Ω) [IsFiniteMeasure P] (μ : Measure S)
    (W₀ : Ω → W) (X : Ω → S) (hW : Measurable W₀) (hX : Measurable X)
    (hindep : IndepFun W₀ X P) (hlaw : P.map X = μ)
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ)
    (hret : ∀ k l, Measurable (fun w ↦ retained w k l))
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i : Fin (n + 1))
    (hatom : ∀ᵐ w ∂P.map W₀, ∀ j k, j ≠ k →
      NullSingletonClass (μ.map (fun s ↦ row (w, s) j - row (w, s) k))) :
    ∀ᵐ ω ∂P, ∃! j, (W₀ ω, X ω) ∈ cavityCell retained row i j := by
  apply ae_existsUnique_mem_cavityCell_of_indepFun P μ W₀ X hW hX hindep hlaw
    retained row hret hrow i
  filter_upwards [hatom] with w hw
  intro j k hjk
  have := hw j k hjk
  exact measure_cavityScore_eq_zero_of_atomless μ retained row hrow i j k w







end OTSelector.Probability

end
