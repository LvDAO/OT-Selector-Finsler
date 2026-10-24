import OTSelector.Finite.NormalizedReferenceHallSplit
import OTSelector.Finite.OrderedHallFlow
import OTSelector.Transport.Coupling.ResidualFinitePopulation
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawFiniteReferenceFlow.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawFiniteReferenceFlow`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerRelativeLawFiniteReferenceFlow

**Conditions:** A finite family of original reference class flows satisfies the displayed legal/marginal/positive-intensity assumptions and actual data are within the corresponding tolerances.

**Objects:** Measurable retained/residual reference-selected flows and one positive tolerance per finite reference.

**Proof detail:** Define each selected matrix by composition with its finite reference selector; choose the deterministic residual-splitting tolerance for each reference and preserve exact original marginals after normalization.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106), Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=39), Section 2.6, Remarks 2.27–2.28, pp. 35–37, equations (2.31)–(2.37); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [OTSelector project, Measurable forward weighted Hall construction](main.tex#measurable-forward-hall), main.tex label measurable-forward-hall, line 6889.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
Explicit normalized finite-reference class splitting for the unchanged original
population, with measurable retained and residual flows and a uniform relative
residual mass bound. All finite Hall constraints are derived from actual legal
class matrices.
-/

open MeasureTheory ProbabilityTheory Function
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Frozen reference class flow, normalized on the literal original label law. -/
def finiteReferenceRetainedClockFlow
    {C Z : Type*} {M L : ℕ} (reference : Z → C)
    (P₀ : C → Fin M → Fin L → ℝ) (η : ℝ) (d : Z → ℝ)
    (z : Z) (i : Fin M) (j : Fin L) : ℝ := (1 - η) * P₀ (reference z) i j / d z

/-- Explicit measurable residual class flow using a finite selected reference
at each original label. -/
def finiteReferenceResidualClockFlow
    {C Z : Type*} {M L : ℕ} (reference : Z → C)
    (a₀ : C → Fin M → ℝ) (b₀ : C → Fin L → ℝ) (η : ℝ)
    (d : Z → ℝ) (a : Z → Fin M → ℝ) (b : Z → Fin L → ℝ)
    (z : Z) (i : Fin M) (j : Fin L) : ℝ :=
  referenceResidualClockFlow (a₀ (reference z)) (b₀ (reference z)) η
    (fun i ↦ d z * a z i) (fun j ↦ d z * b z j) i j / d z

theorem measurable_finiteReferenceRetainedClockFlow
    {C Z : Type*} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
    [MeasurableSpace Z] {M L : ℕ}
    (reference : Z → C) (href : Measurable reference)
    (P₀ : C → Fin M → Fin L → ℝ) (η : ℝ) (d : Z → ℝ) (hd : Measurable d)
    (i : Fin M) (j : Fin L) :
    Measurable (fun z ↦ finiteReferenceRetainedClockFlow reference P₀ η d z i j) := by
  have hm := (measurable_of_finite (fun c ↦ P₀ c i j)).comp href
  exact measurable_div.comp
    ((measurable_mul.comp (measurable_const.prodMk hm)).prodMk hd)

theorem measurable_finiteReferenceResidualClockFlow
    {C Z : Type*} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
    [MeasurableSpace Z] {M L : ℕ}
    (reference : Z → C) (href : Measurable reference)
    (a₀ : C → Fin M → ℝ) (b₀ : C → Fin L → ℝ) (η : ℝ)
    (d : Z → ℝ) (hd : Measurable d) (a : Z → Fin M → ℝ) (b : Z → Fin L → ℝ)
    (ha : ∀ i, Measurable (fun z ↦ a z i)) (hb : ∀ j, Measurable (fun z ↦ b z j))
    (i : Fin M) (j : Fin L) :
    Measurable (fun z ↦ finiteReferenceResidualClockFlow reference a₀ b₀ η d a b z i j) := by
  have hsa (i : Fin M) : Measurable (fun z ↦ d z * a z i - (1 - η) * a₀ (reference z) i) :=
    measurable_sub.comp ((measurable_mul.comp (hd.prodMk (ha i))).prodMk
      (measurable_mul.comp (measurable_const.prodMk
        ((measurable_of_finite (fun c ↦ a₀ c i)).comp href))))
  have htb (j : Fin L) : Measurable (fun z ↦ d z * b z j - (1 - η) * b₀ (reference z) j) :=
    measurable_sub.comp ((measurable_mul.comp (hd.prodMk (hb j))).prodMk
      (measurable_mul.comp (measurable_const.prodMk
        ((measurable_of_finite (fun c ↦ b₀ c j)).comp href))))
  exact measurable_div.comp
    ((measurable_orderedClockFlow _ _ hsa htb i j).prodMk hd)

/-- One positive tolerance for each finite actual reference yields the exact
original conditional split and a uniform `η+ε` residual bound at every label
satisfying its chosen reference tolerance. -/
theorem exists_finite_reference_classSplit_tolerances
    {C : Type*} [Fintype C] {M L : ℕ}
    (allowed : Fin M → Fin L → Prop)
    (horder : ∀ i i' j j', i ≤ i' → j' ≤ j → allowed i' j' → allowed i j)
    (a₀ : C → Fin M → ℝ) (b₀ : C → Fin L → ℝ)
    (P₀ : C → Fin M → Fin L → ℝ) (d₀ : C → ℝ)
    (hP₀ : ∀ c i j, 0 ≤ P₀ c i j)
    (hrow₀ : ∀ c i, ∑ j, P₀ c i j = a₀ c i) (hcol₀ : ∀ c j, ∑ i, P₀ c i j = b₀ c j)
    (hzero₀ : ∀ c i j, ¬ allowed i j → P₀ c i j = 0)
    (hd₀ : ∀ c, 0 < d₀ c) (htotal₀ : ∀ c, ∑ i, a₀ c i = d₀ c)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ δ : C → ℝ, (∀ c, 0 < δ c) ∧
      ∀ (c : C) (d ε : ℝ) (a : Fin M → ℝ) (b : Fin L → ℝ) (A : Fin M → Fin L → ℝ),
        0 < d → 0 ≤ ε → d ≤ (1 + ε) * d₀ c →
        (∀ i j, 0 ≤ A i j) → (∀ i, ∑ j, A i j = a i) → (∀ j, ∑ i, A i j = b j) →
        (∀ i j, ¬ allowed i j → A i j = 0) → (∑ i, a i = 1) →
        (∀ i, |d * a i - a₀ c i| ≤ δ c) → (∀ j, |d * b j - b₀ c j| ≤ δ c) →
        let Q := referenceResidualClockFlow (a₀ c) (b₀ c) η (fun i ↦ d * a i) (fun j ↦ d * b j)
        (∀ i j, 0 ≤ (1 - η) * P₀ c i j / d) ∧
        (∀ i j, 0 ≤ Q i j / d) ∧
        (∀ i, ∑ j, ((1 - η) * P₀ c i j / d + Q i j / d) = a i) ∧
        (∀ j, ∑ i, ((1 - η) * P₀ c i j / d + Q i j / d) = b j) ∧
        (∀ i j, ¬ allowed i j → (1 - η) * P₀ c i j / d = 0 ∧ Q i j / d = 0) ∧
        (∑ i, ∑ j, Q i j / d) ≤ η + ε := by
  classical
  have h (c : C) := exists_tolerance_normalized_reference_classSplit allowed horder
    (a₀ c) (b₀ c) (P₀ c) (hP₀ c) (hrow₀ c) (hcol₀ c) (hzero₀ c)
    (d₀ c) η (hd₀ c) (htotal₀ c) hη hη1
  choose δ hδ hsplit using h
  exact ⟨δ, hδ, hsplit⟩

end OTSelector.Reconstruction

end
end
