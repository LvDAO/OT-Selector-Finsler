import OTSelector.Probability.FiniteCellClassFlow
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawWindowPairFlow.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawWindowPairFlow`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerRelativeLawWindowPairFlow

**Conditions:** Finite disjoint measurable clock bins, a normalized reference matrix, nonnegative residual flow and a specified admissible pair window.

**Objects:** Masked retained/residual matrices with the same marginals and the extra residual mass bounded by window loss.

**Proof detail:** Partition the reference entries by whether their bin rectangle meets the window; move the omitted mask into the residual, use total mass to bound the retained scalar by one, and dominate bad-bin mass by the original window complement.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing; [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf), Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
Original reference-bin feasibility and measurable legal population reconstruction.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- A fixed reference pair-class mask retains its actual finite flow. -/
def maskedClockFlow {I J : Type*} (keep : I → J → Prop) (A : I → J → ℝ)
    (i : I) (j : J) : ℝ := by
  classical
  exact if keep i j then A i j else 0

theorem maskedClockFlow_add_complement {I J : Type*}
    (keep : I → J → Prop) (A : I → J → ℝ) (i : I) (j : J) :
    maskedClockFlow keep A i j + maskedClockFlow (fun i j ↦ ¬ keep i j) A i j = A i j := by
  classical
  by_cases h : keep i j <;> simp only [maskedClockFlow, h, not_true_eq_false,
    not_false_eq_true, ite_true, ite_false, add_zero, zero_add]

/-- Reference class rectangles disjoint from the original scalar window carry
at most the literal original pair-law loss outside that window. This is a pair
mass estimate; no source or target support replacement is used. -/
theorem actualClockClassFlow_masked_mass_le
    {I J : Type*} [Fintype I] [Fintype J]
    (γ : Measure (ℝ × ℝ)) [IsFiniteMeasure γ]
    (S : I → Set ℝ) (T : J → Set ℝ)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (hdS : Pairwise (Disjoint on S)) (hdT : Pairwise (Disjoint on T))
    (H : Set (ℝ × ℝ)) (bad : I → J → Prop)
    (hbad : ∀ i j, bad i j → S i ×ˢ T j ⊆ Hᶜ) :
    (∑ i, ∑ j, maskedClockFlow bad (actualClockClassFlow γ S T) i j) ≤ γ.real Hᶜ := by
  classical
  let R : I × J → Set (ℝ × ℝ) := fun p ↦ if bad p.1 p.2 then S p.1 ×ˢ T p.2 else ∅
  have hm (p : I × J) : MeasurableSet (R p) := by
    dsimp only [R]
    split_ifs
    · exact (hS p.1).prod (hT p.2)
    · exact MeasurableSet.empty
  have hd : Pairwise (Disjoint on R) := by
    intro p q hpq
    change Disjoint (R p) (R q)
    by_cases hp : bad p.1 p.2
    · by_cases hq : bad q.1 q.2
      · rw [show R p = S p.1 ×ˢ T p.2 from ite_eq_left hp,
          show R q = S q.1 ×ˢ T q.2 from ite_eq_left hq]
        apply disjoint_left.mpr
        intro x hx hy
        by_cases hi : p.1 = q.1
        · have hj : p.2 ≠ q.2 := fun hj ↦ hpq (Prod.ext hi hj)
          exact disjoint_left.mp (hdT hj) hx.2 hy.2
        · exact disjoint_left.mp (hdS hi) hx.1 hy.1
      · rw [show R q = ∅ from ite_eq_right hq]
        exact disjoint_empty _
    · rw [show R p = ∅ from ite_eq_right hp]
      exact empty_disjoint _
  have hsub : (⋃ p, R p) ⊆ Hᶜ := by
    intro x hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp hx
    by_cases hb : bad p.1 p.2
    · exact hbad p.1 p.2 hb ((ite_eq_left hb : R p = _) ▸ hp)
    · rw [show R p = ∅ from ite_eq_right hb] at hp
      exact False.elim hp
  calc
    _ = ∑ p : I × J, γ.real (R p) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hb : bad i j <;> simp only [maskedClockFlow, R, hb, ite_true, ite_false,
        actualClockClassFlow, measureReal_empty]
    _ = γ.real (⋃ p, R p) := (measureReal_iUnion_fintype hd hm).symm
    _ ≤ γ.real Hᶜ := measureReal_mono hsub

/-- A normalized retained reference scale is at most one because the actual
nonnegative residual completes it to total original conditional mass one. -/
theorem referenceRetainedScale_le_one
    {I J : Type*} [Fintype I] [Fintype J]
    (A Q : I → J → ℝ) (c : ℝ)
    (htotal : (∑ i, ∑ j, A i j) = 1) (hQ : ∀ i j, 0 ≤ Q i j)
    (hwhole : (∑ i, ∑ j, (c * A i j + Q i j)) = 1) : c ≤ 1 := by
  have hmassQ : 0 ≤ ∑ i, ∑ j, Q i j :=
    Finset.sum_nonneg fun i hi ↦ Finset.sum_nonneg fun j hj ↦ hQ i j
  have he : c + (∑ i, ∑ j, Q i j) = 1 := by
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, htotal, mul_one] using hwhole
  linarith

/-- Discarded retained reference pair classes are moved to the deterministic
residual. Exact original marginals and legality persist, and each unit of the
reference bad-pair mass is charged once. -/
theorem referencePairMask_split
    {I J : Type*} [Fintype I] [Fintype J]
    (keep allowed : I → J → Prop) (A Q : I → J → ℝ) (c : ℝ)
    (a : I → ℝ) (b : J → ℝ) (B L : ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hQ : ∀ i j, 0 ≤ Q i j)
    (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hrow : ∀ i, ∑ j, (c * A i j + Q i j) = a i)
    (hcol : ∀ j, ∑ i, (c * A i j + Q i j) = b j)
    (hzero : ∀ i j, ¬ allowed i j → A i j = 0 ∧ Q i j = 0)
    (hmassQ : (∑ i, ∑ j, Q i j) ≤ B)
    (hmassBad : (∑ i, ∑ j, maskedClockFlow (fun i j ↦ ¬ keep i j) A i j) ≤ L) :
    let P' := fun i j ↦ c * maskedClockFlow keep A i j
    let Q' := fun i j ↦ Q i j + c * maskedClockFlow (fun i j ↦ ¬ keep i j) A i j
    (∀ i j, 0 ≤ P' i j) ∧ (∀ i j, 0 ≤ Q' i j) ∧
    (∀ i, ∑ j, (P' i j + Q' i j) = a i) ∧
    (∀ j, ∑ i, (P' i j + Q' i j) = b j) ∧
    (∀ i j, ¬ allowed i j → P' i j = 0 ∧ Q' i j = 0) ∧
    (∑ i, ∑ j, Q' i j) ≤ B + L := by
  classical
  have hmnonneg (mask : I → J → Prop) (i j) : 0 ≤ maskedClockFlow mask A i j := by
    dsimp only [maskedClockFlow]
    split_ifs
    · exact hA i j
    · exact le_rfl
  have he (i j) : c * maskedClockFlow keep A i j +
      (Q i j + c * maskedClockFlow (fun i j ↦ ¬ keep i j) A i j) = c * A i j + Q i j := by
    calc
      _ = c * (maskedClockFlow keep A i j +
        maskedClockFlow (fun i j ↦ ¬ keep i j) A i j) + Q i j := by ring
      _ = _ := by rw [maskedClockFlow_add_complement]
  refine ⟨fun i j ↦ mul_nonneg hc (hmnonneg keep i j),
    fun i j ↦ add_nonneg (hQ i j) (mul_nonneg hc (hmnonneg _ i j)), ?_, ?_, ?_, ?_⟩
  · intro i
    simp_rw [he]
    exact hrow i
  · intro j
    simp_rw [he]
    exact hcol j
  · intro i j hij
    obtain ⟨ha, hq⟩ := hzero i j hij
    constructor <;> simp only [maskedClockFlow, ha, ite_self, mul_zero, hq, add_zero]
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    apply add_le_add hmassQ
    apply (mul_le_of_le_one_left (Finset.sum_nonneg fun i hi ↦
      Finset.sum_nonneg fun j hj ↦ hmnonneg _ i j) hc1).trans
    exact hmassBad

/-- A reference pair-class mask is static, so the actual label-dependent
retained and transferred residual edge weights remain measurable. -/
theorem measurable_maskedClockFlow
    {I J Z : Type*} [MeasurableSpace Z]
    (keep : I → J → Prop) (A : Z → I → J → ℝ)
    (hA : ∀ i j, Measurable (fun z ↦ A z i j)) (i : I) (j : J) :
    Measurable (fun z ↦ maskedClockFlow keep (A z) i j) := by
  classical
  by_cases h : keep i j
  · simpa only [maskedClockFlow, ite_eq_left h] using hA i j
  · simpa only [maskedClockFlow, ite_eq_right h] using
      (measurable_const : Measurable (fun _z : Z ↦ (0 : ℝ)))

/-- The original pair-window loss is transferred to a deterministic residual
of the exact original split. The retained reference scale bound is derived
from the actual conditional total mass, so the loss is charged without an
additional density-ratio constant. -/
theorem actualReferenceWindow_split
    {I J : Type*} [Fintype I] [Fintype J]
    (γ : Measure (ℝ × ℝ)) [IsFiniteMeasure γ]
    (S : I → Set ℝ) (T : J → Set ℝ)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (hdS : Pairwise (Disjoint on S)) (hdT : Pairwise (Disjoint on T))
    (H : Set (ℝ × ℝ)) (allowed : I → J → Prop)
    (Q : I → J → ℝ) (c : ℝ) (a : I → ℝ) (b : J → ℝ) (B : ℝ)
    (hc : 0 ≤ c) (hQ : ∀ i j, 0 ≤ Q i j)
    (htotalRef : (∑ i, ∑ j, actualClockClassFlow γ S T i j) = 1)
    (htotalActual : (∑ i, a i) = 1)
    (hrow : ∀ i, ∑ j, (c * actualClockClassFlow γ S T i j + Q i j) = a i)
    (hcol : ∀ j, ∑ i, (c * actualClockClassFlow γ S T i j + Q i j) = b j)
    (hzero : ∀ i j, ¬ allowed i j → actualClockClassFlow γ S T i j = 0 ∧ Q i j = 0)
    (hmassQ : (∑ i, ∑ j, Q i j) ≤ B) :
    let keep := fun i j ↦ ((S i ×ˢ T j) ∩ H).Nonempty
    let P' := fun i j ↦ c * maskedClockFlow keep (actualClockClassFlow γ S T) i j
    let Q' := fun i j ↦ Q i j + c * maskedClockFlow (fun i j ↦ ¬ keep i j)
      (actualClockClassFlow γ S T) i j
    (∀ i j, 0 ≤ P' i j) ∧ (∀ i j, 0 ≤ Q' i j) ∧
    (∀ i, ∑ j, (P' i j + Q' i j) = a i) ∧
    (∀ j, ∑ i, (P' i j + Q' i j) = b j) ∧
    (∀ i j, ¬ allowed i j → P' i j = 0 ∧ Q' i j = 0) ∧
    (∑ i, ∑ j, Q' i j) ≤ B + γ.real Hᶜ := by
  classical
  have hc1 : c ≤ 1 := referenceRetainedScale_le_one (actualClockClassFlow γ S T) Q c
    htotalRef hQ (by simp_rw [hrow]; exact htotalActual)
  apply referencePairMask_split _ allowed (actualClockClassFlow γ S T) Q c a b B (γ.real Hᶜ)
    (actualClockClassFlow_nonneg γ S T) hQ hc hc1 hrow hcol hzero hmassQ
  apply actualClockClassFlow_masked_mass_le γ S T hS hT hdS hdT H
  intro i j hbad p hp hpH
  exact hbad ⟨p, hp, hpH⟩

end OTSelector.Reconstruction

end
end
