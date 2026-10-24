import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import OTSelector.Finite.BlockMaxValueComparison
import OTSelector.Finite.MaxCardValueSigned
import OTSelector.Finite.PartialMatching

/-!
Conditions: Measurable natural cloud sizes and every measurable edge-cost coordinate, with a measurable sample-dependent upper bound on all edge costs.

Objects: The actual optimal maximum-cardinality matching value as a measurable real random variable, including zero-sized clouds.

Proof detail: Encode finite partial matchings by a countable family of finite subsets of natural pairs, give invalid candidates a measurable dominating sentinel and identify the true attained optimum with their countable infimum.

References: Reinhard Diestel: Chapter 2 opening matching definition and Section 2.1, first three chapter pages; D. H. Fremlin: Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces.
Relation: A local countable coding proof of optimizer-value measurability. It does not require a measurable choice of one optimal matching or fixed realized cloud sizes.
-/


/-!
# Measurability of cloud matching values with random sizes

The maximum-cardinality value of a cloud matching depends on the random cloud
sizes.  We prove that it is measurable whenever every edge cost is measurable in
the sample and uniformly bounded above.  The proof writes the value as a
countable infimum over finite partial matchings of `ℕ × ℕ`: valid matchings
inside the two clouds give their actual cost, while invalid ones contribute a
sentinel that is at least any valid cost.  The optimal matching attains the
infimum, so the sentinel does not change the value.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section
namespace OTSelector.Probability

open OTSelector

/-- A finite partial matching of `ℕ × ℕ` with a prescribed cardinality and range,
expressed without dependent types. -/
def IsFiniteMatching (σ : Finset (ℕ × ℕ)) (n m : ℕ) : Prop :=
  σ.card = min n m ∧
    (∀ p ∈ σ, p.1 < n ∧ p.2 < m) ∧
    (∀ p ∈ σ, ∀ q ∈ σ, p.1 = q.1 → p = q) ∧
    (∀ p ∈ σ, ∀ q ∈ σ, p.2 = q.2 → p = q)

/-- A valid finite matching costs at most the sum of its edge values in any
fixed-size matrix. -/
theorem maxCardValue_le_sum_of_isFiniteMatching {n m : ℕ} {e : ℕ → ℕ → ℝ}
    {σ : Finset (ℕ × ℕ)} (hσ : IsFiniteMatching σ n m) :
    PartialMatching.maxCardValue (fun i : Fin n => fun j : Fin m => e i j) ≤
      ∑ p ∈ σ, e p.1 p.2 := by
  classical
  obtain ⟨hcard, hrange, hrow, hcol⟩ := hσ
  let f : {p // p ∈ σ} → Fin n × Fin m := fun q =>
    (⟨q.1.1, (hrange q.1 q.2).1⟩, ⟨q.1.2, (hrange q.1 q.2).2⟩)
  have hf_inj : Set.InjOn f ↑σ.attach := by
    intro q _ q' _ h
    have h1 : q.1.1 = q'.1.1 := congrArg (fun p : Fin n × Fin m => (p.1 : ℕ)) h
    exact Subtype.ext (hrow q.1 q.2 q'.1 q'.2 h1)
  let τ : PartialMatching n m :=
    { edges := σ.attach.image f
      row_inj := by
        intro x hx y hy hrowxy
        obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hx
        obtain ⟨q', -, hq'⟩ := Finset.mem_image.mp hy
        have hval : q.1.1 = q'.1.1 := by
          have h := hrowxy
          rw [← hq, ← hq'] at h
          exact congrArg (fun p : Fin n => (p : ℕ)) h
        have hqq : q = q' := Subtype.ext (hrow q.1 q.2 q'.1 q'.2 hval)
        rw [← hq, ← hq', hqq]
      col_inj := by
        intro x hx y hy hcolxy
        obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hx
        obtain ⟨q', -, hq'⟩ := Finset.mem_image.mp hy
        have hval : q.1.2 = q'.1.2 := by
          have h := hcolxy
          rw [← hq, ← hq'] at h
          exact congrArg (fun p : Fin m => (p : ℕ)) h
        have hqq : q = q' := Subtype.ext (hcol q.1 q.2 q'.1 q'.2 hval)
        rw [← hq, ← hq', hqq] }
  have hcardτ : τ.card = min n m := by
    show (σ.attach.image f).card = min n m
    rw [Finset.card_image_of_injOn hf_inj, Finset.card_attach, hcard]
  have hcostτ : τ.cost (fun i j => e i j) = ∑ p ∈ σ, e p.1 p.2 := by
    show ∑ x ∈ σ.attach.image f, e x.1 x.2 = ∑ p ∈ σ, e p.1 p.2
    rw [Finset.sum_image hf_inj]
    have hattach : ∑ q ∈ σ.attach, e (f q).1 (f q).2 =
        ∑ p ∈ σ, e p.1 p.2 := by
      simpa only [f] using
        (Finset.sum_attach σ (fun p : ℕ × ℕ => e p.1 p.2))
    exact hattach
  exact (PartialMatching.maxCardValue_le_of_card _ hcardτ).trans_eq hcostτ

/-- The diagonal matching bounds the value by the cardinality times any uniform
edge upper bound. -/
theorem maxCardValue_le_card_mul_of_le {n m : ℕ} {e : ℕ → ℕ → ℝ} {B : ℝ}
    (hB : ∀ i j, e i j ≤ B) :
    PartialMatching.maxCardValue (fun i : Fin n => fun j : Fin m => e i j) ≤
      ((min n m : ℕ) : ℝ) * B := by
  have hcard : (PartialMatching.diagonal n m).card = min n m :=
    PartialMatching.card_diagonal n m
  have hle : PartialMatching.maxCardValue (fun i : Fin n => fun j : Fin m => e i j) ≤
      (PartialMatching.diagonal n m).cost (fun i j => e i j) :=
    PartialMatching.maxCardValue_le_of_card _ hcard
  have hcost : (PartialMatching.diagonal n m).cost (fun i j => e i j) ≤
      ((min n m : ℕ) : ℝ) * B := by
    unfold PartialMatching.cost
    calc ∑ p ∈ (PartialMatching.diagonal n m).edges, e p.1 p.2
        ≤ ∑ _p ∈ (PartialMatching.diagonal n m).edges, B :=
          Finset.sum_le_sum fun p _ => hB p.1 p.2
      _ = ((min n m : ℕ) : ℝ) * B := by
          rw [Finset.sum_const, nsmul_eq_mul]
          congr 1
          exact_mod_cast hcard
  exact hle.trans hcost

/-- The validity condition of a finite matching is measurable in the random
cloud sizes. -/
theorem measurableSet_isFiniteMatching {Ω : Type*} [MeasurableSpace Ω]
    (σ : Finset (ℕ × ℕ)) {Np Nm : Ω → ℕ} (hNp : Measurable Np) (hNm : Measurable Nm) :
    MeasurableSet {ω | IsFiniteMatching σ (Np ω) (Nm ω)} := by
  classical
  have h1 : MeasurableSet {ω | σ.card = min (Np ω) (Nm ω)} :=
    measurableSet_eq_fun (f := fun _ : Ω => σ.card)
      (g := fun ω => min (Np ω) (Nm ω)) measurable_const (hNp.min hNm)
  have h2 : MeasurableSet {ω | ∀ p ∈ σ, p.1 < Np ω ∧ p.2 < Nm ω} := by
    have hset : {ω | ∀ p ∈ σ, p.1 < Np ω ∧ p.2 < Nm ω} =
        ⋂ p ∈ σ, ({ω | p.1 < Np ω} ∩ {ω | p.2 < Nm ω}) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
    rw [hset]
    exact Finset.measurableSet_biInter σ fun p _ =>
      (hNp measurableSet_Ioi).inter (hNm measurableSet_Ioi)
  have h3 : MeasurableSet {ω : Ω | ∀ p ∈ σ, ∀ q ∈ σ, p.1 = q.1 → p = q} := by
    by_cases h : ∀ p ∈ σ, ∀ q ∈ σ, p.1 = q.1 → p = q
    · simp [h]
    · simp [h]
  have h4 : MeasurableSet {ω : Ω | ∀ p ∈ σ, ∀ q ∈ σ, p.2 = q.2 → p = q} := by
    by_cases h : ∀ p ∈ σ, ∀ q ∈ σ, p.2 = q.2 → p = q
    · simp [h]
    · simp [h]
  simp only [IsFiniteMatching, Set.setOf_and]
  exact h1.inter (h2.inter (h3.inter h4))

/-- The maximum-cardinality value of a random-size cloud matching. -/
noncomputable def cloudValueNat {Ω : Type*} (e : Ω → ℕ → ℕ → ℝ) (Np Nm : Ω → ℕ)
    (ω : Ω) : ℝ :=
  PartialMatching.maxCardValue (fun i : Fin (Np ω) => fun j : Fin (Nm ω) => e ω i j)

/-- Measurability of the random-size cloud value from coordinatewise
measurability and a measurable pointwise upper bound on edge costs. -/
theorem measurable_cloudValueNat {Ω : Type*} [MeasurableSpace Ω]
    {e : Ω → ℕ → ℕ → ℝ} (he : ∀ i j, Measurable fun ω => e ω i j)
    {Np Nm : Ω → ℕ} (hNp : Measurable Np) (hNm : Measurable Nm)
    {B : Ω → ℝ} (hB : Measurable B) (hBbound : ∀ ω i j, e ω i j ≤ B ω) :
    Measurable (cloudValueNat e Np Nm) := by
  classical
  let F : Finset (ℕ × ℕ) → Ω → ℝ := fun σ ω =>
    if IsFiniteMatching σ (Np ω) (Nm ω) then ∑ p ∈ σ, e ω p.1 p.2
    else ((min (Np ω) (Nm ω) : ℕ) : ℝ) * B ω
  have hF (σ : Finset (ℕ × ℕ)) : Measurable (F σ) := by
    unfold F
    apply Measurable.ite
    · exact measurableSet_isFiniteMatching σ hNp hNm
    · exact Finset.measurable_sum _ fun p _ => he p.1 p.2
    · exact Measurable.mul (Measurable.comp measurable_from_nat (hNp.min hNm)) hB
  have hval : cloudValueNat e Np Nm = fun ω => ⨅ σ : Finset (ℕ × ℕ), F σ ω := by
    funext ω
    apply le_antisymm
    · refine le_ciInf fun σ => ?_
      by_cases hσ : IsFiniteMatching σ (Np ω) (Nm ω)
      · rw [show F σ ω = ∑ p ∈ σ, e ω p.1 p.2 from if_pos hσ]
        exact maxCardValue_le_sum_of_isFiniteMatching hσ
      · rw [show F σ ω = ((min (Np ω) (Nm ω) : ℕ) : ℝ) * B ω from if_neg hσ]
        exact maxCardValue_le_card_mul_of_le (fun i j => hBbound ω i j)
    · obtain ⟨τ, hcard, hcost⟩ :=
        PartialMatching.exists_cost_eq_maxCardValue
          (fun i : Fin (Np ω) => fun j : Fin (Nm ω) => e ω i j)
      let σ : Finset (ℕ × ℕ) :=
        τ.edges.image fun p => ((p.1 : ℕ), (p.2 : ℕ))
      have hσ : IsFiniteMatching σ (Np ω) (Nm ω) := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · show (τ.edges.image _).card = min (Np ω) (Nm ω)
          rw [Finset.card_image_of_injOn]
          · exact hcard
          · intro p _ q _ h
            have h1 : (p.1 : ℕ) = (q.1 : ℕ) := congrArg Prod.fst h
            have h2 : (p.2 : ℕ) = (q.2 : ℕ) := congrArg Prod.snd h
            exact Prod.ext (Fin.ext h1) (Fin.ext h2)
        · intro p hp
          obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
          exact ⟨q.1.isLt, q.2.isLt⟩
        · intro p hp q hq hrow
          obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
          obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
          have hrow' : (p'.1 : ℕ) = (q'.1 : ℕ) := hrow
          have := τ.row_inj p' hp' q' hq' (Fin.ext hrow')
          subst this
          rfl
        · intro p hp q hq hcol
          obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
          obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
          have hcol' : (p'.2 : ℕ) = (q'.2 : ℕ) := hcol
          have := τ.col_inj p' hp' q' hq' (Fin.ext hcol')
          subst this
          rfl
      have hFσ : F σ ω = ∑ p ∈ σ, e ω p.1 p.2 := if_pos hσ
      have hσcost : ∑ p ∈ σ, e ω p.1 p.2 =
          τ.cost (fun i : Fin (Np ω) => fun j : Fin (Nm ω) => e ω i j) := by
        show ∑ p ∈ τ.edges.image (fun p : Fin (Np ω) × Fin (Nm ω) =>
          ((p.1 : ℕ), (p.2 : ℕ))), e ω p.1 p.2 = τ.cost _
        rw [Finset.sum_image]
        · unfold PartialMatching.cost
          rfl
        · intro p _ q _ h
          have h1 : (p.1 : ℕ) = (q.1 : ℕ) := congrArg Prod.fst h
          have h2 : (p.2 : ℕ) = (q.2 : ℕ) := congrArg Prod.snd h
          exact Prod.ext (Fin.ext h1) (Fin.ext h2)
      have hbdd : BddBelow (Set.range (fun σ : Finset (ℕ × ℕ) => F σ ω)) := by
        let Rect : ℝ := ∑ i ∈ Finset.range (Np ω), ∑ j ∈ Finset.range (Nm ω), |e ω i j|
        refine ⟨min (-Rect) (((min (Np ω) (Nm ω) : ℕ) : ℝ) * B ω), ?_⟩
        rintro v ⟨σ', rfl⟩
        change min (-Rect) (((min (Np ω) (Nm ω) : ℕ) : ℝ) * B ω) ≤ F σ' ω
        by_cases hσ' : IsFiniteMatching σ' (Np ω) (Nm ω)
        · rw [show F σ' ω = ∑ p ∈ σ', e ω p.1 p.2 from if_pos hσ']
          have hneg : -∑ p ∈ σ', |e ω p.1 p.2| ≤ ∑ p ∈ σ', e ω p.1 p.2 := by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_le_sum (fun p _ => neg_abs_le (e ω p.1 p.2))
          have hleRect : ∑ p ∈ σ', |e ω p.1 p.2| ≤ Rect := by
            have hsub : σ' ⊆ (Finset.range (Np ω)).product (Finset.range (Nm ω)) := by
              intro p hp
              obtain ⟨h1, h2⟩ := hσ'.2.1 p hp
              exact Finset.mem_product.mpr
                ⟨Finset.mem_range.mpr h1, Finset.mem_range.mpr h2⟩
            calc ∑ p ∈ σ', |e ω p.1 p.2|
                ≤ ∑ p ∈ (Finset.range (Np ω)).product (Finset.range (Nm ω)),
                    |e ω p.1 p.2| :=
                  Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => abs_nonneg _)
              _ = Rect := by
                  simp only [Rect]
                  exact Finset.sum_product (Finset.range (Np ω))
                    (Finset.range (Nm ω)) (fun p => |e ω p.1 p.2|)
          have hRect : -Rect ≤ ∑ p ∈ σ', e ω p.1 p.2 := by linarith
          exact (min_le_left _ _).trans hRect
        · rw [show F σ' ω = ((min (Np ω) (Nm ω) : ℕ) : ℝ) * B ω from if_neg hσ']
          exact min_le_right _ _
      calc ⨅ σ, F σ ω ≤ F σ ω := ciInf_le hbdd σ
        _ = ∑ p ∈ σ, e ω p.1 p.2 := hFσ
        _ = τ.cost _ := hσcost
        _ = cloudValueNat e Np Nm ω := by rw [cloudValueNat, hcost]
  rw [hval]
  exact Measurable.iInf hF

end OTSelector.Probability
