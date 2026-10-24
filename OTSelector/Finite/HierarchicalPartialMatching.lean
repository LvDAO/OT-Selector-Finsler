import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import OTSelector.Finite.Assignment
import OTSelector.Finite.HierarchicalAssignment
import OTSelector.Finite.PartialMatching

/-!
# Finite.HierarchicalPartialMatching

**Conditions:** Nested finite partitions, possibly unequal cloud sizes, nonnegative base/weights and the displayed multiscale cost domination.

**Objects:** A maximum-cardinality partial matching and its histogram-discrepancy cost bound.

**Proof detail:** Pad the smaller cloud with zero-cost dummy points carrying a fresh option label, apply the equal-size hierarchical assignment construction, and restrict its permutation to real endpoints; dummy counts give the total size discrepancy.

**Sources:** [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (generalization): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Hierarchical cost bounds for maximum-cardinality partial matchings

The equal-count hierarchical assignment bound is transferred to two point clouds
of possibly different sizes.  Pad the smaller cloud with zero-cost dummy points
whose cells are a fresh `none` label, apply the equal-count theorem to the
resulting square assignment, and restrict the permutation to the real points.
The dummy cell contributes exactly the count difference, so the resulting
maximum-cardinality partial matching satisfies the same multiscale histogram
bound up to that difference.

This is the deterministic core of the Poisson matching pressure: the histogram
discrepancies are the only stochastic inputs.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector.Reconstruction

/-- Counting real points through an option-labelled cell agrees with the original
count on `some` labels. -/
theorem partitionCount_option_some
    {X : Type*} {K a b : ℕ} {C : Fin K → Type*} [∀ k, Fintype (C k)]
    (cell : (k : Fin K) → X → C k) (x : Fin a → X)
    (hab : a ≤ b) (k : Fin K) (c : C k) :
    partitionCount (fun i : Fin b =>
      if h : (i : ℕ) < a then some (cell k (x ⟨i, h⟩)) else none) (some c) =
      partitionCount (fun i : Fin a => cell k (x i)) c := by
  classical
  simp only [partitionCount, partitionIndicator]
  rw [Finset.sum_fin_eq_sum_range (fun i : Fin b => _),
    Finset.sum_fin_eq_sum_range (fun i : Fin a => _)]
  trans ∑ i ∈ Finset.range b,
    (if h : (i : ℕ) < a then
      (if cell k (x ⟨i, h⟩) = c then (1 : ℝ) else 0) else 0)
  · apply Finset.sum_congr rfl
    intro i hi
    have hib : i < b := Finset.mem_range.mp hi
    rw [dif_pos hib]
    by_cases hia : i < a
    · simp [hia]
    · simp [hia]
  · rw [show b = a + (b - a) by omega, Finset.sum_range_add]
    have h2 : (∑ i ∈ Finset.range (b - a),
        (if h : ((a + i : ℕ) < a) then
          (if cell k (x ⟨a + i, h⟩) = c then (1 : ℝ) else 0) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [dif_neg (by omega)]
    rw [h2, add_zero]

/-- The dummy label is used exactly by the `b - a` padded points. -/
theorem partitionCount_none_of_padding
    {C : Type*} [Fintype C] {a b : ℕ} (hab : a ≤ b)
    (f : Fin b → Option C)
    (h : ∀ i : Fin b, f i = none ↔ ¬ (i : ℕ) < a) :
    partitionCount f (none : Option C) = ((b - a : ℕ) : ℝ) := by
  classical
  simp only [partitionCount, partitionIndicator]
  rw [Finset.sum_fin_eq_sum_range]
  trans ∑ i ∈ Finset.range b, (if (i : ℕ) < a then (0 : ℝ) else 1)
  · apply Finset.sum_congr rfl
    intro i hi
    have hib : i < b := Finset.mem_range.mp hi
    rw [dif_pos hib]
    by_cases hia : i < a
    · rw [if_pos hia]
      have hne : f ⟨i, hib⟩ ≠ none := fun he => (h ⟨i, hib⟩).mp he hia
      simp [hne]
    · rw [if_neg hia]
      have hnone : f ⟨i, hib⟩ = none := (h ⟨i, hib⟩).mpr hia
      simp [hnone]
  · rw [show b = a + (b - a) by omega, Finset.sum_range_add]
    have h1 : (∑ i ∈ Finset.range a, (if (i : ℕ) < a then (0 : ℝ) else 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [if_pos (Finset.mem_range.mp hi)]
    have h2 : (∑ i ∈ Finset.range (b - a),
        (if ((a + i : ℕ) < a) then (0 : ℝ) else 1)) = ((b - a : ℕ) : ℝ) := by
      have hterm : ∀ i ∈ Finset.range (b - a),
          (if ((a + i : ℕ) < a) then (0 : ℝ) else 1) = 1 := by
        intro i hi
        rw [if_neg (by omega)]
      rw [Finset.sum_congr rfl hterm]
      simp
    rw [h1, h2, zero_add]
    congr 1
    omega



/-- Maximum-cardinality partial matchings obey the multiscale histogram bound with
the count difference added to the discrepancy. -/
theorem exists_partialMatching_hierarchy_cost_bound
    {X : Type*} {K a b : ℕ} {C : Fin K → Type*} [∀ k, Fintype (C k)]
    (cell : (k : Fin K) → X → C k)
    (hnested : ∀ (k l : Fin K), k ≤ l → ∀ x y : X,
      cell l x = cell l y → cell k x = cell k y)
    (x : Fin a → X) (y : Fin b → X)
    (cost : Fin a → Fin b → ℝ)
    (base : ℝ) (hb : 0 ≤ base) (weight : Fin K → ℝ) (hw : ∀ k, 0 ≤ weight k)
    (hcost : ∀ i j, cost i j ≤
      base + ∑ k, weight k * partitionDistance (cell k (x i)) (cell k (y j))) :
    ∃ σ : PartialMatching a b,
      σ.card = min a b ∧
      σ.cost cost ≤ (max a b : ℝ) * base +
        (1 / 2 : ℝ) * ∑ k, weight k *
          (∑ c, |partitionCount (cell k ∘ x) c - partitionCount (cell k ∘ y) c| +
            |(a : ℝ) - (b : ℝ)|) := by
  classical
  rcases le_total a b with hab | hba
  · -- Pad the source cloud with dummy points.
    let xs : Fin b → X ⊕ Unit := fun i =>
      if h : (i : ℕ) < a then Sum.inl (x ⟨i, h⟩) else Sum.inr ⟨⟩
    let ys : Fin b → X ⊕ Unit := fun j => Sum.inl (y j)
    let cellP : (k : Fin K) → X ⊕ Unit → Option (C k) := fun k z =>
      match z with
      | Sum.inl w => some (cell k w)
      | Sum.inr _ => none
    let costP : Fin b → Fin b → ℝ := fun i j =>
      if h : (i : ℕ) < a then cost ⟨i, h⟩ j else 0
    have hnestP : ∀ (k l : Fin K), k ≤ l → ∀ u v : X ⊕ Unit,
        cellP l u = cellP l v → cellP k u = cellP k v := by
      intro k l hkl u v huv
      cases u with
      | inl u =>
          cases v with
          | inl v =>
              simp only [cellP]
              exact congrArg some (hnested k l hkl u v
                (by simpa only [cellP, Option.some.injEq] using huv))
          | inr v => simp [cellP] at huv
      | inr u =>
          cases v with
          | inl v => simp [cellP] at huv
          | inr v => simp [cellP]
    have hcostP : ∀ i j : Fin b, costP i j ≤ base + ∑ k, weight k *
        partitionDistance (cellP k (xs i)) (cellP k (ys j)) := by
      intro i j
      by_cases hi : (i : ℕ) < a
      · have hpd : ∀ k, partitionDistance (cellP k (xs i)) (cellP k (ys j)) =
            partitionDistance (cell k (x ⟨i, hi⟩)) (cell k (y j)) := by
          intro k
          simp only [cellP, xs, ys, dif_pos hi]
          simp only [partitionDistance, Option.some.injEq]
        simp only [costP, dif_pos hi]
        simpa only [hpd] using hcost ⟨i, hi⟩ j
      · have hsum : 0 ≤ ∑ k, weight k *
            partitionDistance (cellP k (xs i)) (cellP k (ys j)) :=
          Finset.sum_nonneg fun k _ ↦
            mul_nonneg (hw k) (partitionDistance_bounds _ _).1
        simp only [costP, dif_neg hi]
        linarith
    obtain ⟨σ, hσ⟩ := exists_hierarchical_assignment_cost_bound
      (cell := cellP) hnestP xs ys costP base weight hcostP
    have hσ' : assignmentCost costP σ ≤ (b : ℝ) * base + (1 / 2 : ℝ) *
        ∑ k, weight k * ∑ o : Option (C k),
          |partitionCount (cellP k ∘ xs) o - partitionCount (cellP k ∘ ys) o| := by
      simpa only [Fintype.card_fin] using hσ
    -- The restricted matching.
    let emb : Fin a → Fin b := fun i => ⟨i, lt_of_lt_of_le i.isLt hab⟩
    have hemb : Function.Injective emb := fun i j h =>
      Fin.ext (by simpa [emb] using congrArg Fin.val h)
    let e : Fin a → Fin a × Fin b := fun i => (i, σ (emb i))
    have he : Function.Injective e := fun i j h => congrArg Prod.fst h
    let σpm : PartialMatching a b :=
      { edges := Finset.univ.image e
        row_inj := by
          intro p hp q hq hrow
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
          exact congrArg e hrow
        col_inj := by
          intro p hp q hq hcol
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
          have hval : (σ (emb i)).val = (σ (emb j)).val := by
            simpa only using congrArg Fin.val hcol
          have hσeq : σ (emb i) = σ (emb j) := Fin.ext hval
          have hemb_eq : emb i = emb j := σ.injective hσeq
          have : (⟨i, i.isLt⟩ : Fin a) = ⟨j, j.isLt⟩ := hemb hemb_eq
          exact congrArg e this }
    have hcard : σpm.card = min a b := by
      simp only [PartialMatching.card, σpm]
      rw [Finset.card_image_of_injective _ he]
      simp [min_eq_left hab]
    refine ⟨σpm, hcard, ?_⟩
    -- Cost comparison: the dummy rows contribute zero.
    have hcost_le : σpm.cost cost ≤ assignmentCost costP σ := by
      have hsub : Finset.univ.image emb ⊆ (Finset.univ : Finset (Fin b)) := by
        intro z _; exact Finset.mem_univ z
      have hnonneg : ∀ z ∈ (Finset.univ : Finset (Fin b)), z ∉ Finset.univ.image emb →
          0 ≤ costP z (σ z) := by
        intro z _ hz
        have hza : ¬ (z : ℕ) < a := by
          intro hlt
          exact hz (Finset.mem_image.mpr
            ⟨⟨z, hlt⟩, Finset.mem_univ _, by simp [emb, Fin.ext_iff]⟩)
        simp only [costP, dif_neg hza]
        exact le_refl 0
      have hcost_pm : σpm.cost cost = ∑ i : Fin a, cost i (σ (emb i)) := by
        simp only [PartialMatching.cost, σpm, e]
        rw [Finset.sum_image]
        intro i _ j _ hij
        exact congrArg Prod.fst hij
      have hreal : (∑ i : Fin a, cost i (σ (emb i))) =
          ∑ z ∈ Finset.univ.image emb, costP z (σ z) := by
        rw [Finset.sum_image]
        · apply Finset.sum_congr rfl
          intro i _
          simp only [emb, costP, dif_pos i.isLt]
        · intro i _ j _ hij
          exact hemb hij
      calc
        σpm.cost cost = ∑ i : Fin a, cost i (σ (emb i)) := hcost_pm
        _ = ∑ z ∈ Finset.univ.image emb, costP z (σ z) := hreal
        _ ≤ ∑ z : Fin b, costP z (σ z) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
    -- The option discrepancy splits into real blocks plus the count difference.
    have hcount : ∀ k : Fin K,
        (∑ o : Option (C k),
          |partitionCount (cellP k ∘ xs) o - partitionCount (cellP k ∘ ys) o|) =
        (∑ c, |partitionCount (cell k ∘ x) c - partitionCount (cell k ∘ y) c|) +
          |(a : ℝ) - (b : ℝ)| := by
      intro k
      have hS (c : C k) : partitionCount (cellP k ∘ xs) (some c) =
          partitionCount (cell k ∘ x) c := by
        rw [show (cellP k ∘ xs) =
            (fun i : Fin b => if h : (i : ℕ) < a then
              some (cell k (x ⟨i, h⟩)) else none) from by
          funext i
          simp only [Function.comp_apply, cellP, xs]
          split_ifs <;> rfl]
        simpa only [Function.comp_def] using partitionCount_option_some cell x hab k c
      have hT (c : C k) : partitionCount (cellP k ∘ ys) (some c) =
          partitionCount (cell k ∘ y) c := by
        simp only [partitionCount, partitionIndicator, Function.comp_apply, cellP, ys,
          Option.some.injEq]
      have hSn : partitionCount (cellP k ∘ xs) none = ((b - a : ℕ) : ℝ) := by
        apply partitionCount_none_of_padding hab
        intro i
        simp only [Function.comp_apply, cellP, xs]
        by_cases hlt : (i : ℕ) < a
        · simp [hlt]
        · simp [hlt]
      have hTn : partitionCount (cellP k ∘ ys) none = 0 := by
        simp only [partitionCount, partitionIndicator, Function.comp_apply, cellP, ys]
        simp
      rw [Fintype.sum_option]
      simp only [hS, hT, hSn, hTn, sub_zero]
      have hdiff : |(a : ℝ) - (b : ℝ)| = (b - a : ℕ) := by
        rw [abs_of_nonpos (by exact sub_nonpos.mpr (by exact_mod_cast hab)),
          Nat.cast_sub hab]
        ring
      rw [hdiff, abs_of_nonneg (Nat.cast_nonneg _)]
      ring
    calc
      σpm.cost cost ≤ assignmentCost costP σ := hcost_le
      _ ≤ (b : ℝ) * base + (1 / 2 : ℝ) * ∑ k, weight k *
          ∑ o : Option (C k),
            |partitionCount (cellP k ∘ xs) o - partitionCount (cellP k ∘ ys) o| := hσ'
      _ = (max a b : ℝ) * base + (1 / 2 : ℝ) * ∑ k, weight k *
          (∑ c, |partitionCount (cell k ∘ x) c - partitionCount (cell k ∘ y) c| +
            |(a : ℝ) - (b : ℝ)|) := by
        rw [max_eq_right (by exact_mod_cast hab)]
        congr 2
        apply Finset.sum_congr rfl
        intro k _
        rw [hcount k]
  · -- Pad the target cloud with dummy points.
    let xs : Fin a → X ⊕ Unit := fun i => Sum.inl (x i)
    let ys : Fin a → X ⊕ Unit := fun j =>
      if h : (j : ℕ) < b then Sum.inl (y ⟨j, h⟩) else Sum.inr ⟨⟩
    let cellP : (k : Fin K) → X ⊕ Unit → Option (C k) := fun k z =>
      match z with
      | Sum.inl w => some (cell k w)
      | Sum.inr _ => none
    let costP : Fin a → Fin a → ℝ := fun i j =>
      if h : (j : ℕ) < b then cost i ⟨j, h⟩ else 0
    have hnestP : ∀ (k l : Fin K), k ≤ l → ∀ u v : X ⊕ Unit,
        cellP l u = cellP l v → cellP k u = cellP k v := by
      intro k l hkl u v huv
      cases u with
      | inl u =>
          cases v with
          | inl v =>
              simp only [cellP]
              exact congrArg some (hnested k l hkl u v
                (by simpa only [cellP, Option.some.injEq] using huv))
          | inr v => simp [cellP] at huv
      | inr u =>
          cases v with
          | inl v => simp [cellP] at huv
          | inr v => simp [cellP]
    have hcostP : ∀ i j : Fin a, costP i j ≤ base + ∑ k, weight k *
        partitionDistance (cellP k (xs i)) (cellP k (ys j)) := by
      intro i j
      by_cases hj : (j : ℕ) < b
      · have hpd : ∀ k, partitionDistance (cellP k (xs i)) (cellP k (ys j)) =
            partitionDistance (cell k (x i)) (cell k (y ⟨j, hj⟩)) := by
          intro k
          simp only [cellP, xs, ys, dif_pos hj]
          simp only [partitionDistance, Option.some.injEq]
        simp only [costP, dif_pos hj]
        simpa only [hpd] using hcost i ⟨j, hj⟩
      · have hsum : 0 ≤ ∑ k, weight k *
            partitionDistance (cellP k (xs i)) (cellP k (ys j)) :=
          Finset.sum_nonneg fun k _ ↦
            mul_nonneg (hw k) (partitionDistance_bounds _ _).1
        simp only [costP, dif_neg hj]
        linarith
    obtain ⟨σ, hσ⟩ := exists_hierarchical_assignment_cost_bound
      (cell := cellP) hnestP xs ys costP base weight hcostP
    have hσ' : assignmentCost costP σ ≤ (a : ℝ) * base + (1 / 2 : ℝ) *
        ∑ k, weight k * ∑ o : Option (C k),
          |partitionCount (cellP k ∘ xs) o - partitionCount (cellP k ∘ ys) o| := by
      simpa only [Fintype.card_fin] using hσ
    -- The matching is indexed by the real target columns.
    let emb : Fin b → Fin a := fun j => ⟨j, lt_of_lt_of_le j.isLt hba⟩
    have hemb : Function.Injective emb := fun i j h =>
      Fin.ext (by simpa [emb] using congrArg Fin.val h)
    let e : Fin b → Fin a × Fin b := fun j => (σ.symm (emb j), j)
    have he : Function.Injective e := fun i j h => congrArg Prod.snd h
    let σpm : PartialMatching a b :=
      { edges := Finset.univ.image e
        row_inj := by
          intro p hp q hq hrow
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
          have hval : (σ.symm (emb i)).val = (σ.symm (emb j)).val := by
            simpa only using congrArg Fin.val hrow
          have hσeq : σ.symm (emb i) = σ.symm (emb j) := Fin.ext hval
          have hemb_eq : emb i = emb j := σ.symm.injective hσeq
          have : (⟨i, i.isLt⟩ : Fin b) = ⟨j, j.isLt⟩ := hemb hemb_eq
          exact congrArg e this
        col_inj := by
          intro p hp q hq hcol
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
          exact congrArg e hcol }
    have hcard : σpm.card = min a b := by
      simp only [PartialMatching.card, σpm]
      rw [Finset.card_image_of_injective _ he]
      simp [min_eq_right hba]
    refine ⟨σpm, hcard, ?_⟩
    have hcost_le : σpm.cost cost ≤ assignmentCost costP σ := by
      have hsub : Finset.univ.image emb ⊆ (Finset.univ : Finset (Fin a)) := by
        intro z _; exact Finset.mem_univ z
      have hnonneg : ∀ z ∈ (Finset.univ : Finset (Fin a)), z ∉ Finset.univ.image emb →
          0 ≤ costP (σ.symm z) z := by
        intro z _ hz
        have hzb : ¬ (z : ℕ) < b := by
          intro hlt
          exact hz (Finset.mem_image.mpr
            ⟨⟨z, hlt⟩, Finset.mem_univ _, by simp [emb, Fin.ext_iff]⟩)
        simp only [costP, dif_neg hzb]
        exact le_refl 0
      have hcost_pm : σpm.cost cost = ∑ j : Fin b, cost (σ.symm (emb j)) j := by
        simp only [PartialMatching.cost, σpm, e]
        rw [Finset.sum_image]
        intro i _ j _ hij
        exact congrArg Prod.snd hij
      have hreal : (∑ j : Fin b, cost (σ.symm (emb j)) j) =
          ∑ z ∈ Finset.univ.image emb, costP (σ.symm z) z := by
        rw [Finset.sum_image]
        · apply Finset.sum_congr rfl
          intro j _
          simp only [emb, costP, dif_pos j.isLt]
        · intro i _ j _ hij
          exact hemb hij
      have hperm : (∑ z : Fin a, costP z (σ z)) =
          ∑ z : Fin a, costP (σ.symm z) z := by
        refine Fintype.sum_equiv σ (fun z => costP z (σ z))
          (fun z => costP (σ.symm z) z) ?_
        intro z
        simp
      calc
        σpm.cost cost = ∑ j : Fin b, cost (σ.symm (emb j)) j := hcost_pm
        _ = ∑ z ∈ Finset.univ.image emb, costP (σ.symm z) z := hreal
        _ ≤ ∑ z : Fin a, costP (σ.symm z) z :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
        _ = ∑ z : Fin a, costP z (σ z) := hperm.symm
    have hcount : ∀ k : Fin K,
        (∑ o : Option (C k),
          |partitionCount (cellP k ∘ xs) o - partitionCount (cellP k ∘ ys) o|) =
        (∑ c, |partitionCount (cell k ∘ x) c - partitionCount (cell k ∘ y) c|) +
          |(a : ℝ) - (b : ℝ)| := by
      intro k
      have hS (c : C k) : partitionCount (cellP k ∘ xs) (some c) =
          partitionCount (cell k ∘ x) c := by
        simp only [partitionCount, partitionIndicator, Function.comp_apply, cellP, xs,
          Option.some.injEq]
      have hT (c : C k) : partitionCount (cellP k ∘ ys) (some c) =
          partitionCount (cell k ∘ y) c := by
        rw [show (cellP k ∘ ys) =
            (fun i : Fin a => if h : (i : ℕ) < b then
              some (cell k (y ⟨i, h⟩)) else none) from by
          funext i
          simp only [Function.comp_apply, cellP, ys]
          split_ifs <;> rfl]
        simpa only [Function.comp_def] using partitionCount_option_some cell y hba k c
      have hSn : partitionCount (cellP k ∘ xs) none = 0 := by
        simp only [partitionCount, partitionIndicator, Function.comp_apply, cellP, xs]
        simp
      have hTn : partitionCount (cellP k ∘ ys) none = ((a - b : ℕ) : ℝ) := by
        apply partitionCount_none_of_padding hba
        intro i
        simp only [Function.comp_apply, cellP, ys]
        by_cases hlt : (i : ℕ) < b
        · simp [hlt]
        · simp [hlt]
      rw [Fintype.sum_option]
      simp only [hS, hT, hSn, hTn, zero_sub, abs_neg, add_comm]
      have hdiff : |(a : ℝ) - (b : ℝ)| = (a - b : ℕ) := by
        rw [abs_of_nonneg (by exact sub_nonneg.mpr (by exact_mod_cast hba)),
          Nat.cast_sub hba]
      rw [hdiff, abs_of_nonneg (Nat.cast_nonneg _)]
    calc
      σpm.cost cost ≤ assignmentCost costP σ := hcost_le
      _ ≤ (a : ℝ) * base + (1 / 2 : ℝ) * ∑ k, weight k *
          ∑ o : Option (C k),
            |partitionCount (cellP k ∘ xs) o - partitionCount (cellP k ∘ ys) o| := hσ'
      _ = (max a b : ℝ) * base + (1 / 2 : ℝ) * ∑ k, weight k *
          (∑ c, |partitionCount (cell k ∘ x) c - partitionCount (cell k ∘ y) c| +
            |(a : ℝ) - (b : ℝ)|) := by
        rw [max_eq_left (by exact_mod_cast hba)]
        congr 2
        apply Finset.sum_congr rfl
        intro k _
        rw [hcount k]


/-- The optimal maximum-cardinality value obeys the same multiscale histogram
bound, with no explicit matching in the conclusion. -/
theorem maxCardValue_le_hierarchical_counts
    {X : Type*} {K a b : ℕ} {C : Fin K → Type*} [∀ k, Fintype (C k)]
    (cell : (k : Fin K) → X → C k)
    (hnested : ∀ (k l : Fin K), k ≤ l → ∀ x y : X,
      cell l x = cell l y → cell k x = cell k y)
    (x : Fin a → X) (y : Fin b → X)
    (cost : Fin a → Fin b → ℝ)
    (base : ℝ) (hb : 0 ≤ base) (weight : Fin K → ℝ) (hw : ∀ k, 0 ≤ weight k)
    (hcost : ∀ i j, cost i j ≤
      base + ∑ k, weight k * partitionDistance (cell k (x i)) (cell k (y j)))
    (hnonneg : ∀ i j, 0 ≤ cost i j) :
    PartialMatching.maxCardValue cost ≤ (max a b : ℝ) * base +
      (1 / 2 : ℝ) * ∑ k, weight k *
        (∑ c, |partitionCount (cell k ∘ x) c - partitionCount (cell k ∘ y) c| +
          |(a : ℝ) - (b : ℝ)|) := by
  obtain ⟨σ, hcard, hbound⟩ :=
    exists_partialMatching_hierarchy_cost_bound cell hnested x y cost base hb
      weight hw hcost
  exact (PartialMatching.maxCardValue_le cost hcard hnonneg).trans hbound

end OTSelector.Reconstruction
