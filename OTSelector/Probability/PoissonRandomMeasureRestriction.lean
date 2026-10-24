import LeanLevy.RandomMeasure.PoissonRandomMeasure
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.Independence.Basic
import OTSelector.Probability.PoissonRandomMeasureLaw

/-!
Conditions: Actual Poisson point families with sigma-finite intensity, measurable restriction sets, and disjointness for the restriction-independence conclusion.

Objects: Measurable restriction of actual random measures, the whole restriction law at restricted intensity, and independence of two disjoint restrictions.

Proof detail: Refine finite count-box tests into disjoint Boolean atoms intersected with the restriction sets. The true product count laws give equality/factorization on generators, then pi-system uniqueness extends to the full random-measure laws.

References: Günter Last and Mathew Penrose: Section 5.1, Theorem 5.2 (restriction theorem), p. 39; Günter Last and Mathew Penrose: Section 2.3, Proposition 2.10, pp. 14–15; Section 3.1, Proposition 3.2, p. 20.
Relation: The complete actual inventory proves restriction laws and disjoint-restriction independence. The old module prose additionally mentioned superposition, but this source file has no superposition/add-law declaration and that claim is not carried into this catalog.
-/

/-
Copyright (c) 2026 OTSelector Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OTSelector Contributors
-/

/-!
# Restrictions and superpositions of Poisson random measures

This file continues the distributional study of Poisson random measures begun in
`OTSelector/Probability/PoissonRandomMeasureLaw.lean`.  It shows that:

* restricting a Poisson random measure of intensity `m` to a measurable set `A` gives, in law, a
  Poisson random measure of intensity `m.restrict A`;
* the restrictions to two disjoint measurable sets are independent;
* the sum of two independent Poisson random measures of intensities `m₁` and `m₂` has, in law, the
  law of a Poisson random measure of intensity `m₁ + m₂`.

## Main results

* `poissonRandomMeasure_restrict_law` — the restriction law.
* `poissonRandomMeasure_restrict_indep` — independence of restrictions to disjoint sets.
* `poissonRandomMeasure_add_law` — superposition of independent Poisson random measures.

All three are proved by comparing count-box probabilities, refining the finite family defining a
count box into its Boolean atoms and using `poissonRandomMeasure_count_law` on the atoms.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

set_option linter.style.haveILetI false

namespace OTSelector.Probability

/-! ### Boolean atoms of a finite family

The same atom construction as in `PoissonRandomMeasureLaw`, reproduced locally because those
lemmas are private to their module.  The atom of a pattern `S : Finset ι` is the set of points whose
membership pattern in the family is exactly `S`; the empty pattern is replaced by `∅` so that every
atom has finite intensity mass. -/

/-- The atom of a membership pattern `S`. -/
private def countAtom {E : Type} {ι : Type} (A : ι → Set E) (S : Finset ι) : Set E :=
  {x : E | ∀ i, x ∈ A i ↔ i ∈ S}

private theorem mem_countAtom {E : Type} {ι : Type} {A : ι → Set E} {S : Finset ι} {x : E} :
    x ∈ countAtom A S ↔ ∀ i, x ∈ A i ↔ i ∈ S :=
  Iff.rfl

private theorem measurableSet_countAtom {E : Type} [MeasurableSpace E] {ι : Type} [Fintype ι]
    {A : ι → Set E} (hA : ∀ i, MeasurableSet (A i)) (S : Finset ι) :
    MeasurableSet (countAtom A S) := by
  classical
  have hEq : countAtom A S = ⋂ i, (if i ∈ S then A i else (A i)ᶜ) := by
    ext x
    rw [Set.mem_iInter]
    constructor
    · intro h i
      by_cases hi : i ∈ S
      · simpa [hi] using (h i).mpr hi
      · have hx : x ∉ A i := fun hx => hi ((h i).mp hx)
        simpa [hi] using hx
    · intro h i
      constructor
      · intro hx
        by_contra hi
        have hx' : x ∈ (A i)ᶜ := by simpa [hi] using h i
        exact hx' hx
      · intro hi
        simpa [hi] using h i
  rw [hEq,
    show (⋂ i, (if i ∈ S then A i else (A i)ᶜ))
        = ⋂ i ∈ (Finset.univ : Finset ι), (if i ∈ S then A i else (A i)ᶜ) from by
      ext x; simp]
  exact Finset.measurableSet_biInter _ fun i _ => by
    by_cases hi : i ∈ S
    · simpa [hi] using hA i
    · simpa [hi] using (hA i).compl

private theorem pairwise_disjoint_countAtom {E : Type} {ι : Type} (A : ι → Set E) :
    Pairwise (Function.onFun Disjoint (countAtom A)) := by
  intro S T hST
  change Disjoint (countAtom A S) (countAtom A T)
  rw [Set.disjoint_left]
  intro x hxS hxT
  exact hST (Finset.ext fun i =>
    (mem_countAtom.mp hxS i).symm.trans (mem_countAtom.mp hxT i))

private theorem eq_iUnion_countAtom {E : Type} {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : ι → Set E) (i : ι) :
    A i = ⋃ S ∈ (Finset.univ.filter fun S : Finset ι => i ∈ S), countAtom A S := by
  classical
  ext x
  constructor
  · intro hx
    refine Set.mem_iUnion₂.mpr
      ⟨Finset.univ.filter (fun j : ι => x ∈ A j), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, by simpa using hx⟩
    · refine mem_countAtom.mpr fun j => ?_
      rw [Finset.mem_filter]
      simp
  · intro hx
    obtain ⟨S, hS, hxS⟩ := Set.mem_iUnion₂.mp hx
    have hiS : i ∈ S := (Finset.mem_filter.mp hS).2
    exact (mem_countAtom.mp hxS i).mpr hiS

private theorem measure_eq_sum_countAtom {E : Type} [MeasurableSpace E] {ι : Type} [Fintype ι]
    [DecidableEq ι] {A : ι → Set E} (hA : ∀ i, MeasurableSet (A i)) (ν : Measure E) (i : ι) :
    ν (A i) = ∑ S ∈ (Finset.univ.filter fun S : Finset ι => i ∈ S), ν (countAtom A S) := by
  classical
  rw [eq_iUnion_countAtom A i]
  exact measure_biUnion_finset
    (fun a _ b _ hab => pairwise_disjoint_countAtom A hab)
    (fun b _ => measurableSet_countAtom hA b)

private noncomputable def countAtom' {E : Type} {ι : Type} (A : ι → Set E) (S : Finset ι) : Set E :=
  by
  classical
  exact if S.Nonempty then countAtom A S else ∅

private theorem countAtom'_eq_countAtom {E : Type} {ι : Type} (A : ι → Set E) {S : Finset ι}
    (hS : S.Nonempty) : countAtom' A S = countAtom A S := by
  classical
  unfold countAtom'
  rw [ite_eq_left hS]

private theorem countAtom'_eq_empty {E : Type} {ι : Type} (A : ι → Set E) {S : Finset ι}
    (hS : ¬ S.Nonempty) : countAtom' A S = ∅ := by
  classical
  unfold countAtom'
  rw [ite_eq_right hS]

private theorem measurableSet_countAtom' {E : Type} [MeasurableSpace E] {ι : Type} [Fintype ι]
    {A : ι → Set E} (hA : ∀ i, MeasurableSet (A i)) (S : Finset ι) :
    MeasurableSet (countAtom' A S) := by
  classical
  by_cases hS : S.Nonempty
  · rw [countAtom'_eq_countAtom A hS]; exact measurableSet_countAtom hA S
  · rw [countAtom'_eq_empty A hS]; exact MeasurableSet.empty

private theorem pairwise_disjoint_countAtom' {E : Type} {ι : Type} (A : ι → Set E) :
    Pairwise (Function.onFun Disjoint (countAtom' A)) := by
  intro S T hST
  change Disjoint (countAtom' A S) (countAtom' A T)
  classical
  by_cases hS : S.Nonempty
  · by_cases hT : T.Nonempty
    · rw [countAtom'_eq_countAtom A hS, countAtom'_eq_countAtom A hT]
      exact pairwise_disjoint_countAtom A hST
    · obtain rfl : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
      rw [countAtom'_eq_countAtom A hS, countAtom'_eq_empty A (by simp)]
      simp
  · obtain rfl : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [countAtom'_eq_empty A (by simp)]
    simp

private theorem measure_countAtom'_lt_top {E : Type} [MeasurableSpace E] {ι : Type}
    {A : ι → Set E} {m : Measure E} (hfin : ∀ i, m (A i) < ⊤) (S : Finset ι) :
    m (countAtom' A S) < ⊤ := by
  classical
  by_cases hS : S.Nonempty
  · rw [countAtom'_eq_countAtom A hS]
    obtain ⟨i, hiS⟩ := hS
    refine lt_of_le_of_lt (measure_mono ?_) (hfin i)
    intro x hx
    exact (mem_countAtom.mp hx i).mpr hiS
  · rw [countAtom'_eq_empty A hS]; simp

private theorem measure_eq_sum_countAtom' {E : Type} [MeasurableSpace E] {ι : Type} [Fintype ι]
    [DecidableEq ι] {A : ι → Set E} (hA : ∀ i, MeasurableSet (A i)) (ν : Measure E) (i : ι) :
    ν (A i) = ∑ S ∈ (Finset.univ.filter fun S : Finset ι => i ∈ S), ν (countAtom' A S) := by
  classical
  rw [measure_eq_sum_countAtom hA ν i]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hiS : i ∈ S := (Finset.mem_filter.mp hS).2
  rw [countAtom'_eq_countAtom A ⟨i, hiS⟩]

/-- Intersecting a family with a fixed set commutes with the empty-pattern-adjusted atoms: the atoms
of `fun i => B i ∩ A` are the atoms of `B` intersected with `A`.  The adjustment of the empty pattern
is essential here, since the empty atom of the restricted family is `∅` rather than the complement
of the union inside `A`. -/
private theorem countAtom'_inter {E : Type} {ι : Type} {B : ι → Set E} {A : Set E}
    (S : Finset ι) :
    countAtom' (fun i => B i ∩ A) S = countAtom' B S ∩ A := by
  classical
  by_cases hS : S.Nonempty
  · rw [countAtom'_eq_countAtom _ hS, countAtom'_eq_countAtom _ hS]
    ext x
    rw [Set.mem_inter_iff, mem_countAtom, mem_countAtom]
    constructor
    · intro h
      obtain ⟨i₀, hi₀⟩ := hS
      have hxA : x ∈ A := ((h i₀).mpr hi₀).2
      refine ⟨fun i => ?_, hxA⟩
      exact ⟨fun hx => (h i).mp ⟨hx, hxA⟩, fun hi => ((h i).mpr hi).1⟩
    · rintro ⟨h, hxA⟩ i
      exact ⟨fun hx => (h i).mp hx.1, fun hi => ⟨(h i).mpr hi, hxA⟩⟩
  · rw [countAtom'_eq_empty _ hS, countAtom'_eq_empty _ hS]
    exact (Set.empty_inter A).symm

/-! ### Measurability of the restricted random measure -/

/-- Restriction of a measure is a measurable operation for the Giry σ-algebra: on a measurable set
`s` the restricted measure evaluates to `ν (s ∩ A)`, a measurable evaluation of `ν`. -/
theorem measurable_measure_restrict {E : Type} [MeasurableSpace E] {A : Set E}
    (hA : MeasurableSet A) :
    Measurable fun ν : Measure E => ν.restrict A := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hcoe : (fun ν : Measure E => ν.restrict A s) = fun ν => ν (s ∩ A) := by
    funext ν
    exact Measure.restrict_apply hs
  rw [hcoe]
  exact Measure.measurable_coe (hs.inter hA)

/-! ### The restriction law

The proof refines a finite family `B` defining a count box into its atoms `Atom S = countAtom' B S`.
On the canonical side the atom counts are `N' (Atom S)`, with rates `(m.restrict A) (Atom S)`.  On
the restricted side the same sets appear intersected with `A`, with rates `m (Atom S ∩ A)`, and the
two rates agree because `Atom S ⊆ B i` has `(m.restrict A) (Atom S) = m (Atom S ∩ A)`.  Hence the
atom-count vectors have the same product law and the count-box probabilities agree. -/

/-- Count-box probabilities agree between a Poisson random measure restricted to `A` and a Poisson
random measure with intensity `m.restrict A`. -/
private theorem restrict_countBox_eq {Ω Ω' E : Type} [MeasurableSpace E]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {K' : ℕ → Ω' → ℕ} {X' : ℕ → ℕ → Ω' → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E] {μ : Measure Ω} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {A : Set E} (hA : MeasurableSet A)
    (hd : IsPoissonPointFamily K X m μ) (hd' : IsPoissonPointFamily K' X' (m.restrict A) μ')
    {ι : Type} [Fintype ι] [DecidableEq ι] {B : ι → Set E}
    (hB : ∀ i, MeasurableSet (B i)) (hfin : ∀ i, (m.restrict A) (B i) < ⊤)
    {C : ι → Set ℝ≥0∞} (hC : ∀ i, MeasurableSet (C i)) :
    μ' (poissonRandomMeasure K' X' ⁻¹' {ν : Measure E | ∀ i, ν (B i) ∈ C i}) =
      μ ((fun ω => (poissonRandomMeasure K X ω).restrict A) ⁻¹'
        {ν : Measure E | ∀ i, ν (B i) ∈ C i}) := by
  classical
  set Atom : Finset ι → Set E := fun S => countAtom' B S with hAtom_def
  set V' : Ω' → (Finset ι → ℝ≥0∞) := fun ω S => poissonRandomMeasure K' X' ω (Atom S)
    with hV'_def
  set V : Ω → (Finset ι → ℝ≥0∞) := fun ω S => poissonRandomMeasure K X ω (Atom S ∩ A)
    with hV_def
  set ψ : (Finset ι → ℝ≥0∞) → (ι → ℝ≥0∞) :=
    fun v i => ∑ S ∈ (Finset.univ.filter fun S : Finset ι => i ∈ S), v S with hψ_def
  set T : Set (ι → ℝ≥0∞) := {v | ∀ i, v i ∈ C i} with hT_def
  -- Atoms are measurable, finite-mass and pairwise disjoint.
  have hAtom_meas : ∀ S, MeasurableSet (Atom S) := fun S => measurableSet_countAtom' hB S
  have hAtomA_meas : ∀ S, MeasurableSet (Atom S ∩ A) := fun S => (hAtom_meas S).inter hA
  have hAtom_fin : ∀ S, (m.restrict A) (Atom S) < ⊤ := by
    intro S
    by_cases hS : S.Nonempty
    · have hSne : S.Nonempty := hS
      obtain ⟨i, hiS⟩ := hS
      refine lt_of_le_of_lt (measure_mono ?_) (hfin i)
      intro x hx
      have hx' : x ∈ countAtom' B S := by simpa [hAtom_def] using hx
      rw [countAtom'_eq_countAtom B hSne] at hx'
      exact (mem_countAtom.mp hx' i).mpr hiS
    · rw [hAtom_def]
      change (m.restrict A) (countAtom' B S) < ⊤
      rw [countAtom'_eq_empty B hS]
      simp
  have hAtomA_fin : ∀ S, m (Atom S ∩ A) < ⊤ := by
    intro S
    rw [← Measure.restrict_apply (hAtom_meas S)]
    exact hAtom_fin S
  have hAtom_disj : Pairwise (Function.onFun Disjoint Atom) := pairwise_disjoint_countAtom' B
  have hAtomA_disj : Pairwise (Function.onFun Disjoint (fun S => Atom S ∩ A)) := by
    intro S T hST
    change Disjoint (Atom S ∩ A) (Atom T ∩ A)
    exact (hAtom_disj hST).mono Set.inter_subset_left Set.inter_subset_left
  -- The two atom-count vectors have the same law.
  have hlaw' : μ'.map V'
      = Measure.pi (fun S => (poissonMeasure (((m.restrict A) (Atom S)).toNNReal)).map
          (Nat.cast : ℕ → ℝ≥0∞)) :=
    poissonRandomMeasure_count_law hd' Atom hAtom_meas hAtom_fin hAtom_disj
  have hlaw : μ.map V
      = Measure.pi (fun S => (poissonMeasure ((m (Atom S ∩ A)).toNNReal)).map
          (Nat.cast : ℕ → ℝ≥0∞)) :=
    poissonRandomMeasure_count_law hd (fun S => Atom S ∩ A) hAtomA_meas hAtomA_fin hAtomA_disj
  have hrate : (fun S => (poissonMeasure (((m.restrict A) (Atom S)).toNNReal)).map
        (Nat.cast : ℕ → ℝ≥0∞))
      = fun S => (poissonMeasure ((m (Atom S ∩ A)).toNNReal)).map (Nat.cast : ℕ → ℝ≥0∞) := by
    funext S
    rw [Measure.restrict_apply (hAtom_meas S)]
  have hVlaw : μ'.map V' = μ.map V := by rw [hlaw', hlaw, hrate]
  -- The deterministic map from atom counts to the counts on `B i`.
  have hψ : Measurable ψ := by
    rw [hψ_def]
    exact measurable_pi_lambda _ fun i =>
      Finset.measurable_sum _ fun S _ => measurable_pi_apply S
  have hT : MeasurableSet T := by
    rw [hT_def,
      show {v : ι → ℝ≥0∞ | ∀ i, v i ∈ C i}
          = ⋂ i ∈ (Finset.univ : Finset ι), {v : ι → ℝ≥0∞ | v i ∈ C i} from by
        ext v; simp]
    exact Finset.measurableSet_biInter _ fun i _ => measurable_pi_apply i (hC i)
  have hU : MeasurableSet (ψ ⁻¹' T) := hψ hT
  have hV_meas : Measurable V := by
    rw [hV_def]
    exact measurable_pi_lambda _ fun S =>
      measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point
        (hAtomA_meas S)
  have hV'_meas : Measurable V' := by
    rw [hV'_def]
    exact measurable_pi_lambda _ fun S =>
      measurable_poissonRandomMeasure_apply hd'.measurable_count hd'.measurable_point
        (hAtom_meas S)
  -- The atom of the restricted family is the atom of `B` intersected with `A`.
  have hinter : ∀ S, Atom S ∩ A = countAtom' (fun i => B i ∩ A) S := by
    intro S
    rw [hAtom_def]
    exact (countAtom'_inter S).symm
  -- The two events are the preimages of `T` under `ψ`.
  have hleft_event : poissonRandomMeasure K' X' ⁻¹' {ν : Measure E | ∀ i, ν (B i) ∈ C i}
      = V' ⁻¹' (ψ ⁻¹' T) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hV'_def, hψ_def, hT_def, hAtom_def]
    constructor
    · intro h i
      rw [← measure_eq_sum_countAtom' hB (poissonRandomMeasure K' X' ω) i]
      exact h i
    · intro h i
      rw [measure_eq_sum_countAtom' hB (poissonRandomMeasure K' X' ω) i]
      exact h i
  have hright_event : (fun ω => (poissonRandomMeasure K X ω).restrict A) ⁻¹'
        {ν : Measure E | ∀ i, ν (B i) ∈ C i} = V ⁻¹' (ψ ⁻¹' T) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hV_def, hψ_def, hT_def]
    constructor
    · intro h i
      have hi := h i
      rw [Measure.restrict_apply (hB i)] at hi
      simp only [hinter]
      rw [← measure_eq_sum_countAtom' (A := fun i => B i ∩ A)
        (fun i => (hB i).inter hA) (poissonRandomMeasure K X ω) i]
      exact hi
    · intro h i
      rw [Measure.restrict_apply (hB i)]
      have hi := h i
      simp only [hinter] at hi
      rw [measure_eq_sum_countAtom' (A := fun i => B i ∩ A)
        (fun i => (hB i).inter hA) (poissonRandomMeasure K X ω) i]
      exact hi
  calc μ' (poissonRandomMeasure K' X' ⁻¹' {ν : Measure E | ∀ i, ν (B i) ∈ C i})
      = μ' (V' ⁻¹' (ψ ⁻¹' T)) := by rw [hleft_event]
    _ = (μ'.map V') (ψ ⁻¹' T) := (Measure.map_apply hV'_meas hU).symm
    _ = (μ.map V) (ψ ⁻¹' T) := by rw [hVlaw]
    _ = μ (V ⁻¹' (ψ ⁻¹' T)) := Measure.map_apply hV_meas hU
    _ = μ ((fun ω => (poissonRandomMeasure K X ω).restrict A) ⁻¹'
          {ν : Measure E | ∀ i, ν (B i) ∈ C i}) := by rw [hright_event]

/-- **Restriction law.** The restriction of a Poisson random measure with intensity `m` to a
measurable set `A` has the law of a Poisson random measure with intensity `m.restrict A`. -/
theorem poissonRandomMeasure_restrict_law {Ω Ω' E : Type} [MeasurableSpace E]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {K' : ℕ → Ω' → ℕ}
    {X' : ℕ → ℕ → Ω' → E} {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (A : Set E) (hA : MeasurableSet A)
    (hd : IsPoissonPointFamily K X m μ)
    (hd' : IsPoissonPointFamily K' X' (m.restrict A) μ') :
    μ'.map (poissonRandomMeasure K' X') =
      μ.map (fun ω => (poissonRandomMeasure K X ω).restrict A) := by
  have hN : Measurable fun ω => (poissonRandomMeasure K X ω).restrict A :=
    (measurable_measure_restrict hA).comp (measurable_poissonRandomMeasure hd)
  have hN' : Measurable (poissonRandomMeasure K' X') := measurable_poissonRandomMeasure hd'
  refine measure_law_eq_of_countBox_eq (m := m.restrict A) (μ := μ') (μ' := μ)
    (N := poissonRandomMeasure K' X')
    (N' := fun ω => (poissonRandomMeasure K X ω).restrict A) hN' hN ?_
  intro s hs
  obtain ⟨ι, hι, B, C, hB, hfin, hC, rfl⟩ := hs
  haveI := hι
  classical
  exact restrict_countBox_eq hA hd hd' hB hfin hC

/-! ### Independence of restrictions to disjoint sets

The count-box factorization is proved by refining the two finite families into atoms and using the
mutual independence of the counts on a pairwise disjoint family.  The atom families on `A` and on
`B` are disjoint from each other because `A` and `B` are disjoint, so all atom counts are jointly
independent; the two count-box events are functions of the two separate groups of atoms, hence
independent. -/

/-- The joint probability of two count boxes under the restrictions to disjoint sets `A` and `B`
factorizes. -/
private theorem restrict_box_factor {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    {A B : Set E} (hA : MeasurableSet A) (hB : MeasurableSet B) (hdisj : Disjoint A B)
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {a : ι → Set E} (ha : ∀ i, MeasurableSet (a i)) (hafin : ∀ i, (m.restrict A) (a i) < ⊤)
    {C : ι → Set ℝ≥0∞} (hC : ∀ i, MeasurableSet (C i))
    {b : κ → Set E} (hb : ∀ j, MeasurableSet (b j)) (hbfin : ∀ j, (m.restrict B) (b j) < ⊤)
    {D : κ → Set ℝ≥0∞} (hD : ∀ j, MeasurableSet (D j)) :
    μ ((fun ω => (poissonRandomMeasure K X ω).restrict A) ⁻¹'
          {ν : Measure E | ∀ i, ν (a i) ∈ C i} ∩
        (fun ω => (poissonRandomMeasure K X ω).restrict B) ⁻¹'
          {ν : Measure E | ∀ j, ν (b j) ∈ D j}) =
      μ ((fun ω => (poissonRandomMeasure K X ω).restrict A) ⁻¹'
          {ν : Measure E | ∀ i, ν (a i) ∈ C i}) *
        μ ((fun ω => (poissonRandomMeasure K X ω).restrict B) ⁻¹'
          {ν : Measure E | ∀ j, ν (b j) ∈ D j}) := by
  classical
  set aAt : Finset ι → Set E := fun S => countAtom' a S ∩ A with haAt_def
  set bAt : Finset κ → Set E := fun S => countAtom' b S ∩ B with hbAt_def
  set c : (Finset ι) ⊕ (Finset κ) → Set E := Sum.elim aAt bAt with hc_def
  set Xa : Ω → (Finset ι → ℝ≥0∞) := fun ω S => poissonRandomMeasure K X ω (aAt S)
    with hXa_def
  set Xb : Ω → (Finset κ → ℝ≥0∞) := fun ω S => poissonRandomMeasure K X ω (bAt S)
    with hXb_def
  set ψa : (Finset ι → ℝ≥0∞) → (ι → ℝ≥0∞) :=
    fun v i => ∑ S ∈ (Finset.univ.filter fun S : Finset ι => i ∈ S), v S with hψa_def
  set ψb : (Finset κ → ℝ≥0∞) → (κ → ℝ≥0∞) :=
    fun v j => ∑ S ∈ (Finset.univ.filter fun S : Finset κ => j ∈ S), v S with hψb_def
  set Ta : Set (ι → ℝ≥0∞) := {v | ∀ i, v i ∈ C i} with hTa_def
  set Tb : Set (κ → ℝ≥0∞) := {v | ∀ j, v j ∈ D j} with hTb_def
  -- Measurability and finite mass of the atoms.
  have haAt_meas : ∀ S, MeasurableSet (aAt S) :=
    fun S => (measurableSet_countAtom' ha S).inter hA
  have hbAt_meas : ∀ S, MeasurableSet (bAt S) :=
    fun S => (measurableSet_countAtom' hb S).inter hB
  have haAt_fin : ∀ S, m (aAt S) < ⊤ := by
    intro S
    by_cases hS : S.Nonempty
    · have hSne : S.Nonempty := hS
      obtain ⟨i, hiS⟩ := hS
      have hle : m (aAt S) ≤ m (a i ∩ A) := by
        refine measure_mono ?_
        intro x hx
        have hx' : x ∈ countAtom' a S := hx.1
        rw [countAtom'_eq_countAtom a hSne] at hx'
        exact ⟨(mem_countAtom.mp hx' i).mpr hiS, hx.2⟩
      have hlt : m (a i ∩ A) < ⊤ := by
        rw [← Measure.restrict_apply (ha i)]
        exact hafin i
      exact lt_of_le_of_lt hle hlt
    · simp [haAt_def, countAtom'_eq_empty a hS]
  have hbAt_fin : ∀ S, m (bAt S) < ⊤ := by
    intro S
    by_cases hS : S.Nonempty
    · have hSne : S.Nonempty := hS
      obtain ⟨j, hjS⟩ := hS
      have hle : m (bAt S) ≤ m (b j ∩ B) := by
        refine measure_mono ?_
        intro x hx
        have hx' : x ∈ countAtom' b S := hx.1
        rw [countAtom'_eq_countAtom b hSne] at hx'
        exact ⟨(mem_countAtom.mp hx' j).mpr hjS, hx.2⟩
      have hlt : m (b j ∩ B) < ⊤ := by
        rw [← Measure.restrict_apply (hb j)]
        exact hbfin j
      exact lt_of_le_of_lt hle hlt
    · simp [hbAt_def, countAtom'_eq_empty b hS]
  -- The combined atom family is pairwise disjoint.
  have hc_meas : ∀ k, MeasurableSet (c k) := by
    rintro (S | S)
    · exact haAt_meas S
    · exact hbAt_meas S
  have hc_fin : ∀ k, m (c k) < ⊤ := by
    rintro (S | S)
    · exact haAt_fin S
    · exact hbAt_fin S
  have hc_disj : Pairwise (Function.onFun Disjoint c) := by
    intro x y hxy
    change Disjoint (c x) (c y)
    rw [Set.disjoint_left]
    intro z hzx hzy
    rcases x with S | S <;> rcases y with T | T
    · have hST : S ≠ T := fun h => hxy (by rw [h])
      exact (Set.disjoint_left.mp (pairwise_disjoint_countAtom' a hST)) hzx.1 hzy.1
    · exact (Set.disjoint_left.mp hdisj) hzx.2 hzy.2
    · exact (Set.disjoint_left.mp hdisj) hzy.2 hzx.2
    · have hST : S ≠ T := fun h => hxy (by rw [h])
      exact (Set.disjoint_left.mp (pairwise_disjoint_countAtom' b hST)) hzx.1 hzy.1
  -- Mutual independence of all atom counts.
  have hind : iIndepFun (fun k ω => poissonRandomMeasure K X ω (c k)) μ :=
    iIndepFun_poissonRandomMeasure_apply hd hc_meas hc_fin hc_disj
  set Sa : Finset ((Finset ι) ⊕ (Finset κ)) := Finset.univ.image Sum.inl with hSa_def
  set Sb : Finset ((Finset ι) ⊕ (Finset κ)) := Finset.univ.image Sum.inr with hSb_def
  have hdisj_ab : Disjoint Sa Sb := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [hSa_def] at hx
    rw [hSb_def] at hx'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx hx'
    obtain ⟨s, rfl⟩ := hx
    obtain ⟨t, ht⟩ := hx'
    simp at ht
  have hproc := hind.indepFun_finset Sa Sb hdisj_ab
    (fun k => measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point
      (hc_meas k))
  -- Independence of the two atom-count vectors.
  have hXaXb : IndepFun Xa Xb μ := by
    have hleft : Measurable
        (fun (v : Sa → ℝ≥0∞) (S : Finset ι) => v ⟨Sum.inl S, by simp [Sa]⟩) :=
      measurable_pi_lambda _ fun S => measurable_pi_apply _
    have hright : Measurable
        (fun (v : Sb → ℝ≥0∞) (S : Finset κ) => v ⟨Sum.inr S, by simp [Sb]⟩) :=
      measurable_pi_lambda _ fun S => measurable_pi_apply _
    have h := hproc.comp hleft hright
    simpa [Function.comp_def, Xa, Xb, c] using h
  -- The ψ-maps and target boxes are measurable.
  have hψa : Measurable ψa := by
    rw [hψa_def]
    exact measurable_pi_lambda _ fun i =>
      Finset.measurable_sum _ fun S _ => measurable_pi_apply S
  have hψb : Measurable ψb := by
    rw [hψb_def]
    exact measurable_pi_lambda _ fun j =>
      Finset.measurable_sum _ fun S _ => measurable_pi_apply S
  have hTa : MeasurableSet Ta := by
    rw [hTa_def,
      show {v : ι → ℝ≥0∞ | ∀ i, v i ∈ C i}
          = ⋂ i ∈ (Finset.univ : Finset ι), {v : ι → ℝ≥0∞ | v i ∈ C i} from by
        ext v; simp]
    exact Finset.measurableSet_biInter _ fun i _ => measurable_pi_apply i (hC i)
  have hTb : MeasurableSet Tb := by
    rw [hTb_def,
      show {v : κ → ℝ≥0∞ | ∀ j, v j ∈ D j}
          = ⋂ j ∈ (Finset.univ : Finset κ), {v : κ → ℝ≥0∞ | v j ∈ D j} from by
        ext v; simp]
    exact Finset.measurableSet_biInter _ fun j _ => measurable_pi_apply j (hD j)
  have hUa : MeasurableSet (ψa ⁻¹' Ta) := hψa hTa
  have hUb : MeasurableSet (ψb ⁻¹' Tb) := hψb hTb
  -- The atoms of the restricted families.
  have hinter_a : ∀ S, aAt S = countAtom' (fun i => a i ∩ A) S := by
    intro S
    rw [haAt_def]
    exact (countAtom'_inter (B := a) (A := A) S).symm
  have hinter_b : ∀ S, bAt S = countAtom' (fun j => b j ∩ B) S := by
    intro S
    rw [hbAt_def]
    exact (countAtom'_inter (B := b) (A := B) S).symm
  -- The two events are the preimages of `Ta`, `Tb` under `ψa`, `ψb`.
  have hEa : (fun ω => (poissonRandomMeasure K X ω).restrict A) ⁻¹'
        {ν : Measure E | ∀ i, ν (a i) ∈ C i} = Xa ⁻¹' (ψa ⁻¹' Ta) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hXa_def, hψa_def, hTa_def]
    constructor
    · intro h i
      have hi := h i
      rw [Measure.restrict_apply (ha i)] at hi
      simp only [hinter_a]
      rw [← measure_eq_sum_countAtom' (A := fun i => a i ∩ A)
        (fun i => (ha i).inter hA) (poissonRandomMeasure K X ω) i]
      exact hi
    · intro h i
      rw [Measure.restrict_apply (ha i)]
      have hi := h i
      simp only [hinter_a] at hi
      rw [measure_eq_sum_countAtom' (A := fun i => a i ∩ A)
        (fun i => (ha i).inter hA) (poissonRandomMeasure K X ω) i]
      exact hi
  have hEb : (fun ω => (poissonRandomMeasure K X ω).restrict B) ⁻¹'
        {ν : Measure E | ∀ j, ν (b j) ∈ D j} = Xb ⁻¹' (ψb ⁻¹' Tb) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hXb_def, hψb_def, hTb_def]
    constructor
    · intro h j
      have hj := h j
      rw [Measure.restrict_apply (hb j)] at hj
      simp only [hinter_b]
      rw [← measure_eq_sum_countAtom' (A := fun j => b j ∩ B)
        (fun j => (hb j).inter hB) (poissonRandomMeasure K X ω) j]
      exact hj
    · intro h j
      rw [Measure.restrict_apply (hb j)]
      have hj := h j
      simp only [hinter_b] at hj
      rw [measure_eq_sum_countAtom' (A := fun j => b j ∩ B)
        (fun j => (hb j).inter hB) (poissonRandomMeasure K X ω) j]
      exact hj
  have hfac := hXaXb.measure_inter_preimage_eq_mul (ψa ⁻¹' Ta) (ψb ⁻¹' Tb) hUa hUb
  rw [hEa, hEb]
  exact hfac

/-- **Independence of restrictions to disjoint measurable sets.** The restrictions of a Poisson
random measure to two disjoint measurable sets are independent random measures.

The proof first checks the factorization of `μ (f ⁻¹' s ∩ g ⁻¹' t)` for count boxes `s`, `t` using
`restrict_box_factor`.  For a fixed count box `t`, the two sides of the factorization, viewed as
measures in `s`, are finite measures on the Giry space agreeing on the π-system `CountBox` and having
the same total mass, so they agree for every measurable `s` by `Measure.ext_of_generate_finite`; a
second application in `t` extends the factorization to all measurable `s` and `t`, which is exactly
the independence criterion `indepFun_iff_measure_inter_preimage_eq_mul`. -/
theorem poissonRandomMeasure_restrict_indep {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    {A B : Set E} (hA : MeasurableSet A) (hB : MeasurableSet B) (hdisj : Disjoint A B) :
    IndepFun (fun ω => (poissonRandomMeasure K X ω).restrict A)
      (fun ω => (poissonRandomMeasure K X ω).restrict B) μ := by
  classical
  set f : Ω → Measure E := fun ω => (poissonRandomMeasure K X ω).restrict A with hf_def
  set g : Ω → Measure E := fun ω => (poissonRandomMeasure K X ω).restrict B with hg_def
  have hf : Measurable f := by
    rw [hf_def]
    exact (measurable_measure_restrict hA).comp (measurable_poissonRandomMeasure hd)
  have hg : Measurable g := by
    rw [hg_def]
    exact (measurable_measure_restrict hB).comp (measurable_poissonRandomMeasure hd)
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  -- Step 1: factorize against a fixed count box `t` in the second variable.
  have hstep1 : ∀ t ∈ CountBox E (m.restrict B), ∀ s, MeasurableSet s →
      μ (f ⁻¹' s ∩ g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t) := by
    intro t ht s hs
    haveI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
    have hmeasure_eq : (μ.restrict (g ⁻¹' t)).map f = (μ (g ⁻¹' t)) • (μ.map f) := by
      refine ext_of_generate_finite (CountBox E (m.restrict A))
        (giry_eq_generateFrom_countBox E (m.restrict A))
        (isPiSystem_countBox E (m.restrict A)) ?_ ?_
      · intro u hu
        obtain ⟨ι, hι, a, C, ha, hafin, hC, rfl⟩ := hu
        obtain ⟨κ, hκ, b, D, hb, hbfin, hD, rfl⟩ := ht
        haveI := hι
        haveI := hκ
        have hu' : {ν : Measure E | ∀ i, ν (a i) ∈ C i} ∈ CountBox E (m.restrict A) :=
          ⟨ι, hι, a, C, ha, hafin, hC, rfl⟩
        have ht' : {ν : Measure E | ∀ j, ν (b j) ∈ D j} ∈ CountBox E (m.restrict B) :=
          ⟨κ, hκ, b, D, hb, hbfin, hD, rfl⟩
        have hu_meas : MeasurableSet {ν : Measure E | ∀ i, ν (a i) ∈ C i} :=
          measurableSet_countBox hu'
        have hfac := restrict_box_factor hd hA hB hdisj ha hafin hC hb hbfin hD
        have hL : (μ.restrict (g ⁻¹' {ν : Measure E | ∀ j, ν (b j) ∈ D j})).map f
            {ν : Measure E | ∀ i, ν (a i) ∈ C i}
            = μ (f ⁻¹' {ν : Measure E | ∀ i, ν (a i) ∈ C i} ∩
                g ⁻¹' {ν : Measure E | ∀ j, ν (b j) ∈ D j}) := by
          rw [Measure.map_apply hf hu_meas, Measure.restrict_apply (hf hu_meas)]
        have hR : ((μ (g ⁻¹' {ν : Measure E | ∀ j, ν (b j) ∈ D j})) • (μ.map f))
            {ν : Measure E | ∀ i, ν (a i) ∈ C i}
            = μ (f ⁻¹' {ν : Measure E | ∀ i, ν (a i) ∈ C i}) *
              μ (g ⁻¹' {ν : Measure E | ∀ j, ν (b j) ∈ D j}) := by
          rw [Measure.smul_apply, Measure.map_apply hf hu_meas, smul_eq_mul]
          exact mul_comm _ _
        rw [hL, hR]
        exact hfac
      · have h1 : (Measure.map f (μ.restrict (g ⁻¹' t))) Set.univ = μ (g ⁻¹' t) := by
          rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ,
            Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        have h2 : ((μ (g ⁻¹' t)) • (Measure.map f μ)) Set.univ = μ (g ⁻¹' t) := by
          rw [Measure.smul_apply, Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ,
            measure_univ, smul_eq_mul, mul_one]
        rw [h1, h2]
    have hL : (μ.restrict (g ⁻¹' t)).map f s = μ (f ⁻¹' s ∩ g ⁻¹' t) := by
      rw [Measure.map_apply hf hs, Measure.restrict_apply (hf hs)]
    have hR : ((μ (g ⁻¹' t)) • (μ.map f)) s = μ (f ⁻¹' s) * μ (g ⁻¹' t) := by
      rw [Measure.smul_apply, Measure.map_apply hf hs, smul_eq_mul]
      exact mul_comm _ _
    rw [← hL, hmeasure_eq, hR]
  -- Step 2: extend the factorization to an arbitrary measurable `t`.
  have hstep2 : ∀ s, MeasurableSet s → ∀ t, MeasurableSet t →
      μ (f ⁻¹' s ∩ g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t) := by
    intro s hs t ht
    haveI : IsProbabilityMeasure (μ.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
    have hmeasure_eq : (μ.restrict (f ⁻¹' s)).map g = (μ (f ⁻¹' s)) • (μ.map g) := by
      refine ext_of_generate_finite (CountBox E (m.restrict B))
        (giry_eq_generateFrom_countBox E (m.restrict B))
        (isPiSystem_countBox E (m.restrict B)) ?_ ?_
      · intro u hu
        have hu_meas : MeasurableSet u := measurableSet_countBox hu
        have h := hstep1 u hu s hs
        have hL : (μ.restrict (f ⁻¹' s)).map g u = μ (g ⁻¹' u ∩ f ⁻¹' s) := by
          rw [Measure.map_apply hg hu_meas, Measure.restrict_apply (hg hu_meas)]
        have hR : ((μ (f ⁻¹' s)) • (μ.map g)) u = μ (f ⁻¹' s) * μ (g ⁻¹' u) := by
          rw [Measure.smul_apply, Measure.map_apply hg hu_meas, smul_eq_mul]
        rw [hL, hR, Set.inter_comm (g ⁻¹' u) (f ⁻¹' s)]
        exact h
      · have h1 : (Measure.map g (μ.restrict (f ⁻¹' s))) Set.univ = μ (f ⁻¹' s) := by
          rw [Measure.map_apply hg MeasurableSet.univ, Set.preimage_univ,
            Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        have h2 : ((μ (f ⁻¹' s)) • (Measure.map g μ)) Set.univ = μ (f ⁻¹' s) := by
          rw [Measure.smul_apply, Measure.map_apply hg MeasurableSet.univ, Set.preimage_univ,
            measure_univ, smul_eq_mul, mul_one]
        rw [h1, h2]
    have hL : (μ.restrict (f ⁻¹' s)).map g t = μ (g ⁻¹' t ∩ f ⁻¹' s) := by
      rw [Measure.map_apply hg ht, Measure.restrict_apply (hg ht)]
    have hR : ((μ (f ⁻¹' s)) • (μ.map g)) t = μ (f ⁻¹' s) * μ (g ⁻¹' t) := by
      rw [Measure.smul_apply, Measure.map_apply hg ht, smul_eq_mul]
    rw [Set.inter_comm (f ⁻¹' s) (g ⁻¹' t), ← hL, hmeasure_eq, hR]
  intro s t hs ht
  exact hstep2 s hs t ht
