import LeanLevy.RandomMeasure.PoissonRandomMeasure
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.Independence.Basic

/-!
Conditions: Actual Poisson point families with a common sigma-finite intensity on a measurable nonempty carrier; mapped laws require the explicit measurability and sigma-finiteness of the pushed intensity.

Objects: Measurable random measures, product Poisson laws on disjoint finite-mass counts, count-box generators of the Giry sigma-algebra, uniqueness by intensity and the actual measurable-map law.

Proof detail: Refine each finite test family into disjoint Boolean atoms, deleting the unused possibly infinite-mass empty atom. Compute their independent Poisson counts and reconstruct all count boxes; sigma-finite exhaustion and pi-system uniqueness then identify the complete measure law.

References: Günter Last; Mathew Penrose: Section 3.1, Definition 3.1(i)–(ii), p. 19; Günter Last and Mathew Penrose: Section 2.3, Proposition 2.10, pp. 14–15; Section 3.1, Proposition 3.2, p. 20.
Relation: A full law-level proof on the actual random-measure carrier. Counts on overlapping sets are reconstructed from disjoint atoms rather than incorrectly declared independent; infinite intensity is handled by finite-mass generators.
-/

/-
Copyright (c) 2026 OTSelector Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OTSelector Contributors
-/

/-!
# The law of a Poisson random measure

This file shows that the law of a Poisson random measure is determined by its intensity, and that
pushing the random measure forward by a measurable map produces a Poisson random measure with the
pushed-forward intensity.  These are the distributional invariance statements needed by the
finite-volume pressure recursion.

## Main definitions

* `OTSelector.Probability.CountBox` — the π-system of *count boxes*
  `{ν | ∀ i, ν (A i) ∈ B i}` for a finite family of finite-`m`-mass measurable sets `A i` and Borel
  sets `B i` of `ℝ≥0∞`.

## Main results

* `measurable_poissonRandomMeasure` — the Poisson random measure is a measurable map into the space
  of measures with the Giry σ-algebra.
* `poissonRandomMeasure_count_law` — the joint law of the counts on finitely many pairwise disjoint
  finite-mass sets is a product of Poisson laws.
* `isPiSystem_countBox`, `measurableSet_countBox`, `giry_eq_generateFrom_countBox` — the count boxes
  form a π-system of Giry-measurable sets which generates the Giry σ-algebra.
* `measure_law_eq_of_countBox_eq` — two probability laws on measures agreeing on count boxes agree
  everywhere.
* `poissonRandomMeasure_countBox_law_eq` — two Poisson random measures with the same intensity give
  the same count-box probabilities.
* `poissonRandomMeasure_law_eq` — same intensity implies the same law.
* `poissonRandomMeasure_map_law` — the law of the pushforward of a Poisson random measure is the law
  of the Poisson random measure with pushed-forward intensity.

The count-box comparison is proved by refining an arbitrary finite family into its Boolean atoms
(indexed by `Finset ι`), on which the counts are governed by `poissonRandomMeasure_count_law`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

set_option linter.style.haveILetI false

namespace OTSelector.Probability

/-! ### Measurability of the random measure -/

/-- The Poisson random measure is measurable as a map into the space of measures endowed with the
Giry σ-algebra: its evaluations on measurable sets are measurable by
`measurable_poissonRandomMeasure_apply`. -/
theorem measurable_poissonRandomMeasure {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} (hd : IsPoissonPointFamily K X m μ) :
    Measurable (poissonRandomMeasure K X) := by
  rw [Measure.measurable_measure]
  exact fun s hs =>
    measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hs

/-! ### The joint law of counts on disjoint sets -/

/-- **Joint law of the counts on a finite pairwise disjoint family.** For a pairwise disjoint finite
family of finite-mass measurable sets, the vector of Poisson random measure evaluations is
distributed as a product of Poisson laws with means `m (A i)`. -/
theorem poissonRandomMeasure_count_law {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A : ι → Set E)
    (hA : ∀ i, MeasurableSet (A i)) (hfin : ∀ i, m (A i) < ⊤)
    (hdisj : Pairwise (Function.onFun Disjoint A)) :
    μ.map (fun ω (i : ι) => poissonRandomMeasure K X ω (A i)) =
      Measure.pi (fun i => (poissonMeasure ((m (A i)).toNNReal)).map
        (Nat.cast : ℕ → ℝ≥0∞)) := by
  have hmeas : ∀ i, Measurable fun ω => poissonRandomMeasure K X ω (A i) := fun i =>
    measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point (hA i)
  have hind := iIndepFun_poissonRandomMeasure_apply (ι := ι) hd hA hfin hdisj
  rw [iIndepFun.map_fun_eq_pi_map (fun i => (hmeas i).aemeasurable) hind,
    show (fun i => μ.map fun ω => poissonRandomMeasure K X ω (A i))
        = (fun i => (poissonMeasure ((m (A i)).toNNReal)).map (Nat.cast : ℕ → ℝ≥0∞)) from
      funext fun i => map_poissonRandomMeasure_apply hd (hA i) (hfin i)]

/-! ### Count boxes -/

/-- A **count box**: a set of measures specified by finitely many conditions `ν (A i) ∈ B i`, where
the `A i` are measurable finite-`m`-mass sets and the `B i` are measurable subsets of `ℝ≥0∞`. -/
def CountBox (E : Type*) [MeasurableSpace E] (m : Measure E) : Set (Set (Measure E)) :=
  {s | ∃ (ι : Type) (_ : Fintype ι) (A : ι → Set E) (B : ι → Set ℝ≥0∞),
    (∀ i, MeasurableSet (A i)) ∧ (∀ i, m (A i) < ⊤) ∧
      (∀ i, MeasurableSet (B i)) ∧
      s = {ν : Measure E | ∀ i, ν (A i) ∈ B i}}

/-- Count boxes are closed under binary intersections: combine the two families over `ι ⊕ ι'`. -/
theorem isPiSystem_countBox (E : Type*) [MeasurableSpace E] (m : Measure E) :
    IsPiSystem (CountBox E m) := by
  intro s hs t ht _
  obtain ⟨ι, hι, A, B, hA, hfin, hB, rfl⟩ := hs
  obtain ⟨ι', hι', A', B', hA', hfin', hB', rfl⟩ := ht
  haveI := hι
  haveI := hι'
  classical
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim A A', Sum.elim B B', ?_, ?_, ?_, ?_⟩
  · rintro (i | i)
    · simpa using hA i
    · simpa using hA' i
  · rintro (i | i)
    · simpa using hfin i
    · simpa using hfin' i
  · rintro (i | i)
    · simpa using hB i
    · simpa using hB' i
  · ext ν
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Sum.forall, Sum.elim_inl, Sum.elim_inr]

/-- Every count box is measurable for the Giry σ-algebra: it is a finite intersection of preimages
of measurable sets under the measurable evaluations `ν ↦ ν (A i)`. -/
theorem measurableSet_countBox {E : Type*} [MeasurableSpace E] {m : Measure E}
    {s : Set (Measure E)} (hs : s ∈ CountBox E m) : MeasurableSet s := by
  obtain ⟨ι, hι, A, B, hA, hfin, hB, rfl⟩ := hs
  haveI := hι
  classical
  rw [show {ν : Measure E | ∀ i, ν (A i) ∈ B i}
      = ⋂ i ∈ (Finset.univ : Finset ι), {ν : Measure E | ν (A i) ∈ B i} from by
    ext ν; simp]
  exact Finset.measurableSet_biInter _ fun i _ => Measure.measurable_coe (hA i) (hB i)

/-- Measurability of a countable sum of `ℝ≥0∞`-valued measurable functions. -/
private theorem measurable_ennreal_tsum {α : Type*} {mα : MeasurableSpace α} {ι : Type*}
    [Countable ι] {f : ι → α → ℝ≥0∞} (h : ∀ i, @Measurable α ℝ≥0∞ mα _ (f i)) :
    @Measurable α ℝ≥0∞ mα _ (fun x => ∑' i, f i x) := by
  letI := mα
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  exact Measurable.iSup fun s => s.measurable_fun_sum fun i _ => h i

/-- For a σ-finite intensity `m`, the evaluations on finite-`m`-mass measurable sets generate the
Giry σ-algebra.  An arbitrary measurable set is a countable disjoint union of its intersections with
the finite-mass partition pieces, so its evaluation is a countable sum of finite-mass evaluations. -/
private theorem measurable_giry_coe {E : Type*} [MeasurableSpace E] {m : Measure E} [SigmaFinite m]
    {s : Set E} (hs : MeasurableSet s) :
    Measurable[MeasurableSpace.generateFrom (CountBox E m)]
      (fun μ : Measure E => μ s) := by
  classical
  have hpiece : ∀ k : ℕ, Measurable[MeasurableSpace.generateFrom (CountBox E m)]
      (fun μ : Measure E => μ (s ∩ prmPiece m k)) := by
    intro k
    refine Measurable.of_comap_le ?_
    rw [show ENNReal.measurableSpace
          = MeasurableSpace.generateFrom {t : Set ℝ≥0∞ | MeasurableSet t} from
        MeasurableSpace.generateFrom_measurableSet.symm,
      MeasurableSpace.comap_generateFrom]
    refine MeasurableSpace.generateFrom_le ?_
    rintro t ⟨u, hu, rfl⟩
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨Unit, inferInstance, fun _ => s ∩ prmPiece m k, fun _ => u,
        fun _ => hs.inter measurableSet_prmPiece,
        fun _ => lt_of_le_of_lt (measure_mono Set.inter_subset_right) measure_prmPiece_lt_top,
        fun _ => hu, by ext ν; simp⟩
  have hEq : s = ⋃ k, s ∩ prmPiece m k := by
    rw [← Set.inter_iUnion, iUnion_prmPiece, Set.inter_univ]
  have hfun : (fun μ : Measure E => μ s) = fun μ => ∑' k, μ (s ∩ prmPiece m k) := by
    funext μ
    have hnum : μ s = ∑' k, μ (s ∩ prmPiece m k) := by
      conv_lhs => rw [hEq]
      exact measure_iUnion
        (fun i j hij => (pairwise_disjoint_prmPiece hij).mono
          Set.inter_subset_right Set.inter_subset_right)
        (fun k => hs.inter measurableSet_prmPiece)
    exact hnum
  rw [hfun]
  exact measurable_ennreal_tsum (mα := MeasurableSpace.generateFrom (CountBox E m)) hpiece

/-- The Giry σ-algebra on measures is generated by the count boxes: count boxes are Giry-measurable,
and conversely every evaluation `ν ↦ ν A` on a measurable set is a countable sum of finite-mass
evaluations, each of which is a count box. -/
theorem giry_eq_generateFrom_countBox (E : Type*) [MeasurableSpace E] (m : Measure E)
    [SigmaFinite m] :
    (inferInstance : MeasurableSpace (Measure E)) = MeasurableSpace.generateFrom (CountBox E m) := by
  rw [show (inferInstance : MeasurableSpace (Measure E)) =
      ⨆ (s : Set E) (_ : MeasurableSet s),
        (borel ℝ≥0∞).comap fun μ : Measure E => μ s from rfl]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun s => iSup_le fun hs => ?_
    exact (measurable_giry_coe (m := m) hs).comap_le
  · exact MeasurableSpace.generateFrom_le fun t ht => measurableSet_countBox ht

/-! ### Uniqueness from count-box laws -/

/-- **Uniqueness from count-box laws.** Two probability measures on `Measure E` that agree on every
count box agree on the whole Giry σ-algebra, hence are equal. -/
theorem measure_law_eq_of_countBox_eq {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {E : Type} [MeasurableSpace E] {m : Measure E} [SigmaFinite m]
    {μ : Measure Ω} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {N : Ω → Measure E} {N' : Ω' → Measure E}
    (hN : Measurable N) (hN' : Measurable N')
    (h : ∀ s ∈ CountBox E m, μ (N ⁻¹' s) = μ' (N' ⁻¹' s)) :
    μ.map N = μ'.map N' := by
  haveI : IsProbabilityMeasure (μ.map N) := Measure.isProbabilityMeasure_map hN.aemeasurable
  haveI : IsProbabilityMeasure (μ'.map N') := Measure.isProbabilityMeasure_map hN'.aemeasurable
  refine ext_of_generate_finite (CountBox E m) (giry_eq_generateFrom_countBox E m)
    (isPiSystem_countBox E m) ?_ ?_
  · intro s hs
    rw [Measure.map_apply hN (measurableSet_countBox hs),
      Measure.map_apply hN' (measurableSet_countBox hs)]
    exact h s hs
  · rw [Measure.map_apply hN MeasurableSet.univ, Measure.map_apply hN' MeasurableSet.univ]
    simp

/-! ### Boolean atoms of a finite family

For a finite family `A : ι → Set E`, the *atom* of a finset `S : Finset ι` is the set of points
whose membership pattern in the family is exactly `S`.  Atoms form a finite partition of `E` refining
the family: `A i` is the disjoint union of the atoms over all `S` containing `i`.  We replace the
atom `∅` (whose mass may be infinite) by the empty set, which does not affect any of the
decompositions. -/

/-- The atom of a membership pattern `S`: the points lying in exactly the sets `A i` with `i ∈ S`. -/
private def countAtom {E : Type} {ι : Type} (A : ι → Set E) (S : Finset ι) : Set E :=
  {x : E | ∀ i, x ∈ A i ↔ i ∈ S}

/-- Membership in an atom is the defining membership-pattern condition. -/
private theorem mem_countAtom {E : Type} {ι : Type} {A : ι → Set E} {S : Finset ι} {x : E} :
    x ∈ countAtom A S ↔ ∀ i, x ∈ A i ↔ i ∈ S :=
  Iff.rfl

/-- Atoms are measurable for a measurable family. -/
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

/-- Distinct atoms are disjoint. -/
private theorem pairwise_disjoint_countAtom {E : Type} {ι : Type} (A : ι → Set E) :
    Pairwise (Function.onFun Disjoint (countAtom A)) := by
  intro S T hST
  change Disjoint (countAtom A S) (countAtom A T)
  rw [Set.disjoint_left]
  intro x hxS hxT
  exact hST (Finset.ext fun i =>
    (mem_countAtom.mp hxS i).symm.trans (mem_countAtom.mp hxT i))

/-- `A i` is the disjoint union of the atoms whose pattern contains `i`. -/
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

/-- The mass of `A i` is the sum of the masses of the atoms of its memberships. -/
private theorem measure_eq_sum_countAtom {E : Type} [MeasurableSpace E] {ι : Type} [Fintype ι]
    [DecidableEq ι] {A : ι → Set E} (hA : ∀ i, MeasurableSet (A i)) (ν : Measure E) (i : ι) :
    ν (A i) = ∑ S ∈ (Finset.univ.filter fun S : Finset ι => i ∈ S), ν (countAtom A S) := by
  classical
  rw [eq_iUnion_countAtom A i]
  exact measure_biUnion_finset
    (fun a _ b _ hab => pairwise_disjoint_countAtom A hab)
    (fun b _ => measurableSet_countAtom hA b)

/-- The atom of a pattern `S`, with the empty pattern replaced by `∅` so that every member of the
family has finite `m`-mass.  Since no `A i` can contain a point of the atom `∅`, this replacement
does not change any decomposition. -/
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

/-! ### Count-box agreement for a common intensity -/

/-- **Count-box probabilities agree for Poisson random measures with the same intensity.**

Unpack a count box as `{ν | ∀ i, ν (A i) ∈ B i}` and refine the family `A` into its finitely many
Boolean atoms.  On each atom the counts are finite-mass, so `poissonRandomMeasure_count_law` gives
the same joint law on both sides.  The count vector `(ν (A i))_i` is a deterministic measurable
function of the atom-count vector, so the count-box probabilities agree. -/
theorem poissonRandomMeasure_countBox_law_eq {Ω Ω' E : Type} [MeasurableSpace E]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {K' : ℕ → Ω' → ℕ} {X' : ℕ → ℕ → Ω' → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E] {μ : Measure Ω} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hd : IsPoissonPointFamily K X m μ) (hd' : IsPoissonPointFamily K' X' m μ')
    {s : Set (Measure E)} (hs : s ∈ CountBox E m) :
    μ (poissonRandomMeasure K X ⁻¹' s) = μ' (poissonRandomMeasure K' X' ⁻¹' s) := by
  obtain ⟨ι, hι, A, B, hA, hfin, hB, rfl⟩ := hs
  haveI := hι
  classical
  -- The atom-count vectors on the two sides.
  set V : Ω → (Finset ι → ℝ≥0∞) :=
    fun ω S => poissonRandomMeasure K X ω (countAtom' A S) with hV_def
  set V' : Ω' → (Finset ι → ℝ≥0∞) :=
    fun ω S => poissonRandomMeasure K' X' ω (countAtom' A S) with hV'_def
  -- The deterministic map from atom counts to the counts on `A i`.
  set ψ : (Finset ι → ℝ≥0∞) → (ι → ℝ≥0∞) :=
    fun v i => ∑ S ∈ (Finset.univ.filter fun S : Finset ι => i ∈ S), v S with hψ_def
  have hψ : Measurable ψ := by
    rw [hψ_def]
    exact measurable_pi_lambda _ fun i =>
      Finset.measurable_sum _ fun S _ => measurable_pi_apply S
  -- The target box in the count-vector space.
  set T : Set (ι → ℝ≥0∞) := {v | ∀ i, v i ∈ B i} with hT_def
  have hT : MeasurableSet T := by
    rw [hT_def,
      show {v : ι → ℝ≥0∞ | ∀ i, v i ∈ B i}
          = ⋂ i ∈ (Finset.univ : Finset ι), {v : ι → ℝ≥0∞ | v i ∈ B i} from by
        ext v; simp]
    exact Finset.measurableSet_biInter _ fun i _ => measurable_pi_apply i (hB i)
  have hU : MeasurableSet (ψ ⁻¹' T) := hψ hT
  -- Measurability of the two atom-count vectors.
  have hV_meas : Measurable V := by
    rw [hV_def]
    exact measurable_pi_lambda _ fun S =>
      measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point
        (measurableSet_countAtom' hA S)
  have hV'_meas : Measurable V' := by
    rw [hV'_def]
    exact measurable_pi_lambda _ fun S =>
      measurable_poissonRandomMeasure_apply hd'.measurable_count hd'.measurable_point
        (measurableSet_countAtom' hA S)
  -- The two atom-count vectors have the same law, by the disjoint-family count law.
  have hlaw : μ.map V = μ'.map V' := by
    rw [hV_def, hV'_def]
    rw [poissonRandomMeasure_count_law hd (countAtom' A) (measurableSet_countAtom' hA)
        (measure_countAtom'_lt_top hfin) (pairwise_disjoint_countAtom' A),
      poissonRandomMeasure_count_law hd' (countAtom' A) (measurableSet_countAtom' hA)
        (measure_countAtom'_lt_top hfin) (pairwise_disjoint_countAtom' A)]
  -- The count vector on `A i` is the image of the atom-count vector under `ψ`.
  have hpre : poissonRandomMeasure K X ⁻¹' {ν : Measure E | ∀ i, ν (A i) ∈ B i}
      = V ⁻¹' (ψ ⁻¹' T) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hV_def, hψ_def, hT_def]
    constructor
    · intro h i
      rw [← measure_eq_sum_countAtom' hA (poissonRandomMeasure K X ω) i]
      exact h i
    · intro h i
      rw [measure_eq_sum_countAtom' hA (poissonRandomMeasure K X ω) i]
      exact h i
  have hpre' : poissonRandomMeasure K' X' ⁻¹' {ν : Measure E | ∀ i, ν (A i) ∈ B i}
      = V' ⁻¹' (ψ ⁻¹' T) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hV'_def, hψ_def, hT_def]
    constructor
    · intro h i
      rw [← measure_eq_sum_countAtom' hA (poissonRandomMeasure K' X' ω) i]
      exact h i
    · intro h i
      rw [measure_eq_sum_countAtom' hA (poissonRandomMeasure K' X' ω) i]
      exact h i
  calc μ (poissonRandomMeasure K X ⁻¹' {ν : Measure E | ∀ i, ν (A i) ∈ B i})
      = μ (V ⁻¹' (ψ ⁻¹' T)) := by rw [hpre]
    _ = (μ.map V) (ψ ⁻¹' T) := (Measure.map_apply hV_meas hU).symm
    _ = (μ'.map V') (ψ ⁻¹' T) := by rw [hlaw]
    _ = μ' (V' ⁻¹' (ψ ⁻¹' T)) := Measure.map_apply hV'_meas hU
    _ = μ' (poissonRandomMeasure K' X' ⁻¹' {ν : Measure E | ∀ i, ν (A i) ∈ B i}) := by
        rw [hpre']

/-- **Same-intensity uniqueness.** Two Poisson random measures with the same intensity have the same
law. -/
theorem poissonRandomMeasure_law_eq {Ω Ω' E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {K' : ℕ → Ω' → ℕ}
    {X' : ℕ → ℕ → Ω' → E} {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hd : IsPoissonPointFamily K X m μ) (hd' : IsPoissonPointFamily K' X' m μ') :
    μ.map (poissonRandomMeasure K X) = μ'.map (poissonRandomMeasure K' X') :=
  measure_law_eq_of_countBox_eq (measurable_poissonRandomMeasure hd)
    (measurable_poissonRandomMeasure hd')
    (fun _s hs => poissonRandomMeasure_countBox_law_eq hd hd' hs)

/-! ### Pullback atoms and the pushforward count-box law -/

/-- Atoms commute with preimages. -/
private theorem preimage_countAtom {E E' : Type} (e : E → E') {ι : Type} (A : ι → Set E')
    (S : Finset ι) :
    countAtom (fun i => e ⁻¹' A i) S = e ⁻¹' countAtom A S := by
  ext x
  simp only [mem_countAtom, Set.mem_preimage]

/-- The empty-pattern-adjusted atoms commute with preimages. -/
private theorem preimage_countAtom' {E E' : Type} (e : E → E') {ι : Type} (A : ι → Set E')
    (S : Finset ι) :
    countAtom' (fun i => e ⁻¹' A i) S = e ⁻¹' countAtom' A S := by
  classical
  by_cases hS : S.Nonempty
  · rw [countAtom'_eq_countAtom _ hS, countAtom'_eq_countAtom _ hS, preimage_countAtom]
  · rw [countAtom'_eq_empty _ hS, countAtom'_eq_empty _ hS, Set.preimage_empty]

/-- Preimages of a pairwise disjoint family are pairwise disjoint. -/
private theorem pairwise_disjoint_preimage {E E' : Type} (e : E → E') {ι : Type}
    {C : ι → Set E'} (hC : Pairwise (Function.onFun Disjoint C)) :
    Pairwise (Function.onFun Disjoint (fun i => e ⁻¹' C i)) := by
  intro i j hij
  change Disjoint (e ⁻¹' C i) (e ⁻¹' C j)
  rw [Set.disjoint_left]
  intro x hx1 hx2
  exact (Set.disjoint_left.mp (hC hij)) (by simpa using hx1) (by simpa using hx2)

/-- **Count-box agreement under a measurable pushforward.** For a count box in the target space,
the probability that the pushforward of a Poisson random measure with intensity `m` lies in the box
equals the probability that a Poisson random measure with intensity `m.map e` lies in the box.

The proof refines the target family `A` into its Boolean atoms `C S`.  On the source side the
relevant sets are the pullbacks `D S = e ⁻¹' C S`, whose atoms they are; the rate of each atom is
`m (D S) = (m.map e) (C S)`, so the atom-count vectors have the same product law on both sides by
`poissonRandomMeasure_count_law`.  The count vector is a deterministic function of the atom-count
vector, giving the box equality. -/
private theorem countBox_law_eq_map {Ω Ω' E E' : Type} [MeasurableSpace E] [MeasurableSpace E']
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {K' : ℕ → Ω' → ℕ} {X' : ℕ → ℕ → Ω' → E'}
    {m : Measure E} [SigmaFinite m] [Nonempty E] {μ : Measure Ω} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (e : E → E') (he : Measurable e) [SigmaFinite (m.map e)] [Nonempty E']
    (hd : IsPoissonPointFamily K X m μ) (hd' : IsPoissonPointFamily K' X' (m.map e) μ')
    {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Set E'}
    (hA : ∀ i, MeasurableSet (A i)) (hfin : ∀ i, (m.map e) (A i) < ⊤)
    {B : ι → Set ℝ≥0∞} (hB : ∀ i, MeasurableSet (B i)) :
    μ' (poissonRandomMeasure K' X' ⁻¹' {ν : Measure E' | ∀ i, ν (A i) ∈ B i}) =
      μ ((fun ω => (poissonRandomMeasure K X ω).map e) ⁻¹'
        {ν : Measure E' | ∀ i, ν (A i) ∈ B i}) := by
  classical
  -- Atoms of the target family and their pullbacks.
  set C : Finset ι → Set E' := fun S => countAtom' A S with hC_def
  set D : Finset ι → Set E := fun S => e ⁻¹' C S with hD_def
  set V' : Ω' → (Finset ι → ℝ≥0∞) := fun ω S => poissonRandomMeasure K' X' ω (C S) with hV'_def
  set V : Ω → (Finset ι → ℝ≥0∞) := fun ω S => poissonRandomMeasure K X ω (D S) with hV_def
  set ψ : (Finset ι → ℝ≥0∞) → (ι → ℝ≥0∞) :=
    fun v i => ∑ S ∈ (Finset.univ.filter fun S : Finset ι => i ∈ S), v S with hψ_def
  set T : Set (ι → ℝ≥0∞) := {v | ∀ i, v i ∈ B i} with hT_def
  have hC_meas : ∀ S, MeasurableSet (C S) := fun S => measurableSet_countAtom' hA S
  have hD_meas : ∀ S, MeasurableSet (D S) := fun S => by
    rw [hD_def]; exact he (hC_meas S)
  have hC_fin : ∀ S, (m.map e) (C S) < ⊤ := fun S => measure_countAtom'_lt_top hfin S
  have hD_fin : ∀ S, m (D S) < ⊤ := by
    intro S
    rw [hD_def, ← Measure.map_apply he (hC_meas S)]
    exact hC_fin S
  have hC_disj : Pairwise (Function.onFun Disjoint C) := pairwise_disjoint_countAtom' A
  have hD_disj : Pairwise (Function.onFun Disjoint D) := pairwise_disjoint_preimage e hC_disj
  -- The atom-count vectors have the same law.
  have hlaw' : μ'.map V'
      = Measure.pi (fun S => (poissonMeasure (((m.map e) (C S)).toNNReal)).map
          (Nat.cast : ℕ → ℝ≥0∞)) :=
    poissonRandomMeasure_count_law hd' C hC_meas hC_fin hC_disj
  have hlaw : μ.map V
      = Measure.pi (fun S => (poissonMeasure ((m (D S)).toNNReal)).map
          (Nat.cast : ℕ → ℝ≥0∞)) :=
    poissonRandomMeasure_count_law hd D hD_meas hD_fin hD_disj
  have hrate : (fun S => (poissonMeasure (((m.map e) (C S)).toNNReal)).map
        (Nat.cast : ℕ → ℝ≥0∞))
      = fun S => (poissonMeasure ((m (D S)).toNNReal)).map (Nat.cast : ℕ → ℝ≥0∞) := by
    funext S
    rw [hD_def, Measure.map_apply he (hC_meas S)]
  have hVlaw : μ'.map V' = μ.map V := by rw [hlaw', hlaw, hrate]
  -- The deterministic map from atom counts to the counts on `A i`.
  have hψ : Measurable ψ := by
    rw [hψ_def]
    exact measurable_pi_lambda _ fun i =>
      Finset.measurable_sum _ fun S _ => measurable_pi_apply S
  have hT : MeasurableSet T := by
    rw [hT_def,
      show {v : ι → ℝ≥0∞ | ∀ i, v i ∈ B i}
          = ⋂ i ∈ (Finset.univ : Finset ι), {v : ι → ℝ≥0∞ | v i ∈ B i} from by
        ext v; simp]
    exact Finset.measurableSet_biInter _ fun i _ => measurable_pi_apply i (hB i)
  have hU : MeasurableSet (ψ ⁻¹' T) := hψ hT
  have hV_meas : Measurable V := by
    rw [hV_def]
    exact measurable_pi_lambda _ fun S =>
      measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point (hD_meas S)
  have hV'_meas : Measurable V' := by
    rw [hV'_def]
    exact measurable_pi_lambda _ fun S =>
      measurable_poissonRandomMeasure_apply hd'.measurable_count hd'.measurable_point (hC_meas S)
  -- Decomposition of the pullback family into its atoms.
  have hD_decomp : ∀ (ν : Measure E) (i : ι),
      ν (e ⁻¹' A i) = ∑ S ∈ (Finset.univ.filter fun S : Finset ι => i ∈ S), ν (D S) := by
    intro ν i
    have h := measure_eq_sum_countAtom' (A := fun i => e ⁻¹' A i)
      (fun i => he (hA i)) ν i
    rw [h]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [preimage_countAtom', hD_def, hC_def]
  -- The two events are the preimages of `T` under `ψ` of the atom-count vectors.
  have hleft_event : poissonRandomMeasure K' X' ⁻¹' {ν : Measure E' | ∀ i, ν (A i) ∈ B i}
      = V' ⁻¹' (ψ ⁻¹' T) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hV'_def, hψ_def, hT_def, hC_def]
    constructor
    · intro h i
      rw [← measure_eq_sum_countAtom' hA (poissonRandomMeasure K' X' ω) i]
      exact h i
    · intro h i
      rw [measure_eq_sum_countAtom' hA (poissonRandomMeasure K' X' ω) i]
      exact h i
  have hright_event : (fun ω => (poissonRandomMeasure K X ω).map e) ⁻¹'
        {ν : Measure E' | ∀ i, ν (A i) ∈ B i} = V ⁻¹' (ψ ⁻¹' T) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hV_def, hψ_def, hT_def]
    constructor
    · intro h i
      have hi := h i
      rw [Measure.map_apply he (hA i)] at hi
      rw [← hD_decomp (poissonRandomMeasure K X ω) i]
      exact hi
    · intro h i
      rw [Measure.map_apply he (hA i)]
      rw [hD_decomp (poissonRandomMeasure K X ω) i]
      exact h i
  calc μ' (poissonRandomMeasure K' X' ⁻¹' {ν : Measure E' | ∀ i, ν (A i) ∈ B i})
      = μ' (V' ⁻¹' (ψ ⁻¹' T)) := by rw [hleft_event]
    _ = (μ'.map V') (ψ ⁻¹' T) := (Measure.map_apply hV'_meas hU).symm
    _ = (μ.map V) (ψ ⁻¹' T) := by rw [hVlaw]
    _ = μ (V ⁻¹' (ψ ⁻¹' T)) := Measure.map_apply hV_meas hU
    _ = μ ((fun ω => (poissonRandomMeasure K X ω).map e) ⁻¹'
          {ν : Measure E' | ∀ i, ν (A i) ∈ B i}) := by rw [hright_event]

/-! ### Pushforward of the intensity -/

/-- **Pushforward law.** Pushing a Poisson random measure with intensity `m` forward by a measurable
map `e` gives a Poisson random measure with intensity `m.map e`, in law. -/
theorem poissonRandomMeasure_map_law {Ω Ω' E E' : Type} [MeasurableSpace E] [MeasurableSpace E']
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {K' : ℕ → Ω' → ℕ} {X' : ℕ → ℕ → Ω' → E'} {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (e : E → E') (he : Measurable e) [SigmaFinite (m.map e)] [Nonempty E']
    (hd : IsPoissonPointFamily K X m μ) (hd' : IsPoissonPointFamily K' X' (m.map e) μ') :
    μ'.map (poissonRandomMeasure K' X') =
      μ.map (fun ω => (poissonRandomMeasure K X ω).map e) := by
  have hmap : Measurable fun ω => (poissonRandomMeasure K X ω).map e :=
    (Measure.measurable_map e he).comp (measurable_poissonRandomMeasure hd)
  have hmap' : Measurable (poissonRandomMeasure K' X') := measurable_poissonRandomMeasure hd'
  refine measure_law_eq_of_countBox_eq (m := m.map e) (μ := μ') (μ' := μ)
    (N := poissonRandomMeasure K' X')
    (N' := fun ω => (poissonRandomMeasure K X ω).map e) hmap' hmap ?_
  intro s hs
  obtain ⟨ι, hι, A, B, hA, hfin, hB, rfl⟩ := hs
  haveI := hι
  classical
  exact countBox_law_eq_map e he hd hd' hA hfin hB

end OTSelector.Probability
