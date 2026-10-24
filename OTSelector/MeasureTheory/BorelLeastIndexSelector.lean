import Mathlib.Data.Finset.Range
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic

/-!
## Lemma skeleton

* **Conditions:** A measurable real H and countable measurable test predicates with some successful test whenever H>0. Later partition/map statements require only their displayed setwise hypotheses.
* **Objects:** A least successful natural index on the positive set, measurable level sets, a countable block partition and measurable block map.
* **Proof detail:** Define the selector by Nat.find on positive points, use level=positive intersect test_j minus earlier tests, and assemble the countable discrete coordinate.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4, Appendix*, Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.
  https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32

**Relationship to the sources:** Pure countable Borel construction. No ray geometry, continuity of a surplus, coupling or Finsler premise is part of these generic statements.
-/

/-!
# Borel active-block space (eq:intrinsic-active-marker)

This module constructs the Borel block space of the paper's structural
invariance theorem (main.tex:958), the step eq:intrinsic-active-marker of the
section Intrinsic active ray components (main.tex, around lines 935-950).
For a ray label space Z with surplus H : Z -> R -> R (constructed for scalar
couplings in FinslerIntrinsicActiveRayDataConstruction.lean) and a block test
test z r j (the paper's test that the rational r_j lies in the same
positive-flux component as r, formalized abstractly here), we prove:

* exists_borel_leastIndex_blockSpace: a least-index block selector idx z r
  (first index whose test succeeds on the positive-flux set), whose level
  sets are Borel whenever the flux and the test family are Borel;
* blockSpace_iUnion_blocks: the Borel block-label sets
  {p | 0 < H p.1 p.2 and idx p.1 p.2 = j} partition the positive-flux set;
* blockMap_measurableOnPos: the block map b(z,r) = (z, idx z r) is Borel on
  the positive-flux set, so pushforwards of physical laws carried there give
  the block quotient laws eq:intrinsic-active-quotient.

The remaining analytic inputs are kept explicit: the segment test
eq:intrinsic-active-marker must be supplied as a Borel test family with the
positive-set existence property; its identification with rational segment
positivity (continuity on the compact segment), the actual Finsler
forward-coupling ray data of prop:general-optimal-face (main.tex:422) and
prop:ray-forward-criterion (main.tex:524), the conullness of the active sets,
the block matching T with its injective-image Borel inverse, and the
two-cover containment remain the outstanding geometric inputs.
-/

open Set Function MeasureTheory

noncomputable section
namespace OTSelector.Reconstruction

set_option linter.unusedVariables false
set_option linter.deprecated false

/-- Borel least-index block space eq:intrinsic-active-marker. -/
theorem exists_borel_leastIndex_blockSpace
    {Z : Type*} [MeasurableSpace Z] (H : Z → ℝ → ℝ)
    (hH : Measurable (fun p : Z × ℝ ↦ H p.1 p.2))
    (test : Z → ℝ → ℕ → Prop)
    (htest : ∀ j, MeasurableSet {p : Z × ℝ | test p.1 p.2 j})
    (hex : ∀ z r, 0 < H z r → ∃ j, test z r j) :
    ∃ idx : Z → ℝ → ℕ,
      (∀ (z : Z) (r : ℝ) (h : 0 < H z r),
        test z r (idx z r) ∧ ∀ i < idx z r, ¬ test z r i) ∧
      (∀ j : ℕ, MeasurableSet {p : Z × ℝ | 0 < H p.1 p.2 ∧ idx p.1 p.2 = j}) := by
  classical
  let idx : Z → ℝ → ℕ := fun z r ↦
    if h : 0 < H z r then Nat.find (hex z r h) else 0
  have hsH : MeasurableSet {p : Z × ℝ | 0 < H p.1 p.2} :=
    hH measurableSet_Ioi
  have hidx_pos : ∀ (z : Z) (r : ℝ) (h : 0 < H z r),
      idx z r = Nat.find (hex z r h) := by
    intro z r h
    simp only [idx, dif_pos h]
  have hspec : ∀ (z : Z) (r : ℝ) (h : 0 < H z r),
      test z r (idx z r) ∧ ∀ i < idx z r, ¬ test z r i := by
    intro z r h
    rw [hidx_pos z r h]
    exact ⟨Nat.find_spec (hex z r h),
      fun i hi ↦ Nat.find_min (hex z r h) hi⟩
  have hlevel : ∀ j : ℕ, MeasurableSet
      {p : Z × ℝ | 0 < H p.1 p.2 ∧ idx p.1 p.2 = j} := by
    intro j
    have hbase : MeasurableSet
        {p : Z × ℝ | test p.1 p.2 j ∧ ∀ i < j, ¬ test p.1 p.2 i} := by
      have h1 : MeasurableSet {p : Z × ℝ | test p.1 p.2 j} := htest j
      have h2 : MeasurableSet
          {p : Z × ℝ | ∀ i < j, ¬ test p.1 p.2 i} := by
        have hset : {p : Z × ℝ | ∀ i < j, ¬ test p.1 p.2 i} =
            ⋂ i ∈ Finset.range j, {p : Z × ℝ | ¬ test p.1 p.2 i} := by
          ext p
          simp only [Set.mem_iInter, Finset.mem_range, Set.mem_ofPred_eq]
        rw [hset]
        exact MeasurableSet.biInter (Finset.countable_toSet _) fun i _ ↦ (htest i).compl
      exact h1.inter h2
    have heq : {p : Z × ℝ | 0 < H p.1 p.2 ∧ idx p.1 p.2 = j} =
        {p : Z × ℝ | 0 < H p.1 p.2} ∩
          {p : Z × ℝ | test p.1 p.2 j ∧ ∀ i < j, ¬ test p.1 p.2 i} := by
      ext p
      constructor
      · rintro ⟨hpos, hidx⟩
        have hp := hspec p.1 p.2 hpos
        rw [hidx] at hp
        exact ⟨hpos, hp⟩
      · rintro ⟨hpos, htj, hlow⟩
        refine ⟨hpos, ?_⟩
        rw [hidx_pos p.1 p.2 hpos]
        exact (Nat.find_eq_iff (hex p.1 p.2 hpos)).mpr ⟨htj, hlow⟩
    rw [heq]
    exact hsH.inter hbase
  exact ⟨idx, hspec, hlevel⟩

/-- Block partition eq:intrinsic-active-marker. -/
theorem blockSpace_iUnion_blocks
    {Z : Type*} (H : Z → ℝ → ℝ) (idx : Z → ℝ → ℕ)
    (hex : ∀ (z : Z) (r : ℝ), 0 < H z r → ∃ j, idx z r = j) :
    {p : Z × ℝ | 0 < H p.1 p.2}
      = ⋃ j : ℕ, {p : Z × ℝ | 0 < H p.1 p.2 ∧ idx p.1 p.2 = j} := by
  ext p
  constructor
  · intro hp
    obtain ⟨j, hj⟩ := hex p.1 p.2 hp
    exact Set.mem_iUnion.mpr ⟨j, hp, hj⟩
  · intro hp
    obtain ⟨j, hpj, -⟩ := Set.mem_iUnion.mp hp
    exact hpj

/-- Measurability of the block map on the positive-flux set. -/
theorem blockMap_measurableOnPos
    {Z : Type*} [MeasurableSpace Z] (H : Z → ℝ → ℝ) (idx : Z → ℝ → ℕ)
    (hlevel : ∀ j : ℕ, MeasurableSet
      {p : Z × ℝ | 0 < H p.1 p.2 ∧ idx p.1 p.2 = j}) :
    Measurable (fun q : {p : Z × ℝ // 0 < H p.1 p.2} ↦
      (q.1.1, idx q.1.1 q.1.2)) := by
  have hidx : Measurable (fun q : {p : Z × ℝ // 0 < H p.1 p.2} ↦
      idx q.1.1 q.1.2) := by
    refine measurable_to_countable' fun j ↦ ?_
    have hpre : (fun q : {p : Z × ℝ // 0 < H p.1 p.2} ↦
        idx q.1.1 q.1.2) ⁻¹' {j} =
        Subtype.val ⁻¹' ({p : Z × ℝ | 0 < H p.1 p.2 ∧ idx p.1 p.2 = j}) := by
      ext q
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      constructor
      · intro hq
        exact ⟨q.2, hq⟩
      · rintro ⟨-, hq⟩
        exact hq
    rw [hpre]
    exact (hlevel j).preimage measurable_subtype_coe
  exact (measurable_fst.comp measurable_subtype_coe).prodMk hidx

end OTSelector.Reconstruction