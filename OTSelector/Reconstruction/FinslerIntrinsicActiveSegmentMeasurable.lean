import OTSelector.Reconstruction.FinslerIntrinsicActiveNullLabel
import OTSelector.Topology.Real.PositiveComponentSegmentMinimum
import OTSelector.MeasureTheory.BorelLeastIndexSelector

/-!
# Measurability of the segment test and of the component enumeration

This module addresses the remaining gaps of FinslerIntrinsicActiveMarker.lean
for the structural invariance theorem (main.tex:958).

## The segment test is Borel

For a ray surplus `H : Z → ℝ → ℝ` jointly measurable in `(z, r)` and
continuous in the ray parameter `r`, the paper's segment test value
`segmentMin H_z(r) (r_j)` (the infimum/minimum of `H_z` on the compact segment
between `r` and the rational `r_j`) is measurable in `(z, r)`: it is the
infimum of the countable family of measurable functions
`(z,r) ↦ H_z((1-u)r + u r_j)` over the rational `u ∈ [0,1]`, and the infimum
over the rationals equals the infimum over the whole segment by density (the
continuity of `H_z` identifies both with the minimum on the compact segment).
Consequently the set `{(z,r) | 0 < segmentMin H_z(r) (r_j)}` is Borel.

## The least-index component enumeration is Borel

From the joint measurability and continuity we derive the marker-existence
property of `eq:intrinsic-active-marker` (every active parameter has a rational
code whose segment test passes, by the segment-positivity criterion and
rational density), then instantiate the Borel least-index block-space
construction of `FinslerIntrinsicActiveRayDataFinsler` with the measurable
segment test.  This yields a Borel least-index function `idx z r`, Borel block
level sets `{(z,r) | 0 < H_z(r) ∧ idx z r = j}`, and a Borel block map
`(z,r) ↦ (z, idx z r)` on the active set — the measurable component
enumeration of `eq:intrinsic-active-marker`.

## The ℕ-enumeration interface obstruction

The `IntrinsicActiveRayData` interface requires every one of its `ℕ`-many block
labels to be nonempty and pairwise disjoint; combined with `IsComponentCover`
this forces a bijective enumeration of the active components, hence infinitely
many active components on every ray.  We prove this obstruction
(`infinite_activeComponents_of_isComponentCover`), so a ray whose active set has
only finitely many components admits no such data: the honest interface change
is either to allow inactive/empty labels or to use the ℚ-indexed rational-code
family of `FinslerIntrinsicActiveMarker.exists_component_cover_of_rayFlux`.
-/

open Set Function MeasureTheory
open scoped ENNReal MeasureTheory

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-! ## Measurability of the rational segment infimum -/

/-- The rational segment-test value of a family of ray surpluses: the infimum
of the surplus over the rational parameters of the segment between `r` and the
rational `q j`. -/
def segmentMinRatFamily {Z : Type*} (H : Z → ℝ → ℝ) (q : ℕ → ℚ) (j : ℕ) :
    Z × ℝ → ℝ :=
  fun p => sInf ((fun u : ℚ =>
    H p.1 ((1 - (u : ℝ)) * p.2 + (u : ℝ) * ((q j : ℚ) : ℝ))) ''
      {u : ℚ | (u : ℝ) ∈ Icc (0 : ℝ) 1})

/-- **Joint measurability of the rational segment infimum.**  It is the
infimum over the countable family of the measurable functions
`(z,r) ↦ H_z((1-u)r + u r_j)`, indexed by the rationals of `[0,1]`. -/
theorem measurable_segmentMinRatFamily {Z : Type*} [MeasurableSpace Z]
    {H : Z → ℝ → ℝ} (hH : Measurable fun p : Z × ℝ => H p.1 p.2)
    (q : ℕ → ℚ) (j : ℕ) :
    Measurable (segmentMinRatFamily H q j) := by
  refine Measurable.sInf (s := {u : ℚ | (u : ℝ) ∈ Icc (0 : ℝ) 1}) ?_ ?_
  · exact (Set.countable_univ).mono (Set.subset_univ _)
  · intro u hu
    have hmap : Measurable fun p : Z × ℝ =>
        (p.1, (1 - (u : ℝ)) * p.2 + (u : ℝ) * ((q j : ℚ) : ℝ)) :=
      Measurable.prodMk measurable_fst (by fun_prop)
    exact hH.comp hmap

/-- **The segment test set is Borel.** -/
theorem measurableSet_segmentTestRat {Z : Type*} [MeasurableSpace Z]
    {H : Z → ℝ → ℝ} (hH : Measurable fun p : Z × ℝ => H p.1 p.2)
    (q : ℕ → ℚ) (j : ℕ) :
    MeasurableSet {p : Z × ℝ | 0 < segmentMinRatFamily H q j p} := by
  exact (measurable_segmentMinRatFamily hH q j) measurableSet_Ioi

/-! ## Density of the rational segment parameters -/

/-- The rational points of `[0,1]` are dense in `[0,1]`. -/
theorem dense_rat_mem_Icc :
    Icc (0 : ℝ) 1 ⊆ closure ((fun u : ℚ => (u : ℝ)) '' {u : ℚ | (u : ℝ) ∈ Icc (0 : ℝ) 1}) := by
  intro x hx
  rcases lt_or_eq_of_le hx.1 with hx0 | hx0
  · rcases lt_or_eq_of_le hx.2 with hx1 | hx1
    · have hdense : Dense (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
      rw [mem_closure_iff]
      intro U hU hxU
      have hopen : IsOpen (U ∩ Ioo (0 : ℝ) 1) := hU.inter isOpen_Ioo
      have hmemU : x ∈ U ∩ Ioo (0 : ℝ) 1 := ⟨hxU, ⟨hx0, hx1⟩⟩
      have hxcl : x ∈ closure (Set.range ((↑) : ℚ → ℝ)) := by
        rw [hdense.closure_eq]
        exact Set.mem_univ x
      rw [mem_closure_iff] at hxcl
      obtain ⟨y, hy, hyS⟩ := hxcl (U ∩ Ioo (0 : ℝ) 1) hopen hmemU
      obtain ⟨r, rfl⟩ := hyS
      have hrI : ((r : ℝ)) ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt hy.2.1, le_of_lt hy.2.2⟩
      exact ⟨(r : ℝ), hy.1, ⟨r, hrI, rfl⟩⟩
    · have hx1' : x = ((1 : ℚ) : ℝ) := by rw [hx1]; norm_num
      rw [hx1']
      exact subset_closure (Set.mem_image_of_mem _ (by norm_num : ((1 : ℚ) : ℝ) ∈ Icc (0 : ℝ) 1))
  · have hx0' : x = ((0 : ℚ) : ℝ) := by rw [← hx0]; norm_num
    rw [hx0']
    exact subset_closure (Set.mem_image_of_mem _ (by norm_num : ((0 : ℚ) : ℝ) ∈ Icc (0 : ℝ) 1))

/-! ## The rational infimum equals the segment minimum -/

/-- The infimum of a continuous function over a compact set equals its infimum
over any subset that is dense in it (the infimum is attained, and the value at
the minimizer is a limit of values on the dense subset). -/
theorem sInf_image_eq_of_dense {f : ℝ → ℝ} (hf : Continuous f) {s t : Set ℝ}
    (hst : s ⊆ t) (hdense : t ⊆ closure s) (ht : IsCompact t) (hsne : s.Nonempty) :
    sInf (f '' t) = sInf (f '' s) := by
  have hS : IsCompact (f '' t) := ht.image hf
  have hSne : (f '' t).Nonempty := (hsne.mono hst).image f
  have hAsub : f '' s ⊆ f '' t := Set.image_mono hst
  have hAbdd : BddBelow (f '' s) := hS.bddBelow.mono hAsub
  have h1 : sInf (f '' t) ≤ sInf (f '' s) :=
    le_csInf (hsne.image f) (fun a ha => csInf_le hS.bddBelow (hAsub ha))
  have h2 : sInf (f '' s) ≤ sInf (f '' t) := by
    by_contra hle
    have hε : 0 < sInf (f '' s) - sInf (f '' t) :=
      sub_pos.mpr (lt_of_not_ge hle)
    have hmin : sInf (f '' t) ∈ f '' t := hS.sInf_mem hSne
    obtain ⟨x, hxt, hfx⟩ := hmin
    have hxcl : x ∈ closure s := hdense hxt
    have hmem : f x ∈ closure (f '' s) :=
      image_closure_subset_closure_image hf ⟨x, hxcl, rfl⟩
    have hmem' : sInf (f '' t) ∈ closure (f '' s) := by rwa [← hfx]
    obtain ⟨a, ha, hadist⟩ :=
      Metric.mem_closure_iff.mp hmem' (sInf (f '' s) - sInf (f '' t)) hε
    have hadist' : |a - sInf (f '' t)| < sInf (f '' s) - sInf (f '' t) := by
      rw [abs_sub_comm]
      rwa [Real.dist_eq] at hadist
    have hlt : a < sInf (f '' s) := by
      have h2' := (abs_lt.mp hadist').2
      linarith
    have hge : sInf (f '' s) ≤ a := csInf_le hAbdd ha
    linarith
  exact le_antisymm h1 h2

/-- **The rational segment infimum is the segment minimum.**  For a continuous
ray surplus, the infimum over the rational parameters of the segment equals
the infimum (minimum) over the whole segment. -/
theorem segmentMinRat_eq_segmentMin {H : ℝ → ℝ} (hH : Continuous H) {x y : ℝ} :
    sInf ((fun u : ℚ => H ((1 - (u : ℝ)) * x + (u : ℝ) * y)) ''
      {u : ℚ | (u : ℝ) ∈ Icc (0 : ℝ) 1}) = segmentMin H x y := by
  have hcont : Continuous fun t : ℝ => H ((1 - t) * x + t * y) := hH.comp (by fun_prop)
  have himg : (fun u : ℚ => H ((1 - (u : ℝ)) * x + (u : ℝ) * y)) ''
        {u : ℚ | (u : ℝ) ∈ Icc (0 : ℝ) 1}
      = (fun t : ℝ => H ((1 - t) * x + t * y)) ''
        ((fun u : ℚ => (u : ℝ)) '' {u : ℚ | (u : ℝ) ∈ Icc (0 : ℝ) 1}) := by
    rw [Set.image_image]
  rw [himg, segmentMin]
  refine Eq.symm (sInf_image_eq_of_dense (f := fun t : ℝ => H ((1 - t) * x + t * y))
    (s := (fun u : ℚ => (u : ℝ)) '' {u : ℚ | (u : ℝ) ∈ Icc (0 : ℝ) 1})
    (t := Icc (0 : ℝ) 1) hcont ?_ dense_rat_mem_Icc isCompact_Icc ?_)
  · rintro z ⟨u, hu, rfl⟩
    exact hu
  · exact ⟨0, ⟨0, by norm_num, by norm_num⟩⟩

/-- **Joint measurability of the paper's segment test value.** -/
theorem measurable_paper_segmentTest {Z : Type*} [MeasurableSpace Z]
    {H : Z → ℝ → ℝ} (hH : Measurable fun p : Z × ℝ => H p.1 p.2)
    (hcont : ∀ z : Z, Continuous (H z)) (q : ℕ → ℚ) (j : ℕ) :
    Measurable fun p : Z × ℝ => segmentMin (H p.1) p.2 ((q j : ℚ) : ℝ) := by
  have hmeas := measurable_segmentMinRatFamily hH q j
  have heq : (fun p : Z × ℝ => segmentMin (H p.1) p.2 ((q j : ℚ) : ℝ))
      = segmentMinRatFamily H q j := by
    funext p
    exact (segmentMinRat_eq_segmentMin (hcont p.1) (x := p.2)
      (y := ((q j : ℚ) : ℝ))).symm
  rw [heq]
  exact hmeas

/-- **The paper's segment-test set is Borel.**  For a joint measurable ray
surplus continuous in the ray parameter, the set of states for which the strict
segment test against the rational code `q j` passes is Borel. -/
theorem measurableSet_paper_segmentTest {Z : Type*} [MeasurableSpace Z]
    {H : Z → ℝ → ℝ} (hH : Measurable fun p : Z × ℝ => H p.1 p.2)
    (hcont : ∀ z : Z, Continuous (H z)) (q : ℕ → ℚ) (j : ℕ) :
    MeasurableSet {p : Z × ℝ | 0 < segmentMin (H p.1) p.2 ((q j : ℚ) : ℝ)} := by
  exact (measurable_paper_segmentTest hH hcont q j) measurableSet_Ioi

/-! ## The segment test depends only on the active component -/

/-- **The segment test is positivity of the other endpoint plus component
equality.**  For a continuous surplus and an active base point, the segment
test against a code `c` passes iff `c` is active and lies in the same component
of the active set as the base point. -/
theorem segmentTest_pos_iff_component_eq {H : ℝ → ℝ} (hH : Continuous H)
    {x c : ℝ} (hx : 0 < H x) :
    0 < segmentMin H x c ↔ 0 < H c ∧
      connectedComponentIn {s : ℝ | 0 < H s} x =
        connectedComponentIn {s : ℝ | 0 < H s} c := by
  constructor
  · intro htest
    have hseg := (segmentMin_pos_iff hH).mp htest
    have hc : 0 < H c := by
      have h1 := hseg 1 (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
      simpa using h1
    exact ⟨hc, (segment_subset_iff_connectedComponentIn_eq
      (U := {s : ℝ | 0 < H s}) hx hc).mp hseg⟩
  · rintro ⟨hc, hcc⟩
    exact (segmentMin_pos_iff hH).mpr
      ((segment_subset_iff_connectedComponentIn_eq (U := {s : ℝ | 0 < H s}) hx hc).mpr hcc)

/-- **The segment test depends only on the active component.** -/
theorem segmentTest_iff_of_component_eq {H : ℝ → ℝ} (hH : Continuous H)
    {x y c : ℝ} (hx : 0 < H x) (hy : 0 < H y)
    (hxy : connectedComponentIn {s : ℝ | 0 < H s} x =
      connectedComponentIn {s : ℝ | 0 < H s} y) :
    0 < segmentMin H x c ↔ 0 < segmentMin H y c := by
  rw [segmentTest_pos_iff_component_eq hH hx,
    segmentTest_pos_iff_component_eq hH hy, hxy]

/-! ## Marker existence and the Borel least-index enumeration -/

/-- **Marker existence for the segment test.**  Every active parameter has a
rational curve code whose segment test passes: the rational code of its
component (rational density), transported by the segment-positivity criterion.
-/
theorem exists_segmentTest_of_active {Z : Type*} [MeasurableSpace Z]
    {H : Z → ℝ → ℝ} (hcont : ∀ z : Z, Continuous (H z))
    (q : ℕ → ℚ) (hq : Function.Surjective q) :
    ∀ (z : Z) (r : ℝ), 0 < H z r → ∃ j : ℕ, 0 < segmentMin (H z) r ((q j : ℚ) : ℝ) := by
  intro z r hr
  have hU : IsOpen {s : ℝ | 0 < H z s} := isOpen_lt continuous_const (hcont z)
  obtain ⟨u, hmem, hcc⟩ := exists_rat_connectedComponentIn_eq hU hr
  have hcode : 0 < H z ((u : ℚ) : ℝ) :=
    connectedComponentIn_subset {s : ℝ | 0 < H z s} r hmem
  obtain ⟨j, hj⟩ := hq u
  refine ⟨j, ?_⟩
  have hseg : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      0 < H z ((1 - t) * r + t * ((u : ℚ) : ℝ)) :=
    (segment_subset_iff_connectedComponentIn_eq (U := {s : ℝ | 0 < H z s}) hr hcode).mpr
      hcc.symm
  rw [show ((q j : ℚ) : ℝ) = ((u : ℚ) : ℝ) from by rw [hj]]
  exact (segmentMin_pos_iff (hcont z)).mpr hseg

/-- **Borel least-index component enumeration for the segment test.**  The
least index `idx z r` whose rational code passes the strict segment test is a
Borel function of `(z, r)` on the active set: all its level sets are Borel. -/
theorem exists_borel_leastIndex_segmentTest {Z : Type*} [MeasurableSpace Z]
    {H : Z → ℝ → ℝ} (hH : Measurable fun p : Z × ℝ => H p.1 p.2)
    (hcont : ∀ z : Z, Continuous (H z)) (q : ℕ → ℚ) (hq : Function.Surjective q) :
    ∃ idx : Z → ℝ → ℕ,
      (∀ (z : Z) (r : ℝ) (h : 0 < H z r),
        0 < segmentMin (H z) r ((q (idx z r) : ℚ) : ℝ) ∧
          ∀ i < idx z r, ¬ 0 < segmentMin (H z) r ((q i : ℚ) : ℝ)) ∧
      (∀ j : ℕ, MeasurableSet
        {p : Z × ℝ | 0 < H p.1 p.2 ∧ idx p.1 p.2 = j}) := by
  refine exists_borel_leastIndex_blockSpace H hH
    (fun z r j => 0 < segmentMin (H z) r ((q j : ℚ) : ℝ))
    (fun j => measurableSet_paper_segmentTest hH hcont q j) ?_
  exact exists_segmentTest_of_active hcont q hq

/-- **The block map of the least-index component enumeration is Borel.**  The
map sending an active state to its label together with its block index is
measurable: this is the measurable component enumeration of
`eq:intrinsic-active-marker`. -/
theorem measurable_blockMap_segmentTest {Z : Type*} [MeasurableSpace Z]
    {H : Z → ℝ → ℝ} (hH : Measurable fun p : Z × ℝ => H p.1 p.2)
    (hcont : ∀ z : Z, Continuous (H z)) (q : ℕ → ℚ) (hq : Function.Surjective q) :
    ∃ idx : Z → ℝ → ℕ,
      (∀ (z : Z) (r : ℝ) (h : 0 < H z r),
        0 < segmentMin (H z) r ((q (idx z r) : ℚ) : ℝ) ∧
          ∀ i < idx z r, ¬ 0 < segmentMin (H z) r ((q i : ℚ) : ℝ)) ∧
      (∀ j : ℕ, MeasurableSet
        {p : Z × ℝ | 0 < H p.1 p.2 ∧ idx p.1 p.2 = j}) ∧
      Measurable fun p : {p : Z × ℝ // 0 < H p.1 p.2} =>
        (p.1.1, idx p.1.1 p.1.2) := by
  obtain ⟨idx, hspec, hlevel⟩ := exists_borel_leastIndex_segmentTest hH hcont q hq
  exact ⟨idx, hspec, hlevel, blockMap_measurableOnPos H idx hlevel⟩

/-! ## The rational-code blocks are exactly the active components -/

/-- **Uniqueness of the least witness.**  Two labels satisfying the
minimal-witness property for the same predicate coincide. -/
theorem nat_find_witness_unique {p : ℕ → Prop} {a b : ℕ}
    (ha : p a ∧ ∀ i < a, ¬ p i) (hb : p b ∧ ∀ i < b, ¬ p i) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact absurd ha.1 (hb.2 a h)
  · exact h
  · exact absurd hb.1 (ha.2 b h)

/-- **Each least-index rational-code block is empty or an active component.**
Under the least-index specification, the set of active parameters with a fixed
label `j` is either empty or exactly the component of the active set of the
rational code `q j`.  This is the measurable form of the paper's block space
`eq:intrinsic-active-marker`: the blocks of the least-index enumeration are
literally the active components. -/
theorem segmentTest_level_empty_or_component {Z : Type*} [MeasurableSpace Z]
    {H : Z → ℝ → ℝ} (hcont : ∀ z : Z, Continuous (H z))
    (q : ℕ → ℚ) (idx : Z → ℝ → ℕ)
    (hspec : ∀ (z : Z) (r : ℝ) (h : 0 < H z r),
      0 < segmentMin (H z) r ((q (idx z r) : ℚ) : ℝ) ∧
        ∀ i < idx z r, ¬ 0 < segmentMin (H z) r ((q i : ℚ) : ℝ))
    (z : Z) (j : ℕ) :
    {s : ℝ | 0 < H z s ∧ idx z s = j} = ∅ ∨
      ∃ r : ℝ, 0 < H z r ∧
        {s : ℝ | 0 < H z s ∧ idx z s = j} =
          connectedComponentIn {s : ℝ | 0 < H z s} r := by
  classical
  by_cases hempty : {s : ℝ | 0 < H z s ∧ idx z s = j} = ∅
  · exact Or.inl hempty
  · right
    obtain ⟨r, hr⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    simp only [Set.mem_setOf_eq] at hr
    obtain ⟨hrU, hrj⟩ := hr
    refine ⟨r, hrU, ?_⟩
    ext s
    constructor
    · intro hs
      simp only [Set.mem_setOf_eq] at hs
      obtain ⟨hsU, hsj⟩ := hs
      have htest_r : 0 < segmentMin (H z) r ((q j : ℚ) : ℝ) := by
        have h := (hspec z r hrU).1
        rwa [hrj] at h
      have htest_s : 0 < segmentMin (H z) s ((q j : ℚ) : ℝ) := by
        have h := (hspec z s hsU).1
        rwa [hsj] at h
      have hccr : connectedComponentIn {t : ℝ | 0 < H z t} r =
          connectedComponentIn {t : ℝ | 0 < H z t} ((q j : ℚ) : ℝ) :=
        (segmentTest_pos_iff_component_eq (hcont z) hrU).mp htest_r |>.2
      have hccs : connectedComponentIn {t : ℝ | 0 < H z t} s =
          connectedComponentIn {t : ℝ | 0 < H z t} ((q j : ℚ) : ℝ) :=
        (segmentTest_pos_iff_component_eq (hcont z) hsU).mp htest_s |>.2
      have hcc : connectedComponentIn {t : ℝ | 0 < H z t} s =
          connectedComponentIn {t : ℝ | 0 < H z t} r := hccs.trans hccr.symm
      rw [← hcc]
      exact mem_connectedComponentIn hsU
    · intro hs
      have hsU : 0 < H z s := connectedComponentIn_subset {t : ℝ | 0 < H z t} r hs
      have hccsr : connectedComponentIn {t : ℝ | 0 < H z t} s =
          connectedComponentIn {t : ℝ | 0 < H z t} r :=
        (connectedComponentIn_eq hs).symm
      have hiff : ∀ i : ℕ, (0 < segmentMin (H z) s ((q i : ℚ) : ℝ)) ↔
          (0 < segmentMin (H z) r ((q i : ℚ) : ℝ)) :=
        fun i => segmentTest_iff_of_component_eq (hcont z) hsU hrU hccsr
      have hsp := hspec z s hsU
      have ha : (0 < segmentMin (H z) r ((q (idx z s) : ℚ) : ℝ)) ∧
          ∀ i < idx z s, ¬ 0 < segmentMin (H z) r ((q i : ℚ) : ℝ) :=
        ⟨(hiff (idx z s)).mp hsp.1, fun i hi h => hsp.2 i hi ((hiff i).mpr h)⟩
      have hb : (0 < segmentMin (H z) r ((q (idx z r) : ℚ) : ℝ)) ∧
          ∀ i < idx z r, ¬ 0 < segmentMin (H z) r ((q i : ℚ) : ℝ) :=
        hspec z r hrU
      have hmin : idx z s = idx z r := nat_find_witness_unique
        (p := fun i : ℕ => 0 < segmentMin (H z) r ((q i : ℚ) : ℝ))
        (a := idx z s) (b := idx z r) ha hb
      exact ⟨hsU, hmin.trans hrj⟩

/-! ## Obstruction to the ℕ-indexed component interface -/

/-- **A component cover forces infinitely many active components.**  Any
`IntrinsicActiveRayData` whose blocks cover the active set by genuine components
has infinitely many distinct blocks on every ray: the blocks are pairwise
disjoint and nonempty, so distinct labels give distinct components. -/
theorem infinite_range_blocks_of_isComponentCover {Z : Type*}
    {A : IntrinsicActiveRayData Z} (hA : IsComponentCover A) (z : Z) :
    (Set.range (A.block z)).Infinite := by
  have hinj : Function.Injective fun j : ℕ =>
      (⟨A.block z j, Set.mem_range_self j⟩ : Set.range (A.block z)) := by
    intro j k hjk
    have hEq : A.block z j = A.block z k := Subtype.ext_iff.mp hjk
    by_contra hne
    obtain ⟨x, hx⟩ := A.nonempty z j
    have hxk : x ∈ A.block z k := hEq ▸ hx
    exact Set.disjoint_left.mp (A.disjoint z j k hne) hx hxk
  exact infinite_coe_iff.mp (Infinite.of_injective _ hinj)

/-- **Finite active-component obstruction.**  A ray whose active set has only
finitely many components admits no component cover in the `ℕ`-indexed
`IntrinsicActiveRayData` form; the honest interface change is to allow empty
labels or to use the ℚ-indexed rational-code family of
`exists_component_cover_of_rayFlux`. -/
theorem not_isComponentCover_of_finite_activeComponents {Z : Type*}
    {A : IntrinsicActiveRayData Z} {z : Z}
    (hfin : ({s : Set ℝ | ∃ x : ℝ, 0 < A.flux z x ∧
      s = connectedComponentIn {r : ℝ | 0 < A.flux z r} x}).Finite) :
    ¬ IsComponentCover A := by
  intro hA
  have hrange : (Set.range (A.block z)).Infinite :=
    infinite_range_blocks_of_isComponentCover hA z
  have hsub : Set.range (A.block z) ⊆
      {s : Set ℝ | ∃ x : ℝ, 0 < A.flux z x ∧
        s = connectedComponentIn {r : ℝ | 0 < A.flux z r} x} := by
    rintro s ⟨j, rfl⟩
    obtain ⟨x, hx, hb⟩ := hA z j
    exact ⟨x, hx, hb⟩
  exact (not_infinite.mpr hfin) (hrange.mono hsub)

end OTSelector.Reconstruction