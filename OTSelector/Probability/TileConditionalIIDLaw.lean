import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ConditionalProbability
import OTSelector.Probability.MarkedBlockPrefixLaw
import OTSelector.Probability.InfiniteProductLaw

/-!
# The conditional iid law of tile points given the label pattern

This module formalizes the law-theoretic heart of the per-cell block comparison
`hblock` in `OTSelector.Probability.PhysicalUpperBoundAssembly`.

We fix a general measurable setting: a sample space `X`, a probability measure
`μ` on `X`, a finite label type `ι`, a measurable label map `lab : X → ι`, and
iid samples `x : Fin n → X` with law `Measure.pi (fun _ : Fin n ↦ μ)`.

The results are:

* `measurable_tileCount` / `measurableSet_tileCountSet`: the tile count
  `tileCount lab x c = #{i | lab (x i) = c}` and the count vector event
  `tileCountSet lab m` are measurable.

* Pattern algebra: `labelPatternSet`, its measurability
  (`measurableSet_labelPatternSet`), the fact that patterns are pairwise disjoint
  and cover the whole sample space (`pairwiseDisjoint_labelPatternSet`,
  `iUnion_labelPatternSet`), and the count/pattern relation
  `tileCount_eq_patternCount_of_mem`, `mem_tileCountSet_iff_exists_pattern`.

* `measure_labelPatternSet` / `restrict_labelPatternSet`: on a full label pattern
  `σ` the iid law restricts to the product of the one-coordinate restrictions
  `μ.restrict (lab ⁻¹' {σ i})`; its mass is `∏ i, μ (lab ⁻¹' {σ i})`, regrouped
  per tile in `measure_labelPatternSet_eq_prod_pow`.

* `integral_pi_tile_factor` (general finite index type): if a function depends only
  on the coordinates selected by a predicate `p`, then its integral under a product
  measure factors as the integral over the selected block times the total mass of
  the complementary block.  `integral_pi_const_smul_normalize` converts the
  un-normalized block product into the normalized one.

* `integral_labelPattern_tile_factor` / `integral_labelPattern_tile_eq`: the
  resulting factorization of a tile-local function under the pattern law.  The
  second form carries the pattern probability `μ^{⊗n}(labelPatternSet lab σ)` as
  an explicit prefactor, so dividing by it gives the conditional expectation.

* `cond_labelPattern_tile_eq` and `map_cond_labelPattern_tile`: **conditional on
  the full label pattern**, the points of tile `c` are iid with the normalized
  restriction `(μ (lab ⁻¹' {c}))⁻¹ • μ.restrict (lab ⁻¹' {c})`.  The second form is
  the measure-level statement: the conditional law of the tile-`c` block is the
  product measure.  This is the exact conditional-iid statement used by `hblock`.

* `integral_pi_two_tile_factor` (with the reindexing lemmas
  `integral_pi_subtype_q_reindex`, `pi_univ_subtype_and`) and its pattern form
  `integral_labelPattern_two_tile_factor`: distinct tiles are independent — the
  joint integral of a `c₁`-block function and a `c₂`-block function factors into
  the two block integrals and the residual mass.

* Count summation: `integral_pi_reindex_const` (reindexing a constant product
  measure), `tileEquiv` (a canonical identification `Fin (m c) ≃ tileIndex σ c`),
  `integral_labelPattern_tile_eq_fin` (the pattern-tile identity with a
  `Fin (m c)`-indexed test function), `tileCountSet_eq_iUnion_pattern` /
  `measure_tileCountSet_eq_tsum` (the count event as the disjoint union of the
  patterns with matching counts), and the main count-summed identity
  `sum_integral_labelPattern_tile_eq_countWeight`:
  summing the pattern-conditional tile integral over all patterns with a
  prescribed count vector gives `P(tileCount = m)` times the normalized tile
  expectation.

* Product normalization: `prod_restrict_prod` (a rectangle restriction of a
  product measure is the product of the restrictions),
  `norm_restrict_prod_corner` (the normalized corner is the product of the
  normalized restrictions) and `prod_label_preimage_singleton` (the product-label
  tile is the product rectangle), which instantiate the one-colour theorems on
  `X := Xs × Xt` with `lab p := (labS p.1, labT p.2)`.

* Marked-model bridge: `markedOnePointLaw`, `markedExtend`,
  `markedFixedBlockValue_eq_of_prefix` and
  `integral_markedFixedBlockValue_prefix_eq_fin` reduce the infinite-sequence
  marked block expectation to a finite product of one-point marked laws, and
  `integral_tile_markedFixedBlock_eq` shows that once the normalized physical
  tile pushes forward to the marked one-point law, the physical tile integral of
  the marked block value *is* `markedFixedBlockExpectation` at the tile counts.

The count vector `N` is recovered from the pattern: `tileCount lab x c` equals the
pattern count `patternCount σ c` on `labelPatternSet lab σ`, and the count event is
the union of the patterns with matching counts
(`mem_tileCountSet_iff_exists_pattern`).  Hence the pattern law is the sharp form of
the count-conditional law: the multinomial distribution of `N` itself is *not*
proved here (that is the separate count-law lane); only the conditional law given
the pattern and its count-summed form are identified, which is what the per-cell
block expectation uses.

## Relation to `hblock`

In `exists_physical_upper_bound_of_block_model` the per-cell input is
`∫ ξ, block n c ξ ∂P n ≤ modelBlockSum ...`.  For a physical tile block, `block n c`
reads only the source and target points whose label is `c`.

The two-colour situation reduces to the one-colour theorems above by taking
`X := X_src × X_tgt`, `μ := μ_src.prod μ_tgt`, `ι := ι_src × ι_tgt` and
`lab p := (labS p.1, labT p.2)`.  The tile `(c, c)` of this product label is
exactly the pair of the source tile `c` and the target tile `c`, so
`integral_labelPattern_tile_eq` / `cond_labelPattern_tile_eq` identify the
conditional law of the physical block with the normalized product law used to
define `markedFixedBlockExpectation`
(`markedFixedBlockExpectation_eq_seq` in
`OTSelector.Probability.MarkedBlockPrefixLaw`).  Since `block n c` depends only on
the tile-`(c,c)` coordinates, the tile-law statement is precisely what the
per-cell comparison needs; no cross-tile input enters `hblock` itself.

`sum_integral_labelPattern_tile_eq_countWeight` already performs the count
summation over the pattern partition; what remains is to identify the count weight
`P(tileCount = m)` with the binomial/multinomial weights of `N` (the separate
count-law lane) and to supply the atlas identification
`νs.map markS = markedOnePointLaw q A α` (the normalized physical tile pushes
forward to the marked one-point law) required by
`integral_tile_markedFixedBlock_eq`.  These are the only remaining inputs to the
per-cell `hblock` comparison.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

noncomputable section
namespace OTSelector.Probability

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

section Counts

variable {X : Type*} [MeasurableSpace X]
variable {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype ι] [DecidableEq ι]

/-- The number of sample coordinates whose label is `c`. -/
def tileCount {n : ℕ} (lab : X → ι) (x : Fin n → X) (c : ι) : ℕ :=
  (Finset.univ.filter fun i => lab (x i) = c).card

omit [MeasurableSpace X] [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype ι] in
/-- The count is a sum of coordinate indicators. -/
theorem tileCount_eq_sum {n : ℕ} (lab : X → ι) (x : Fin n → X) (c : ι) :
    tileCount lab x c = ∑ i : Fin n, if lab (x i) = c then 1 else 0 := by
  classical
  rw [tileCount, Finset.card_filter]

omit [Fintype ι] in
/-- The tile count is measurable. -/
theorem measurable_tileCount {n : ℕ} {lab : X → ι} (hlab : Measurable lab) (c : ι) :
    Measurable fun x : Fin n → X => tileCount lab x c := by
  classical
  have h : (fun x : Fin n → X => tileCount lab x c)
      = fun x => ∑ i : Fin n, if lab (x i) = c then (1 : ℕ) else 0 := by
    funext x
    rw [tileCount_eq_sum]
  rw [h]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact Measurable.ite (hlab.comp (measurable_pi_apply i) (measurableSet_singleton c))
    measurable_const measurable_const

/-- The event that the count vector equals a prescribed vector `m`. -/
def tileCountSet {n : ℕ} (lab : X → ι) (m : ι → ℕ) : Set (Fin n → X) :=
  {x | ∀ c, tileCount lab x c = m c}

/-- The count vector event is measurable. -/
theorem measurableSet_tileCountSet {n : ℕ} {lab : X → ι} (hlab : Measurable lab)
    (m : ι → ℕ) : MeasurableSet (tileCountSet (n := n) lab m) := by
  rw [show tileCountSet (n := n) lab m =
      ⋂ c, {x : Fin n → X | tileCount lab x c = m c} by
    ext x; simp [tileCountSet]]
  exact MeasurableSet.iInter fun c =>
    (measurable_tileCount hlab c) (measurableSet_singleton (m c))

end Counts

section Patterns

variable {X : Type*} [MeasurableSpace X]
variable {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype ι] [DecidableEq ι]

/-- The set of samples whose full label pattern is exactly `σ`. -/
def labelPatternSet {n : ℕ} (lab : X → ι) (σ : Fin n → ι) : Set (Fin n → X) :=
  {x | ∀ i, lab (x i) = σ i}

omit [MeasurableSpace X] in
/-- Membership in a pattern set. -/
theorem mem_labelPatternSet_iff {n : ℕ} {lab : X → ι} {σ : Fin n → ι} {x : Fin n → X} :
    x ∈ labelPatternSet lab σ ↔ ∀ i, lab (x i) = σ i :=
  Iff.rfl

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype ι] in
/-- A pattern set is the corresponding coordinate rectangle. -/
theorem labelPatternSet_eq_univ_pi {n : ℕ} (lab : X → ι) (σ : Fin n → ι) :
    labelPatternSet lab σ = Set.univ.pi fun i => lab ⁻¹' {σ i} := by
  ext x
  simp [labelPatternSet, Set.mem_pi]

omit [Fintype ι] in
/-- Pattern sets are measurable for a measurable label map. -/
theorem measurableSet_labelPatternSet {n : ℕ} {lab : X → ι} (hlab : Measurable lab)
    (σ : Fin n → ι) : MeasurableSet (labelPatternSet lab σ) := by
  rw [labelPatternSet_eq_univ_pi]
  exact MeasurableSet.univ_pi fun i => hlab (measurableSet_singleton (σ i))

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype ι] in
/-- Distinct patterns are disjoint. -/
theorem pairwiseDisjoint_labelPatternSet {n : ℕ} (lab : X → ι) :
    Pairwise fun (σ σ' : Fin n → ι) =>
      Disjoint (labelPatternSet lab σ) (labelPatternSet lab σ') := by
  intro σ σ' hne
  rw [Set.disjoint_left]
  intro x hx hx'
  exact hne (funext fun i => (hx i).symm.trans (hx' i))

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype ι] in
/-- Every sample has a label pattern. -/
theorem iUnion_labelPatternSet {n : ℕ} (lab : X → ι) :
    ⋃ σ : Fin n → ι, labelPatternSet lab σ = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨fun i => lab (x i), fun _ => rfl⟩

/-- The number of coordinates of a pattern `σ` carrying the label `c`. -/
def patternCount {n : ℕ} (σ : Fin n → ι) (c : ι) : ℕ :=
  (Finset.univ.filter fun i => σ i = c).card

omit [MeasurableSpace X] [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype ι] in
/-- The tile count is the pattern count on the matching pattern. -/
theorem tileCount_eq_patternCount_of_mem {n : ℕ} {lab : X → ι} {σ : Fin n → ι}
    {x : Fin n → X} (hx : x ∈ labelPatternSet lab σ) (c : ι) :
    tileCount lab x c = patternCount σ c := by
  rw [tileCount, patternCount]
  congr 1
  ext i
  rw [Finset.mem_filter, Finset.mem_filter]
  exact and_congr_right fun _ => by rw [hx i]

omit [MeasurableSpace X] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The pattern counts sum to the sample size. -/
theorem sum_patternCount {n : ℕ} (σ : Fin n → ι) : ∑ c, patternCount σ c = n := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset ι)) (f := σ) (fun i _ => Finset.mem_univ (σ i))
  simpa [patternCount, Finset.card_univ] using h.symm

omit [MeasurableSpace X] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Regrouping a product over the coordinates by the label of each coordinate. -/
theorem prod_comp_patternCount {n : ℕ} {M : Type*} [CommMonoid M]
    (σ : Fin n → ι) (f : ι → M) :
    ∏ i : Fin n, f (σ i) = ∏ c : ι, f c ^ patternCount σ c := by
  rw [← Finset.prod_fiberwise' Finset.univ σ f]
  exact Finset.prod_congr rfl fun c _ => by rw [Finset.prod_const, patternCount]

/-- **The count event is the disjoint union of the patterns with matching counts.**
This is the reduction from the count-conditional to the pattern-conditional law;
the multinomial weight of the count vector itself is not computed here. -/
theorem mem_tileCountSet_iff_exists_pattern {n : ℕ} (lab : X → ι) (m : ι → ℕ)
    (x : Fin n → X) :
    x ∈ tileCountSet lab m ↔
      ∃ σ : Fin n → ι, (∀ c, patternCount σ c = m c) ∧ x ∈ labelPatternSet lab σ := by
  constructor
  · intro hx
    refine ⟨fun i => lab (x i), ?_, fun _ => rfl⟩
    intro c
    rw [← tileCount_eq_patternCount_of_mem
      (σ := fun i => lab (x i)) (x := x) (fun _ => rfl) c]
    exact hx c
  · rintro ⟨σ, hσ, hx⟩ c
    rw [tileCount_eq_patternCount_of_mem hx, hσ c]

/-- The law of a full label pattern. -/
theorem measure_labelPatternSet {n : ℕ} (μ : Measure X) [IsProbabilityMeasure μ]
    (lab : X → ι) (σ : Fin n → ι) :
    Measure.pi (fun _ : Fin n => μ) (labelPatternSet lab σ) =
      ∏ i : Fin n, μ (lab ⁻¹' {σ i}) := by
  rw [labelPatternSet_eq_univ_pi, Measure.pi_pi]

/-- The law of a full label pattern, regrouped by tiles. -/
theorem measure_labelPatternSet_eq_prod_pow {n : ℕ} (μ : Measure X) [IsProbabilityMeasure μ]
    (lab : X → ι) (σ : Fin n → ι) :
    Measure.pi (fun _ : Fin n => μ) (labelPatternSet lab σ) =
      ∏ c : ι, (μ (lab ⁻¹' {c})) ^ patternCount σ c := by
  rw [measure_labelPatternSet]
  exact prod_comp_patternCount σ fun c => μ (lab ⁻¹' {c})

/-- Restricting the iid product law to a full label pattern gives the product of
the one-coordinate restrictions. -/
theorem restrict_labelPatternSet {n : ℕ} (μ : Measure X) [IsProbabilityMeasure μ]
    (lab : X → ι) (σ : Fin n → ι) :
    (Measure.pi (fun _ : Fin n => μ)).restrict (labelPatternSet lab σ) =
      Measure.pi (fun i : Fin n => μ.restrict (lab ⁻¹' {σ i})) := by
  rw [labelPatternSet_eq_univ_pi, Measure.restrict_pi_pi]

end Patterns

section TileFactorization

variable {X : Type*} [MeasurableSpace X]

/-- **Single-block factorization of an arbitrary product measure.** A function that
depends only on the coordinates selected by a predicate `p` integrates against the
product measure to the integral of its restriction to the selected block times the
total mass of the complementary block. -/
theorem integral_pi_tile_factor {δ : Type*} [Fintype δ]
    (ν : δ → Measure X) [∀ i, SigmaFinite (ν i)]
    (p : δ → Prop) [DecidablePred p]
    (G : ({i : δ // p i} → X) → ℝ) :
    ∫ x : δ → X, G (fun i : {i // p i} => x i.1) ∂(Measure.pi ν) =
      (∫ y : ({i // p i} → X), G y ∂(Measure.pi (fun i : {i // p i} => ν i))) *
        ((Measure.pi (fun i : {i // ¬p i} => ν i)) Set.univ).toReal := by
  have hmp : MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : δ => X) p) (Measure.pi ν)
      ((Measure.pi (fun i : {i // p i} => ν i)).prod
        (Measure.pi (fun i : {i // ¬p i} => ν i))) :=
    measurePreserving_piEquivPiSubtypeProd ν p
  have h := hmp.integral_comp'
    (fun z : ({i // p i} → X) × ({i // ¬p i} → X) => G z.1)
  simp only [MeasurableEquiv.piEquivPiSubtypeProd_apply] at h
  rw [h]
  have h1 : (∫ y : ({i // ¬p i} → X), (1 : ℝ) ∂(Measure.pi (fun i : {i // ¬p i} => ν i))) =
      ((Measure.pi (fun i : {i // ¬p i} => ν i)) Set.univ).toReal := by
    simp [Measure.real]
  rw [← h1, ← integral_prod_mul (fun y : ({i // p i} → X) => G y) (fun _ => (1 : ℝ))]
  simp

/-- Pointwise scalar multiples of a product measure. -/
theorem pi_const_smul {δ : Type*} [Fintype δ] (ρ : Measure X) [IsFiniteMeasure ρ]
    (a : ℝ≥0∞) (ha : a ≠ ∞) :
    Measure.pi (fun _ : δ => a • ρ) =
      a ^ Fintype.card δ • Measure.pi (fun _ : δ => ρ) := by
  haveI : IsFiniteMeasure (a • ρ) := Measure.smul_finite ρ ha
  refine Measure.pi_eq (μ := fun _ : δ => a • ρ) fun s hs => ?_
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/-- **Normalizing a constant product measure.** Passing from the un-normalized
`ρ^{⊗ k}` to the normalized `(ρ univ)⁻¹ • ρ` product multiplies the integral by the
`k`-th power of the total mass. -/
theorem integral_pi_const_smul_normalize {δ : Type*} [Fintype δ]
    (ρ : Measure X) [IsFiniteMeasure ρ] (hρ : ρ univ ≠ 0)
    (G : (δ → X) → ℝ) :
    ∫ y : δ → X, G y ∂(Measure.pi (fun _ : δ => ρ)) =
      (ρ univ).toReal ^ (Fintype.card δ) *
        ∫ y : δ → X, G y ∂(Measure.pi (fun _ : δ => (ρ univ)⁻¹ • ρ)) := by
  haveI : IsFiniteMeasure ((ρ univ)⁻¹ • ρ) :=
    Measure.smul_finite ρ (ENNReal.inv_ne_top.mpr hρ)
  have hρ' : (ρ univ) • ((ρ univ)⁻¹ • ρ) = ρ := by
    rw [smul_smul, ENNReal.mul_inv_cancel hρ (measure_ne_top ρ univ), one_smul]
  have hpi : Measure.pi (fun _ : δ => ρ) =
      (ρ univ) ^ Fintype.card δ • Measure.pi (fun _ : δ => (ρ univ)⁻¹ • ρ) := by
    have h2 := pi_const_smul (δ := δ) ((ρ univ)⁻¹ • ρ) (ρ univ) (measure_ne_top ρ univ)
    rwa [hρ'] at h2
  rw [hpi, integral_smul_measure, smul_eq_mul, ENNReal.toReal_pow]

/-- The total mass of a finite product measure. -/
theorem real_pi_univ_eq_prod_real {δ : Type*} [Fintype δ]
    (ν : δ → Measure X) [∀ i, IsFiniteMeasure (ν i)] :
    (Measure.pi ν).real Set.univ = ∏ i, (ν i).real Set.univ := by
  simp [Measure.real, Measure.pi_univ]

/-- The total mass of a finite product measure, as a `toReal` of the product. -/
theorem pi_univ_toReal_eq_prod {δ : Type*} [Fintype δ]
    (ν : δ → Measure X) [∀ i, IsFiniteMeasure (ν i)] :
    ((Measure.pi ν) Set.univ).toReal = ∏ i, ((ν i) Set.univ).toReal := by
  simp [Measure.pi_univ]

/-- The selected coordinate block of a label pattern. -/
abbrev tileIndex {ι : Type*} {n : ℕ} (σ : Fin n → ι) (c : ι) : Type :=
  {i : Fin n // σ i = c}

/-- The cardinality of a tile block is its pattern count. -/
theorem card_tileIndex {ι : Type*} [DecidableEq ι] {n : ℕ} (σ : Fin n → ι) (c : ι) :
    Fintype.card (tileIndex σ c) = patternCount σ c := by
  rw [Fintype.card_subtype, patternCount]

end TileFactorization

section PatternTile

variable {X : Type*} [MeasurableSpace X]
variable {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype ι] [DecidableEq ι]

/-- **The real-valued mass of a label pattern**, split into the tile-`c` block and
its complement. -/
theorem toReal_measure_labelPatternSet {n : ℕ} (μ : Measure X) [IsProbabilityMeasure μ]
    (lab : X → ι) (σ : Fin n → ι) (c : ι) :
    ((Measure.pi (fun _ : Fin n => μ)) (labelPatternSet lab σ)).toReal =
      μ.real (lab ⁻¹' {c}) ^ patternCount σ c *
        ((Measure.pi (fun i : {i : Fin n // ¬(σ i = c)} =>
          μ.restrict (lab ⁻¹' {σ i}))) Set.univ).toReal := by
  rw [measure_labelPatternSet, ENNReal.toReal_prod]
  rw [← Fintype.prod_subtype_mul_prod_subtype (p := fun i : Fin n => σ i = c)
    (f := fun i : Fin n => (μ (lab ⁻¹' {σ i})).toReal)]
  congr 1
  · rw [show (∏ i : {i : Fin n // σ i = c}, (μ (lab ⁻¹' {σ i.1})).toReal)
        = ∏ _i : {i : Fin n // σ i = c}, (μ (lab ⁻¹' {c})).toReal by
      apply Finset.prod_congr rfl
      intro i _
      rw [i.2]]
    rw [Finset.prod_const, Finset.card_univ, card_tileIndex]
    rfl
  · rw [pi_univ_toReal_eq_prod]
    simp

/-- **Tile factorization under a fixed label pattern.** A function of the tile-`c`
points integrates, under the restricted pattern law, to the integral of its
restriction against the un-normalized product of `μ.restrict (lab ⁻¹' {c})` times
the total mass of the complementary coordinates. -/
theorem integral_labelPattern_tile_factor {n : ℕ} (μ : Measure X) [IsProbabilityMeasure μ]
    (lab : X → ι) (σ : Fin n → ι) (c : ι) (G : (tileIndex σ c → X) → ℝ) :
    ∫ x : Fin n → X, G (fun i : tileIndex σ c => x i.1)
        ∂(Measure.pi (fun i : Fin n => μ.restrict (lab ⁻¹' {σ i}))) =
      (∫ y : (tileIndex σ c → X), G y
          ∂(Measure.pi (fun _ : tileIndex σ c => μ.restrict (lab ⁻¹' {c})))) *
        ((Measure.pi (fun i : {i : Fin n // ¬(σ i = c)} =>
          μ.restrict (lab ⁻¹' {σ i}))) Set.univ).toReal := by
  have h := integral_pi_tile_factor (ν := fun i : Fin n => μ.restrict (lab ⁻¹' {σ i}))
    (p := fun i => σ i = c) G
  convert h using 2
  have hfun : (fun _ : tileIndex σ c => μ.restrict (lab ⁻¹' {c}))
      = (fun i : tileIndex σ c => μ.restrict (lab ⁻¹' {σ i.1})) := by
    funext i
    rw [i.2]
  rw [hfun]

/-- **The mass form of the pattern-tile factorization.** The pattern law
factorizes into the integral of the tile function against the normalized tile
measure times the probability of the whole pattern. -/
theorem integral_labelPattern_tile_eq {n : ℕ} (μ : Measure X) [IsProbabilityMeasure μ]
    (lab : X → ι) (σ : Fin n → ι) (c : ι) (hρ : μ (lab ⁻¹' {c}) ≠ 0)
    (G : (tileIndex σ c → X) → ℝ) :
    ∫ x : Fin n → X, G (fun i : tileIndex σ c => x i.1)
        ∂(Measure.pi (fun i : Fin n => μ.restrict (lab ⁻¹' {σ i}))) =
      ((Measure.pi (fun _ : Fin n => μ)) (labelPatternSet lab σ)).toReal *
        ∫ y : (tileIndex σ c → X), G y
          ∂(Measure.pi (fun _ : tileIndex σ c =>
            (μ (lab ⁻¹' {c}))⁻¹ • μ.restrict (lab ⁻¹' {c}))) := by
  rw [integral_labelPattern_tile_factor]
  have hρ' : (μ.restrict (lab ⁻¹' {c})) Set.univ ≠ 0 := by simpa using hρ
  have hA := integral_pi_const_smul_normalize (δ := tileIndex σ c)
    (ρ := μ.restrict (lab ⁻¹' {c})) hρ' G
  rw [show (μ.restrict (lab ⁻¹' {c})) Set.univ = μ (lab ⁻¹' {c}) from by simp] at hA
  rw [toReal_measure_labelPatternSet μ lab σ c, hA, ← card_tileIndex σ c]
  simp only [Measure.real]
  ring

/-- **The conditional iid law of the tile-`c` points.**  Conditional on the full
label pattern `σ`, the tile-`c` points (read in their original index order) are
iid with the normalized restriction measure
`(μ (lab ⁻¹' {c}))⁻¹ • μ.restrict (lab ⁻¹' {c})`.  The statement is the
integral form of the law identity: it holds for every test function `G` on the
tile block, i.e. the conditional law of `fun i ↦ x i.1` is the product measure. -/
theorem cond_labelPattern_tile_eq {n : ℕ} (μ : Measure X) [IsProbabilityMeasure μ]
    (lab : X → ι) (σ : Fin n → ι) (c : ι) (hρ : μ (lab ⁻¹' {c}) ≠ 0)
    (hE : (Measure.pi (fun _ : Fin n => μ)) (labelPatternSet lab σ) ≠ 0)
    (G : (tileIndex σ c → X) → ℝ) :
    ∫ x : Fin n → X, G (fun i : tileIndex σ c => x i.1)
        ∂(ProbabilityTheory.cond (Measure.pi (fun _ : Fin n => μ)) (labelPatternSet lab σ)) =
      ∫ y : (tileIndex σ c → X), G y
        ∂(Measure.pi (fun _ : tileIndex σ c =>
          (μ (lab ⁻¹' {c}))⁻¹ • μ.restrict (lab ⁻¹' {c}))) := by
  rw [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul]
  rw [restrict_labelPatternSet, integral_labelPattern_tile_eq μ lab σ c hρ G]
  rw [ENNReal.toReal_inv]
  have hne : ((Measure.pi (fun _ : Fin n => μ)) (labelPatternSet lab σ)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hE, measure_ne_top _ _⟩
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- **Measure-level form of the conditional tile law.**  Conditional on the full
label pattern `σ`, the law of the tile-`c` block is exactly the product measure of
the normalized restriction `μ[|lab ⁻¹' {c}]`. -/
theorem map_cond_labelPattern_tile {n : ℕ} (μ : Measure X) [IsProbabilityMeasure μ]
    (lab : X → ι) (σ : Fin n → ι) (c : ι) (hρ : μ (lab ⁻¹' {c}) ≠ 0)
    (hE : (Measure.pi (fun _ : Fin n => μ)) (labelPatternSet lab σ) ≠ 0) :
    Measure.map (fun x : Fin n → X => fun i : tileIndex σ c => x i.1)
        (ProbabilityTheory.cond (Measure.pi (fun _ : Fin n => μ)) (labelPatternSet lab σ)) =
      Measure.pi (fun _ : tileIndex σ c =>
        (μ (lab ⁻¹' {c}))⁻¹ • μ.restrict (lab ⁻¹' {c})) := by
  classical
  haveI : IsFiniteMeasure ((μ (lab ⁻¹' {c}))⁻¹ • μ.restrict (lab ⁻¹' {c})) :=
    Measure.smul_finite _ (ENNReal.inv_ne_top.mpr hρ)
  have hproj : Measurable (fun x : Fin n → X => fun i : tileIndex σ c => x i.1) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply i.1
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply hproj hS]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have hG_int : ∀ ν : Measure (Fin n → X),
      (ν ((fun x : Fin n → X => fun i : tileIndex σ c => x i.1) ⁻¹' S)).toReal =
        ∫ x, (fun y : (tileIndex σ c → X) => S.indicator (fun _ => (1 : ℝ)) y)
          (fun i : tileIndex σ c => x i.1) ∂ν := by
    intro ν
    rw [show (fun x : Fin n → X =>
          (fun y : (tileIndex σ c → X) => S.indicator (fun _ => (1 : ℝ)) y)
            (fun i : tileIndex σ c => x i.1))
        = ((fun x : Fin n → X => fun i : tileIndex σ c => x i.1) ⁻¹' S).indicator
            (fun _ => (1 : ℝ)) by
      funext x
      by_cases hx : (fun i : tileIndex σ c => x i.1) ∈ S <;>
        simp [Set.indicator_apply, hx]]
    rw [integral_indicator (hproj hS)]
    simp [Measure.real]
  rw [hG_int, cond_labelPattern_tile_eq μ lab σ c hρ hE]
  rw [integral_indicator hS]
  simp [Measure.real]

end PatternTile

section TwoTile

variable {X : Type*} [MeasurableSpace X]

/-- Reindexing the `q`-block inside the complement of `p` by the `q`-block of the
whole index type. -/
theorem integral_pi_subtype_q_reindex {δ : Type*} [Fintype δ]
    (ν : δ → Measure X) [∀ i, SigmaFinite (ν i)]
    (p q : δ → Prop) [DecidablePred p] [DecidablePred q]
    (hpq : ∀ i, p i → q i → False)
    (H : ({i : δ // q i} → X) → ℝ) :
    ∫ z : ({i : {i : δ // ¬p i} // q i.1} → X),
        H (fun i : {i : δ // q i} => z ⟨⟨i.1, fun hp => hpq i.1 hp i.2⟩, i.2⟩)
        ∂(Measure.pi (fun z : {i : {i : δ // ¬p i} // q i.1} => ν z.1.1)) =
      ∫ b : ({i : δ // q i} → X), H b ∂(Measure.pi (fun i : {i : δ // q i} => ν i.1)) := by
  let e2 : {i : {i : δ // ¬p i} // q i.1} ≃ {i : δ // q i} :=
    { toFun := fun z => ⟨z.1.1, z.2⟩
      invFun := fun i => ⟨⟨i.1, fun hp => hpq i.1 hp i.2⟩, i.2⟩
      left_inv := by rintro ⟨⟨i, hi⟩, hq⟩; rfl
      right_inv := by rintro ⟨i, hq⟩; rfl }
  have hmp : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : {i : {i : δ // ¬p i} // q i.1} => X) e2.symm)
      (Measure.pi (fun i : {i : δ // q i} => ν i.1))
      (Measure.pi (fun z : {i : {i : δ // ¬p i} // q i.1} => ν z.1.1)) :=
    measurePreserving_piCongrLeft (α := fun _ : {i : {i : δ // ¬p i} // q i.1} => X)
      (fun z : {i : {i : δ // ¬p i} // q i.1} => ν z.1.1) e2.symm
  rw [← hmp.integral_comp'
    (fun z : ({i : {i : δ // ¬p i} // q i.1} → X) =>
      H (fun i : {i : δ // q i} => z ⟨⟨i.1, fun hp => hpq i.1 hp i.2⟩, i.2⟩))]
  congr 1

/-- The residual mass after removing two disjoint blocks. -/
theorem pi_univ_subtype_and {δ : Type*} [Fintype δ]
    (ν : δ → Measure X) [∀ i, SigmaFinite (ν i)]
    (p q : δ → Prop) [DecidablePred p] [DecidablePred q] :
    ((Measure.pi (fun z : {i : {i : δ // ¬p i} // ¬q i.1} => ν z.1.1)) Set.univ).toReal =
      ((Measure.pi (fun i : {i : δ // ¬p i ∧ ¬q i} => ν i.1)) Set.univ).toReal := by
  let e3 : {i : {i : δ // ¬p i} // ¬q i.1} ≃ {i : δ // ¬p i ∧ ¬q i} :=
    { toFun := fun z => ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
      invFun := fun i => ⟨⟨i.1, i.2.1⟩, i.2.2⟩
      left_inv := by rintro ⟨⟨i, hi⟩, hq⟩; rfl
      right_inv := by rintro ⟨i, ⟨hi, hq⟩⟩; rfl }
  have hmp : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : {i : {i : δ // ¬p i} // ¬q i.1} => X) e3.symm)
      (Measure.pi (fun i : {i : δ // ¬p i ∧ ¬q i} => ν i.1))
      (Measure.pi (fun z : {i : {i : δ // ¬p i} // ¬q i.1} => ν z.1.1)) :=
    measurePreserving_piCongrLeft (α := fun _ : {i : {i : δ // ¬p i} // ¬q i.1} => X)
      (fun z : {i : {i : δ // ¬p i} // ¬q i.1} => ν z.1.1) e3.symm
  have h := congrArg (fun μ : Measure ({i : {i : δ // ¬p i} // ¬q i.1} → X) =>
    (μ Set.univ).toReal) hmp.map_eq
  have hmap_univ :
      (Measure.map (MeasurableEquiv.piCongrLeft
          (fun _ : {i : {i : δ // ¬p i} // ¬q i.1} => X) e3.symm)
        (Measure.pi fun i : {i : δ // ¬p i ∧ ¬q i} => ν i.1)) Set.univ =
      (Measure.pi fun i : {i : δ // ¬p i ∧ ¬q i} => ν i.1) Set.univ := by
    rw [Measure.map_apply (MeasurableEquiv.measurable _) MeasurableSet.univ,
      Set.preimage_univ]
  rw [hmap_univ] at h
  exact h.symm

/-- **Two-block factorization: distinct tiles are independent.**  A product of a
function of the `p`-block and a function of the `q`-block integrates, under the
product measure on a finite index type, to the product of the two block integrals
times the total mass of the residual coordinates. -/
theorem integral_pi_two_tile_factor {δ : Type*} [Fintype δ]
    (ν : δ → Measure X) [∀ i, SigmaFinite (ν i)]
    (p q : δ → Prop) [DecidablePred p] [DecidablePred q]
    (hpq : ∀ i, p i → q i → False)
    (G : ({i : δ // p i} → X) → ℝ) (H : ({i : δ // q i} → X) → ℝ) :
    ∫ x : δ → X, G (fun i : {i // p i} => x i.1) * H (fun i : {i // q i} => x i.1)
        ∂(Measure.pi ν) =
      (∫ a : ({i // p i} → X), G a ∂(Measure.pi fun i : {i // p i} => ν i)) *
        (∫ b : ({i // q i} → X), H b ∂(Measure.pi fun i : {i // q i} => ν i)) *
        ((Measure.pi fun i : {i // ¬p i ∧ ¬q i} => ν i) Set.univ).toReal := by
  have hmp := measurePreserving_piEquivPiSubtypeProd (α := fun _ : δ => X) ν p
  have hkey : ∫ x : δ → X, G (fun i : {i // p i} => x i.1) * H (fun i : {i // q i} => x i.1)
      ∂(Measure.pi ν) =
      ∫ z : ({i // p i} → X) × ({i // ¬p i} → X),
        G z.1 * H (fun i : {i // q i} => z.2 ⟨i.1, fun hp => hpq i.1 hp i.2⟩)
        ∂((Measure.pi fun i : {i // p i} => ν i).prod
          (Measure.pi fun i : {i // ¬p i} => ν i)) := by
    rw [← hmp.integral_comp'
      (fun z : ({i // p i} → X) × ({i // ¬p i} → X) =>
        G z.1 * H (fun i : {i // q i} => z.2 ⟨i.1, fun hp => hpq i.1 hp i.2⟩))]
    congr 1
  rw [hkey]
  rw [integral_prod_mul (μ := Measure.pi fun i : {i // p i} => ν i)
    (ν := Measure.pi fun i : {i // ¬p i} => ν i)
    (f := fun a : ({i // p i} → X) => G a)
    (g := fun b : ({i // ¬p i} → X) =>
      H (fun i : {i // q i} => b ⟨i.1, fun hp => hpq i.1 hp i.2⟩))]
  have hsingle := integral_pi_tile_factor
    (ν := fun i : {i : δ // ¬p i} => ν i.1)
    (p := fun i : {i : δ // ¬p i} => q i.1)
    (G := fun z : ({i : {i : δ // ¬p i} // q i.1} → X) =>
      H (fun i : {i // q i} => z ⟨⟨i.1, fun hp => hpq i.1 hp i.2⟩, i.2⟩))
  simp only [] at hsingle
  rw [hsingle, integral_pi_subtype_q_reindex ν p q hpq H, pi_univ_subtype_and ν p q]
  ring

end TwoTile

section PatternTwoTile

variable {X : Type*} [MeasurableSpace X]
variable {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype ι] [DecidableEq ι]

/-- **Two-tile independence under the pattern law (un-normalized form).**  On a
fixed label pattern, a function of the `c₁`-block and a function of the `c₂`-block
have product expectation: the joint integral factors into the two block integrals
and the mass of the residual coordinates.  Dividing by the corresponding
normalization constants (`(μ (lab ⁻¹' {c})) ^ patternCount σ c`) gives the
conditional independence statement. -/
theorem integral_labelPattern_two_tile_factor {n : ℕ} (μ : Measure X)
    [IsProbabilityMeasure μ]
    (lab : X → ι) (σ : Fin n → ι) (c₁ c₂ : ι) (hne : c₁ ≠ c₂)
    (G : (tileIndex σ c₁ → X) → ℝ) (H : (tileIndex σ c₂ → X) → ℝ) :
    ∫ x in labelPatternSet lab σ,
        G (fun i : tileIndex σ c₁ => x i.1) * H (fun i : tileIndex σ c₂ => x i.1)
        ∂(Measure.pi (fun _ : Fin n => μ)) =
      (∫ a : (tileIndex σ c₁ → X), G a
          ∂(Measure.pi (fun _ : tileIndex σ c₁ => μ.restrict (lab ⁻¹' {c₁})))) *
        (∫ b : (tileIndex σ c₂ → X), H b
          ∂(Measure.pi (fun _ : tileIndex σ c₂ => μ.restrict (lab ⁻¹' {c₂})))) *
        ((Measure.pi (fun i : {i : Fin n // ¬(σ i = c₁) ∧ ¬(σ i = c₂)} =>
          μ.restrict (lab ⁻¹' {σ i}))) Set.univ).toReal := by
  rw [restrict_labelPatternSet]
  rw [integral_pi_two_tile_factor (ν := fun i : Fin n => μ.restrict (lab ⁻¹' {σ i}))
    (p := fun i => σ i = c₁) (q := fun i => σ i = c₂)
    (hpq := fun i hp hq => hne (hp.symm.trans hq)) G H]
  have h1 : (fun i : {i : Fin n // σ i = c₁} => μ.restrict (lab ⁻¹' {σ i.1}))
      = (fun _ : {i : Fin n // σ i = c₁} => μ.restrict (lab ⁻¹' {c₁})) := by
    funext i; rw [i.2]
  have h2 : (fun i : {i : Fin n // σ i = c₂} => μ.restrict (lab ⁻¹' {σ i.1}))
      = (fun _ : {i : Fin n // σ i = c₂} => μ.restrict (lab ⁻¹' {c₂})) := by
    funext i; rw [i.2]
  rw [h1, h2]

end PatternTwoTile

section ProductNormalization

variable {Xs Xt : Type*} [MeasurableSpace Xs] [MeasurableSpace Xt]

/-- Restriction of a product measure to a measurable rectangle is the product of
the restricted measures. -/
theorem prod_restrict_prod (μs : Measure Xs) [SFinite μs]
    (μt : Measure Xt) [SFinite μt] (A : Set Xs) (B : Set Xt) :
    (μs.prod μt).restrict (A ×ˢ B) = (μs.restrict A).prod (μt.restrict B) :=
  (Measure.prod_restrict (μ := μs) (ν := μt) A B).symm

/-- **Normalized corner of a product measure.**  The normalized restriction of a
product measure to a rectangle with positive mass is the product of the two
normalized restrictions. -/
theorem norm_restrict_prod_corner (μs : Measure Xs) [IsFiniteMeasure μs]
    (μt : Measure Xt) [IsFiniteMeasure μt] {A : Set Xs} {B : Set Xt}
    (hA : μs A ≠ 0) (hB : μt B ≠ 0) :
    ((μs.prod μt) (A ×ˢ B))⁻¹ • (μs.prod μt).restrict (A ×ˢ B) =
      ((μs A)⁻¹ • μs.restrict A).prod ((μt B)⁻¹ • μt.restrict B) := by
  have hAtop : μs A ≠ ∞ := measure_ne_top _ _
  have hBtop : μt B ≠ ∞ := measure_ne_top _ _
  have hAB0 : μs A * μt B ≠ 0 := mul_ne_zero hA hB
  have hABtop : μs A * μt B ≠ ∞ := ENNReal.mul_ne_top hAtop hBtop
  rw [← Measure.prod_restrict (μ := μs) (ν := μt), Measure.prod_prod A B]
  have hs : (μs A) • ((μs A)⁻¹ • μs.restrict A) = μs.restrict A := by
    rw [smul_smul, ENNReal.mul_inv_cancel hA hAtop, one_smul]
  have ht : (μt B) • ((μt B)⁻¹ • μt.restrict B) = μt.restrict B := by
    rw [smul_smul, ENNReal.mul_inv_cancel hB hBtop, one_smul]
  have hstep : ((μs A) • ((μs A)⁻¹ • μs.restrict A)).prod
        ((μt B) • ((μt B)⁻¹ • μt.restrict B))
      = (μs A * μt B) •
          (((μs A)⁻¹ • μs.restrict A).prod ((μt B)⁻¹ • μt.restrict B)) := by
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  have hfin : (μs A * μt B)⁻¹ •
      ((μs A * μt B) • (((μs A)⁻¹ • μs.restrict A).prod ((μt B)⁻¹ • μt.restrict B)))
      = ((μs A)⁻¹ • μs.restrict A).prod ((μt B)⁻¹ • μt.restrict B) := by
    rw [smul_smul, ENNReal.inv_mul_cancel hAB0 hABtop, one_smul]
  calc
    (μs A * μt B)⁻¹ • ((μs.restrict A).prod (μt.restrict B))
        = (μs A * μt B)⁻¹ •
            (((μs A) • ((μs A)⁻¹ • μs.restrict A)).prod
              ((μt B) • ((μt B)⁻¹ • μt.restrict B))) := by
          rw [hs, ht]
    _ = (μs A * μt B)⁻¹ •
            ((μs A * μt B) •
              (((μs A)⁻¹ • μs.restrict A).prod ((μt B)⁻¹ • μt.restrict B))) := by
          rw [hstep]
    _ = ((μs A)⁻¹ • μs.restrict A).prod ((μt B)⁻¹ • μt.restrict B) := hfin

/-- The tile of a product label is the rectangle of the two component tiles. -/
theorem prod_label_preimage_singleton {ιs ιt : Type*}
    (labS : Xs → ιs) (labT : Xt → ιt) (c : ιs × ιt) :
    (fun p : Xs × Xt => (labS p.1, labT p.2)) ⁻¹' {c} = (labS ⁻¹' {c.1}) ×ˢ (labT ⁻¹' {c.2}) := by
  ext p
  simp [Set.mem_preimage, Set.mem_prod, Prod.ext_iff]

end ProductNormalization

section CountSummed

variable {X : Type*} [MeasurableSpace X]
variable {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype ι] [DecidableEq ι]

/-- Reindexing a constant product measure along an equivalence of the index types. -/
theorem integral_pi_reindex_const {δ δ' : Type*} [Fintype δ] [Fintype δ']
    (e : δ ≃ δ') (ρ : Measure X) [SigmaFinite ρ] (G : (δ → X) → ℝ) :
    ∫ y : (δ' → X), G (fun i : δ => y (e i)) ∂(Measure.pi (fun _ : δ' => ρ)) =
      ∫ z : (δ → X), G z ∂(Measure.pi (fun _ : δ => ρ)) := by
  have hmp := measurePreserving_piCongrLeft (α := fun _ : δ => X)
    (μ := fun _ : δ => ρ) e.symm
  have h := hmp.integral_comp' G
  have hfun : (fun y : δ' → X =>
        (MeasurableEquiv.piCongrLeft (fun _ : δ => X) e.symm) y)
      = fun y : δ' → X => fun i : δ => y (e i) := by
    funext y i
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft',
      Equiv.piCongrLeft'_apply]
  simpa only [hfun] using h

/-- A canonical identification of `Fin (m c)` with the tile-`c` index block of a
pattern whose tile-`c` count is `m c`. -/
noncomputable def tileEquiv {n : ℕ} (σ : Fin n → ι) (c : ι) (m : ι → ℕ)
    (hσ : patternCount σ c = m c) : Fin (m c) ≃ tileIndex σ c :=
  (Fintype.equivFinOfCardEq (by rw [card_tileIndex, hσ])).symm

/-- **Pattern-tile identity with a `Fin (m c)`-indexed test function.**  This is
the form in which the tile block enters the count-summed expectation: the tile
points are read through the canonical identification `tileEquiv`. -/
theorem integral_labelPattern_tile_eq_fin {n : ℕ} (μ : Measure X) [IsProbabilityMeasure μ]
    (lab : X → ι) (σ : Fin n → ι) (c : ι) (m : ι → ℕ) (hσ : patternCount σ c = m c)
    (hρ : μ (lab ⁻¹' {c}) ≠ 0) (G : (Fin (m c) → X) → ℝ) :
    ∫ x in labelPatternSet lab σ,
        G (fun j : Fin (m c) => x ((tileEquiv σ c m hσ j).1))
        ∂(Measure.pi (fun _ : Fin n => μ)) =
      ((Measure.pi (fun _ : Fin n => μ)) (labelPatternSet lab σ)).toReal *
        ∫ y : (Fin (m c) → X), G y
          ∂(Measure.pi (fun _ : Fin (m c) =>
            (μ (lab ⁻¹' {c}))⁻¹ • μ.restrict (lab ⁻¹' {c}))) := by
  rw [restrict_labelPatternSet]
  rw [integral_labelPattern_tile_eq μ lab σ c hρ
    (fun y : tileIndex σ c → X => G (fun j : Fin (m c) => y (tileEquiv σ c m hσ j)))]
  haveI : SigmaFinite ((μ (lab ⁻¹' {c}))⁻¹ • μ.restrict (lab ⁻¹' {c})) :=
    (Measure.smul_finite _ (ENNReal.inv_ne_top.mpr hρ)).toSigmaFinite
  congr 1
  exact integral_pi_reindex_const (tileEquiv σ c m hσ) _ G

/-- The count event is the union of the patterns with the prescribed count vector. -/
theorem tileCountSet_eq_iUnion_pattern {n : ℕ} (lab : X → ι) (m : ι → ℕ) :
    tileCountSet lab m =
      ⋃ σ : {σ : Fin n → ι // ∀ c, patternCount σ c = m c}, labelPatternSet lab σ.1 := by
  ext x
  rw [mem_tileCountSet_iff_exists_pattern, Set.mem_iUnion]
  exact ⟨fun ⟨σ, hσ, hx⟩ => ⟨⟨σ, hσ⟩, hx⟩, fun ⟨σ, hx⟩ => ⟨σ.1, σ.2, hx⟩⟩

/-- The mass of the count event is the sum of the pattern masses. -/
theorem measure_tileCountSet_eq_tsum {n : ℕ} (μ : Measure X) [IsProbabilityMeasure μ]
    (lab : X → ι) (hlab : Measurable lab) (m : ι → ℕ) :
    (Measure.pi (fun _ : Fin n => μ)) (tileCountSet lab m) =
      ∑' σ : {σ : Fin n → ι // ∀ c, patternCount σ c = m c},
        (Measure.pi (fun _ : Fin n => μ)) (labelPatternSet lab σ.1) := by
  rw [tileCountSet_eq_iUnion_pattern]
  exact measure_iUnion
    (fun σ σ' hne => pairwiseDisjoint_labelPatternSet lab
      (fun h => hne (Subtype.ext h)))
    (fun σ => measurableSet_labelPatternSet hlab σ.1)

/-- **Count-summed tile identity.**  Summing the pattern-conditional tile law over
all patterns with a prescribed count vector gives the count weight times the
normalized tile expectation.  This is the "unconditional expectation over the
count event = `P(N = m)` times conditional expectation" form used by `hblock`. -/
theorem sum_integral_labelPattern_tile_eq_countWeight {n : ℕ} (μ : Measure X)
    [IsProbabilityMeasure μ]
    (lab : X → ι) (hlab : Measurable lab) (c : ι) (m : ι → ℕ)
    (hρ : μ (lab ⁻¹' {c}) ≠ 0) (G : (Fin (m c) → X) → ℝ) :
    (∑ σ : {σ : Fin n → ι // ∀ c', patternCount σ c' = m c'},
        ∫ x in labelPatternSet lab σ.1,
          G (fun j : Fin (m c) => x ((tileEquiv σ.1 c m (σ.2 c) j).1))
          ∂(Measure.pi (fun _ : Fin n => μ))) =
      ((Measure.pi (fun _ : Fin n => μ)) (tileCountSet lab m)).toReal *
        ∫ y : (Fin (m c) → X), G y
          ∂(Measure.pi (fun _ : Fin (m c) =>
            (μ (lab ⁻¹' {c}))⁻¹ • μ.restrict (lab ⁻¹' {c}))) := by
  have hterm : ∀ σ : {σ : Fin n → ι // ∀ c', patternCount σ c' = m c'},
      (∫ x in labelPatternSet lab σ.1,
        G (fun j : Fin (m c) => x ((tileEquiv σ.1 c m (σ.2 c) j).1))
        ∂(Measure.pi (fun _ : Fin n => μ))) =
      ((Measure.pi (fun _ : Fin n => μ)) (labelPatternSet lab σ.1)).toReal *
        ∫ y : (Fin (m c) → X), G y
          ∂(Measure.pi (fun _ : Fin (m c) =>
            (μ (lab ⁻¹' {c}))⁻¹ • μ.restrict (lab ⁻¹' {c}))) :=
    fun σ => integral_labelPattern_tile_eq_fin μ lab σ.1 c m (σ.2 c) hρ G
  rw [Finset.sum_congr rfl (fun σ (_ : σ ∈ Finset.univ) => hterm σ)]
  rw [← Finset.sum_mul]
  congr 1
  rw [measure_tileCountSet_eq_tsum μ lab hlab m, tsum_fintype,
    ENNReal.toReal_sum (fun σ (_ : σ ∈ Finset.univ) => measure_ne_top _ _)]

end CountSummed

section MarkedBridge

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The one-point marked law underlying `markedSeqLaw`. -/
noncomputable abbrev markedOnePointLaw (q : ℕ) (A : Type*) [MeasurableSpace A]
    (α : Measure A) : Measure ((Fin q → ℝ) × A) :=
  (cubeMeasure (Fin q) 1).prod α

/-- Extension of a finite tuple to an infinite sequence by repeating the first
entry.  Only the first `n` entries are ever used below. -/
def markedExtend {Pos : Type*} (n : ℕ) (hn : 0 < n) (p : Fin n → Pos) : ℕ → Pos :=
  fun i => if h : i < n then p ⟨i, h⟩ else p ⟨0, hn⟩

/-- The extension map is measurable. -/
theorem measurable_markedExtend {Pos : Type*} [MeasurableSpace Pos]
    (n : ℕ) (hn : 0 < n) : Measurable (markedExtend (Pos := Pos) n hn) := by
  rw [measurable_pi_iff]
  intro i
  by_cases h : i < n
  · rw [show (fun p : Fin n → Pos => markedExtend n hn p i) = fun p => p ⟨i, h⟩ by
      funext p; simp [markedExtend, h]]
    exact measurable_pi_apply (⟨i, h⟩ : Fin n)
  · rw [show (fun p : Fin n → Pos => markedExtend n hn p i) = fun p => p ⟨0, hn⟩ by
      funext p; simp [markedExtend, h]]
    exact measurable_pi_apply (⟨0, hn⟩ : Fin n)

/-- The fixed marked block value only depends on the first `a` source and the
first `b` target points. -/
theorem markedFixedBlockValue_eq_of_prefix {q : ℕ} {r t : ℝ}
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    {a b : ℕ} {ω ω' : TwoMarkedCloudSpace q A B}
    (hs : ∀ i : Fin a, ω.1.2 i.1 = ω'.1.2 i.1)
    (ht : ∀ j : Fin b, ω.2.2 j.1 = ω'.2.2 j.1) :
    markedFixedBlockValue q r t kin g a b ω = markedFixedBlockValue q r t kin g a b ω' := by
  unfold markedFixedBlockValue
  congr 1
  funext i j
  unfold markedEdgeCost mKineticCost mProbe mSourcePoint mSourceMark mTargetPoint mTargetMark
  rw [hs i, ht j]

/-- The first `n` coordinates of an infinite product have the finite product law. -/
theorem infinitePi_map_fin_prefix {Pos : Type*} [MeasurableSpace Pos] (ν : Measure Pos)
    [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map
        (fun y : ℕ → Pos => fun j : Fin n => y j) =
      Measure.pi (fun _ : Fin n => ν) := by
  exact infinitePi_map_fin ν n

/-- Measurability of the finite-prefix projection of an iid sequence. -/
theorem measurable_markedPrefix {q : ℕ} {A : Type*} [MeasurableSpace A] (a : ℕ) :
    Measurable fun z : ℕ → (Fin q → ℝ) × A => fun i : Fin a => z i := by
  rw [measurable_pi_iff]
  exact fun i => measurable_pi_apply i.1

/-- **Finite-prefix form of the fixed marked block integral.**  The block value
only reads the first `a` source and `b` target entries, so its integral against the
two infinite iid sequence laws is an integral against the finite products of the
one-point marked laws. -/
theorem integral_markedFixedBlockValue_prefix_eq_fin {q : ℕ} {r t : ℝ}
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ∫ z : (ℕ → (Fin q → ℝ) × A) × (ℕ → (Fin q → ℝ) × B),
        markedFixedBlockValue q r t kin g a b ((0, z.1), (0, z.2))
        ∂((markedSeqLaw q A α).prod (markedSeqLaw q B β))
      = ∫ p : ((Fin a → (Fin q → ℝ) × A) × (Fin b → (Fin q → ℝ) × B)),
          markedFixedBlockValue q r t kin g a b
            ((0, markedExtend a ha p.1), (0, markedExtend b hb p.2))
          ∂((Measure.pi (fun _ : Fin a => markedOnePointLaw q A α)).prod
            (Measure.pi (fun _ : Fin b => markedOnePointLaw q B β))) := by
  classical
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  let proj : (ℕ → (Fin q → ℝ) × A) × (ℕ → (Fin q → ℝ) × B) →
      ((Fin a → (Fin q → ℝ) × A) × (Fin b → (Fin q → ℝ) × B)) :=
    fun z => (fun i : Fin a => z.1 i, fun j : Fin b => z.2 j)
  have hproj : Measurable proj :=
    ((measurable_markedPrefix (A := A) (q := q) a).comp measurable_fst).prodMk
      ((measurable_markedPrefix (A := B) (q := q) b).comp measurable_snd)
  have hmap : Measure.map proj ((markedSeqLaw q A α).prod (markedSeqLaw q B β)) =
      (Measure.pi (fun _ : Fin a => markedOnePointLaw q A α)).prod
        (Measure.pi (fun _ : Fin b => markedOnePointLaw q B β)) := by
    rw [show proj = Prod.map
        (fun z : ℕ → (Fin q → ℝ) × A => fun i : Fin a => z i)
        (fun z : ℕ → (Fin q → ℝ) × B => fun j : Fin b => z j) from rfl,
      ← Measure.map_prod_map _ _ (measurable_markedPrefix (A := A) (q := q) a)
        (measurable_markedPrefix (A := B) (q := q) b)]
    congr 1
    · rw [markedSeqLaw]
      exact infinitePi_map_fin_prefix (markedOnePointLaw q A α) a
    · rw [markedSeqLaw]
      exact infinitePi_map_fin_prefix (markedOnePointLaw q B β) b
  rw [← hmap]
  rw [integral_map hproj.aemeasurable]
  · apply integral_congr_ae
    filter_upwards with z
    symm
    apply markedFixedBlockValue_eq_of_prefix
    · intro i
      simp [markedExtend, proj, i.2]
    · intro j
      simp [markedExtend, proj, j.2]
  · have hΨ : Measurable (fun p :
        ((Fin a → (Fin q → ℝ) × A) × (Fin b → (Fin q → ℝ) × B)) =>
        ((0, markedExtend a ha p.1), (0, markedExtend b hb p.2)) :
        _ → TwoMarkedCloudSpace q A B) :=
      (measurable_const.prodMk ((measurable_markedExtend a ha).comp measurable_fst)).prodMk
        (measurable_const.prodMk ((measurable_markedExtend b hb).comp measurable_snd))
    exact ((measurable_markedFixedBlockValue q r t hkin hg a b).comp hΨ).aestronglyMeasurable

/-- **Bridge to the marked model.**  Suppose the normalized source and target tile
laws push forward under the one-point marking maps to the marked one-point laws
`(cubeMeasure (Fin q) 1).prod α` and `(cubeMeasure (Fin q) 1).prod β`.  Then the
integral of the marked block value over the physical tile block is exactly the
marked fixed-block expectation at the tile counts `a`, `b`.

This is the exact interface between the conditional tile law proved above and
`markedFixedBlockExpectation`; the remaining input is the atlas identification
`νs.map markS = markedOnePointLaw q A α` (and its target analogue), i.e. that the
normalized physical tile pushes forward to the marked model's one-point law. -/
theorem integral_tile_markedFixedBlock_eq {q : ℕ} {r t : ℝ}
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (R : ℝ≥0) {Xs Yt : Type*} [MeasurableSpace Xs] [MeasurableSpace Yt]
    (νs : Measure Xs) [IsProbabilityMeasure νs]
    (νt : Measure Yt) [IsProbabilityMeasure νt]
    (markS : Xs → (Fin q → ℝ) × A) (hmarkS : Measurable markS)
    (markT : Yt → (Fin q → ℝ) × B) (hmarkT : Measurable markT)
    (hα : νs.map markS = markedOnePointLaw q A α)
    (hβ : νt.map markT = markedOnePointLaw q B β)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ∫ p : (Fin a → Xs) × (Fin b → Yt),
        markedFixedBlockValue q r t kin g a b
          ((0, markedExtend a ha (fun i => markS (p.1 i))),
           (0, markedExtend b hb (fun j => markT (p.2 j))))
        ∂((Measure.pi (fun _ : Fin a => νs)).prod (Measure.pi (fun _ : Fin b => νt)))
      = markedFixedBlockExpectation q r t kin g α β R a b := by
  classical
  rw [markedFixedBlockExpectation_eq_seq q r t hkin hg α β R a b]
  rw [integral_markedFixedBlockValue_prefix_eq_fin hkin hg α β a b ha hb]
  let Φ : (Fin a → Xs) × (Fin b → Yt) →
      ((Fin a → (Fin q → ℝ) × A) × (Fin b → (Fin q → ℝ) × B)) :=
    fun p => (fun i => markS (p.1 i), fun j => markT (p.2 j))
  have hSA : Measurable (fun z : Fin a → Xs => fun i : Fin a => markS (z i)) :=
    measurable_pi_iff.mpr fun i => hmarkS.comp (measurable_pi_apply i)
  have hTA : Measurable (fun z : Fin b → Yt => fun j : Fin b => markT (z j)) :=
    measurable_pi_iff.mpr fun j => hmarkT.comp (measurable_pi_apply j)
  have hΦ : Measurable Φ := (hSA.comp measurable_fst).prodMk (hTA.comp measurable_snd)
  have hmap : Measure.map Φ
        ((Measure.pi (fun _ : Fin a => νs)).prod (Measure.pi (fun _ : Fin b => νt))) =
      (Measure.pi (fun _ : Fin a => markedOnePointLaw q A α)).prod
        (Measure.pi (fun _ : Fin b => markedOnePointLaw q B β)) := by
    rw [show Φ = Prod.map (fun z : Fin a → Xs => fun i => markS (z i))
        (fun z : Fin b → Yt => fun j => markT (z j)) from rfl,
      ← Measure.map_prod_map _ _ hSA hTA]
    congr 1
    · rw [Measure.pi_map_pi (fun _ => hmarkS.aemeasurable), hα]
    · rw [Measure.pi_map_pi (fun _ => hmarkT.aemeasurable), hβ]
  rw [← hmap]
  rw [integral_map hΦ.aemeasurable]
  · have hΨ : Measurable (fun q' :
        ((Fin a → (Fin q → ℝ) × A) × (Fin b → (Fin q → ℝ) × B)) =>
        ((0, markedExtend a ha q'.1), (0, markedExtend b hb q'.2)) :
        _ → TwoMarkedCloudSpace q A B) :=
      (measurable_const.prodMk ((measurable_markedExtend a ha).comp measurable_fst)).prodMk
        (measurable_const.prodMk ((measurable_markedExtend b hb).comp measurable_snd))
    exact ((measurable_markedFixedBlockValue q r t hkin hg a b).comp hΨ).aestronglyMeasurable

end MarkedBridge

end OTSelector.Probability
