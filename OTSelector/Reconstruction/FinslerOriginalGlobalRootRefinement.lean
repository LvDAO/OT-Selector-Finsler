import OTSelector.Reconstruction.FinslerOriginalRefinementRootCover
import OTSelector.Reconstruction.FinslerOriginalGlobalRefinedAtlas

/-!
# Global producer map and root-piece refinement

This file closes the producer gap stated at the end of
`FinslerOriginalRefinementRootCover.lean`.

## (1) The per-parent producer map

`ParentChartProducer` packages the per-parent chart data needed to run the
level-seed constructor on the concentric compact cores of the parent core:
the chart datum, the compact parent core inside the open chart domain, the
parent seed patch realizing the parent window's seed, and the linear
identification of the parent label space with the chart label space.

`exists_parentRefinedFamily_withCurves` runs the constructor
`exists_levelSeedPatch_of_chartData` on the cores `parentCore j ∩ closedBall (σ 0) i`
for every parent `j`, producing a coherent refined family (patch, label
identification, label equation, curve equation) in one pass.  The label cover
`refinedLabels_cover_of_labels` is elementary from the label equation (no
circularity).  `refinedReferenceRoots_subset_parent` and the imported
`parentReferenceRoots_subset_union_refined` give, for a matched pair of label
reference laws, that the refined reference-root sets are *both* contained in and
covering the parent reference-root set.

## (2) Block and global root-piece partitions

The refined child family of one parent is disjointified inside the parent piece
(`refinedBlockPiece`), giving per parent:

* `pairwiseDisjoint_refinedBlockPiece`;
* `iUnion_refinedBlockPiece`: the parent piece is the union of its child pieces;
* `existsUnique_refinedBlockPiece`: exact-one-window form (C(b)) per parent;
* `refinedBlockPiece_restrict_eq_sum`: the lambda-level C(a) restriction sum
  over the child pieces.

The global family is indexed by `Nat.pair` (`globalRefinedRootPiece`,
`globalRefinedParent`), and the same four statements hold globally
(`pairwiseDisjoint_globalRefinedRootPiece`, `iUnion_globalRefinedRootPiece`,
`existsUnique_globalRefinedRootPiece`,
`globalRefinedRootPiece_restrict_eq_sum`).

## (3) Assembly

`globalRootPieceRefinement_of_chartProducer` combines the two layers into the
strongest true form of the `RootPieceRefinement` conclusion at the reference-root
level: cover and subset of each parent reference-root set, pairwise disjointness of
the global refined pieces, block cover and the global exact-one-window form, the
per-parent and global lambda-level restriction sums.

## Remaining producer inputs (exact)

1. **The producer map itself is not derivable from the global atlas.**  The atlas
   `exists_global_refinedBallCore_atlas` exposes only the window family; the
   chart datum, parent core and parent label/curve realization per window are not
   recoverable from it.  `ParentChartProducer` is the precise interface a
   producer must supply.
2. **A parent-major *monotone* enumeration of the global family is impossible
   with infinitely many children per parent.**  Every parent has countably many
   refined children, and a strictly parent-major enumeration has order type
   `ω · ω`, which has no order embedding into `ω` (elements of the second block
   have infinitely many predecessors).  This is why the global family is stated
   in block form (`globalRefinedParent`) carrying no `parent_mono` field; the
   block/global forms above are the order-free replacement of
   `RootPieceRefinement`.  If the consumer insists on `parent_mono`, the
   producer must additionally choose *finitely many* witnesses per parent.
3. **Label reference laws must be matched per parent.**  The hypothesis
   `hlabref` in the assembly theorem is the one genuinely new producer field
   (equality of the two pushed label reference laws); the constructive route from
   the chart data to it (transporting `κ` along the linear identifications) is
   not formalized here.
4. The sums are taken with restricted measures on the union of the parent pieces
   `⋃ j, disjointed S j`; extending to all of `Z` needs the normalization law
   (`ae_existsUnique_populationSeedRootPiece`), which is available when the
   conditional window law is instantiated.
-/
open Set Function MeasureTheory Manifold OTSelector.Geometry
open Metric
open scoped Topology ContDiff ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## (1) The per-parent producer map -/

/-- **The per-parent producer map.**  For every parent window index `j` it supplies
the chart datum, the compact parent core inside the open chart domain, the parent
seed patch realizing the parent window's seed, and the linear identification of the
parent label space with the chart label space. -/
structure ParentChartProducer (F : ContinuousFinslerNorm E M) (u : M → ℝ)
    (P : ℕ → F.CalibratedSeedWindow u) where
  chartData : (j : ℕ) → CoreSectionChartData F u
  parentCore : (j : ℕ) → Set E
  parentCore_compact : ∀ j, IsCompact (parentCore j)
  parentCore_subset : ∀ j, parentCore j ⊆ (chartData j).U
  parentCore_center : ∀ j, (chartData j).σ 0 ∈ parentCore j
  parentPatch : (j : ℕ) → F.CalibratedLevelSeedPatch u
  parentEquiv : (j : ℕ) → (parentPatch j).covector.ker ≃L[ℝ] (chartData j).p.ker
  parent_labels : ∀ j, (parentPatch j).labels =
    (parentEquiv j) ⁻¹' ((chartData j).V ∩ (chartData j).σ ⁻¹' (parentCore j))
  parent_curves : ∀ j (w : (parentPatch j).covector.ker) (t : ℝ),
    (parentPatch j).curve w t = (chartData j).Γ ((chartData j).σ ((parentEquiv j) w)) t
  seed_eq : ∀ j, (P j).seed = parentPatch j

/-- **The refined family of one parent, with curve equations.**  Running the level
seed constructor on the concentric cores `parentCore j ∩ closedBall (σ 0) i` gives
patches whose labels are the preimage of the concentric core data and whose curves
run through the same chart datum. -/
theorem exists_parentRefinedFamily_withCurves
    {P : ℕ → F.CalibratedSeedWindow u} (Q : ParentChartProducer F u P)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (j : ℕ) :
    ∃ (A : ℕ → F.CalibratedLevelSeedPatch u)
      (e : ∀ i, (A i).covector.ker ≃L[ℝ] (Q.chartData j).p.ker),
      (∀ i, (A i).labels = (e i) ⁻¹'
        ((Q.chartData j).V ∩ (Q.chartData j).σ ⁻¹'
          (Q.parentCore j ∩ closedBall ((Q.chartData j).σ 0) (i : ℝ)))) ∧
      (∀ i (w : (A i).covector.ker) (t : ℝ),
        (A i).curve w t = (Q.chartData j).Γ ((Q.chartData j).σ ((e i) w)) t) := by
  let C := Q.chartData j
  let K := Q.parentCore j
  have hKi : ∀ i : ℕ, IsCompact (K ∩ closedBall (C.σ 0) (i : ℝ)) := fun i =>
    (Q.parentCore_compact j).inter (ProperSpace.isCompact_closedBall (C.σ 0) (i : ℝ))
  have hKU : ∀ i : ℕ, K ∩ closedBall (C.σ 0) (i : ℝ) ⊆ C.U := fun i =>
    inter_subset_left.trans (Q.parentCore_subset j)
  have hKc : ∀ i : ℕ, C.σ 0 ∈ K ∩ closedBall (C.σ 0) (i : ℝ) := fun i =>
    ⟨Q.parentCore_center j, mem_closedBall_self (by positivity)⟩
  choose A e hprops using fun i =>
    exists_levelSeedPatch_of_chartData hF hcomplete hu C (hKi i) (hKU i) (hKc i)
  exact ⟨A, e, fun i => (hprops i).2.1, fun i => (hprops i).2.2.1⟩

/-- **The label cover of a parent core by the refined labels.**  Elementary from the
label equation: every parent label is a refined label after the linear
identification, because the concentric refined cores cover the parent core. -/
theorem refinedLabels_cover_of_labels
    (C : CoreSectionChartData F u) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ C.U) (hKcenter : C.σ 0 ∈ K)
    (A : ℕ → F.CalibratedLevelSeedPatch u)
    (e : ∀ i, (A i).covector.ker ≃L[ℝ] C.p.ker)
    (hAlab : ∀ i, (A i).labels =
      (e i) ⁻¹' (C.V ∩ C.σ ⁻¹' (K ∩ closedBall (C.σ 0) (i : ℝ)))) :
    C.V ∩ C.σ ⁻¹' K ⊆ ⋃ i, (e i) '' ((A i).labels) := by
  intro w hw
  obtain ⟨i, hi⟩ : ∃ i : ℕ, dist (C.σ w) (C.σ 0) < (i : ℝ) := exists_nat_gt _
  have hmemKi : w ∈ C.V ∩ C.σ ⁻¹' (K ∩ closedBall (C.σ 0) (i : ℝ)) :=
    ⟨hw.1, hw.2, mem_closedBall.mpr (le_of_lt hi)⟩
  have hx : (e i).symm w ∈ (A i).labels := by
    rw [hAlab i]
    show (e i) ((e i).symm w) ∈ C.V ∩ C.σ ⁻¹' (K ∩ closedBall (C.σ 0) (i : ℝ))
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hmemKi
  have heq : (e i) ((e i).symm w) = w := ContinuousLinearEquiv.apply_symm_apply (e i) w
  exact mem_iUnion.mpr ⟨i, heq ▸ mem_image_of_mem (e i) hx⟩

/-- **Refined reference roots are parent reference roots** when the pushed label
reference laws agree. -/
theorem refinedReferenceRoots_subset_parent
    (S0 : F.CalibratedLevelSeedPatch u) (a : M → Z)
    (κ0 : Measure S0.covector.ker) (lambda : Measure Z)
    (S : F.CalibratedLevelSeedPatch u) (κ : Measure S.covector.ker)
    (hdom : populationSeedRootDomain S a ⊆ populationSeedRootDomain S0 a)
    (hlabref : populationSeedLabelReference S a κ =
      populationSeedLabelReference S0 a κ0) :
    populationSeedReferenceRoots S a κ lambda ⊆
      populationSeedReferenceRoots S0 a κ0 lambda := by
  intro z hz
  obtain ⟨h1, h2, h3⟩ := hz
  exact ⟨hdom h1, by simpa only [hlabref] using h2,
    by simpa only [hlabref] using h3⟩

/-- The parent reference-root sets of a producer map. -/
def parentRefRootSets {P : ℕ → F.CalibratedSeedWindow u}
    (Q : ParentChartProducer F u P) (a : M → Z)
    (κ0 : ∀ j, Measure (Q.parentPatch j).covector.ker) (lambda : Measure Z) :
    ℕ → Set Z :=
  fun j => populationSeedReferenceRoots (Q.parentPatch j) a (κ0 j) lambda

/-- The refined reference-root sets of a refined patch family. -/
def refinedRefRootSets (A : ℕ → ℕ → F.CalibratedLevelSeedPatch u) (a : M → Z)
    (κ : ∀ j i, Measure (A j i).covector.ker) (lambda : Measure Z) :
    ℕ → ℕ → Set Z :=
  fun j i => populationSeedReferenceRoots (A j i) a (κ j i) lambda

/-! ## (2) Block and global root-piece partitions -/

/-- **A refined block piece**: the disjointified child root set of `(j, i)` inside
the parent root piece of `j`. -/
def refinedBlockPiece (S : ℕ → Set Z) (R : ℕ → ℕ → Set Z) (j i : ℕ) : Set Z :=
  disjointed (R j) i ∩ disjointed S j

/-- Parent index of a global refined index. -/
def globalRefinedParent (n : ℕ) : ℕ := (Nat.unpair n).1

/-- Child index of a global refined index. -/
def globalRefinedChild (n : ℕ) : ℕ := (Nat.unpair n).2

/-- **The global refined root piece** at `Nat.pair` index. -/
def globalRefinedRootPiece (S : ℕ → Set Z) (R : ℕ → ℕ → Set Z) (n : ℕ) : Set Z :=
  refinedBlockPiece S R (globalRefinedParent n) (globalRefinedChild n)

theorem refinedBlockPiece_subset_parentPiece
    (S : ℕ → Set Z) (R : ℕ → ℕ → Set Z) (j i : ℕ) :
    refinedBlockPiece S R j i ⊆ disjointed S j :=
  inter_subset_right

/-- **Distinct refined block pieces are disjoint.** -/
theorem pairwiseDisjoint_refinedBlockPiece (S : ℕ → Set Z) (R : ℕ → ℕ → Set Z) :
    Pairwise (Function.onFun Disjoint (fun p : ℕ × ℕ => refinedBlockPiece S R p.1 p.2)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ hne
  show Disjoint (refinedBlockPiece S R a b) (refinedBlockPiece S R c d)
  by_cases hac : a = c
  · subst hac
    have hbd : b ≠ d := fun h => hne (by simp [h])
    exact (disjoint_disjointed (R a) hbd).mono inter_subset_left inter_subset_left
  · exact (disjoint_disjointed S hac).mono
      (refinedBlockPiece_subset_parentPiece S R a b)
      (refinedBlockPiece_subset_parentPiece S R c d)

/-- **Block cover:** the union of the child pieces of `j` is the parent piece. -/
theorem iUnion_refinedBlockPiece (S : ℕ → Set Z) (R : ℕ → ℕ → Set Z)
    (hcover : ∀ j, S j ⊆ ⋃ i, R j i) (j : ℕ) :
    (⋃ i, refinedBlockPiece S R j i) = disjointed S j := by
  refine Subset.antisymm ?_ ?_
  · exact iUnion_subset fun i => refinedBlockPiece_subset_parentPiece S R j i
  · intro z hz
    have hzS : z ∈ S j := disjointed_subset S j hz
    obtain ⟨i0, hi0⟩ := mem_iUnion.mp (hcover j hzS)
    have hzd : z ∈ ⋃ i, disjointed (R j) i := by
      rw [iUnion_disjointed]
      exact mem_iUnion.mpr ⟨i0, hi0⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hzd
    exact mem_iUnion.mpr ⟨i, hi, hz⟩

/-- **C(b) exactly-one-window form per parent.**  Every point of a parent piece
belongs to exactly one child piece of that parent. -/
theorem existsUnique_refinedBlockPiece (S : ℕ → Set Z) (R : ℕ → ℕ → Set Z)
    (hcover : ∀ j, S j ⊆ ⋃ i, R j i) {j : ℕ} {z : Z}
    (hz : z ∈ disjointed S j) :
    ∃! i, z ∈ refinedBlockPiece S R j i := by
  have hzu : z ∈ ⋃ i, refinedBlockPiece S R j i := by
    rw [iUnion_refinedBlockPiece S R hcover j]
    exact hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp hzu
  refine ⟨i, hi, ?_⟩
  intro i' hi'
  by_contra hne
  exact (Set.disjoint_left.mp (disjoint_disjointed (R j) hne) hi'.1) hi.1

/-- **The lambda-level C(a) restriction sum over child pieces.** -/
theorem refinedBlockPiece_restrict_eq_sum (S : ℕ → Set Z) (R : ℕ → ℕ → Set Z)
    (lambda : Measure Z) (hcover : ∀ j, S j ⊆ ⋃ i, R j i)
    (hmeasS : ∀ j, MeasurableSet (S j)) (hmeasR : ∀ j i, MeasurableSet (R j i))
    (j : ℕ) :
    lambda.restrict (disjointed S j) =
      Measure.sum (fun i => lambda.restrict (refinedBlockPiece S R j i)) := by
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun i => refinedBlockPiece S R j i)) := by
    intro i i' hne
    have hpairne : (j, i) ≠ (j, i') := fun h => hne (Prod.mk.inj h).2
    show Disjoint (refinedBlockPiece S R j i) (refinedBlockPiece S R j i')
    exact pairwiseDisjoint_refinedBlockPiece S R hpairne
  have hmeas : ∀ i, MeasurableSet (refinedBlockPiece S R j i) := fun i =>
    (MeasurableSet.disjointed (hmeasR j) i).inter (MeasurableSet.disjointed hmeasS j)
  rw [← iUnion_refinedBlockPiece S R hcover j]
  rw [Measure.restrict_iUnion hdisj hmeas]

/-! ## (3) Global family -/

theorem pairwiseDisjoint_globalRefinedRootPiece (S : ℕ → Set Z) (R : ℕ → ℕ → Set Z) :
    Pairwise (Function.onFun Disjoint (globalRefinedRootPiece S R)) := by
  intro n m hne
  apply pairwiseDisjoint_refinedBlockPiece S R
  intro h
  exact hne (by
    rw [← Nat.pair_unpair n, ← Nat.pair_unpair m]
    exact congrArg (fun p : ℕ × ℕ => Nat.pair p.1 p.2) h)

theorem iUnion_globalRefinedRootPiece (S : ℕ → Set Z) (R : ℕ → ℕ → Set Z)
    (hcover : ∀ j, S j ⊆ ⋃ i, R j i) :
    (⋃ n, globalRefinedRootPiece S R n) = ⋃ j, disjointed S j := by
  ext z
  constructor
  · intro hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨globalRefinedParent n,
      refinedBlockPiece_subset_parentPiece S R (globalRefinedParent n)
        (globalRefinedChild n) hn⟩
  · intro hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    have hzu : z ∈ ⋃ i, refinedBlockPiece S R j i := by
      rw [iUnion_refinedBlockPiece S R hcover j]
      exact hj
    obtain ⟨i, hi⟩ := mem_iUnion.mp hzu
    refine mem_iUnion.mpr ⟨Nat.pair j i, ?_⟩
    simpa [globalRefinedRootPiece, globalRefinedParent, globalRefinedChild,
      Nat.unpair_pair] using hi

theorem existsUnique_globalRefinedRootPiece (S : ℕ → Set Z) (R : ℕ → ℕ → Set Z)
    (hcover : ∀ j, S j ⊆ ⋃ i, R j i) {j : ℕ} {z : Z}
    (hz : z ∈ disjointed S j) :
    ∃! n, globalRefinedParent n = j ∧ z ∈ globalRefinedRootPiece S R n := by
  obtain ⟨i, hi, huniq⟩ := existsUnique_refinedBlockPiece S R hcover hz
  refine ⟨Nat.pair j i, ⟨?_, ?_⟩, ?_⟩
  · simp only [globalRefinedParent, Nat.unpair_pair]
  · simpa [globalRefinedRootPiece, globalRefinedParent, globalRefinedChild,
      Nat.unpair_pair] using hi
  · rintro n ⟨hnparent, hzn⟩
    have hchild : z ∈ refinedBlockPiece S R j (globalRefinedChild n) := by
      simpa [globalRefinedRootPiece, hnparent] using hzn
    have hci : globalRefinedChild n = i := huniq _ hchild
    have hn1 : (Nat.unpair n).1 = j := hnparent
    have hn2 : (Nat.unpair n).2 = i := hci
    calc n = Nat.pair (Nat.unpair n).1 (Nat.unpair n).2 := (Nat.pair_unpair n).symm
      _ = Nat.pair j i := by rw [hn1, hn2]

theorem globalRefinedRootPiece_restrict_eq_sum (S : ℕ → Set Z) (R : ℕ → ℕ → Set Z)
    (lambda : Measure Z) (hcover : ∀ j, S j ⊆ ⋃ i, R j i)
    (hmeasS : ∀ j, MeasurableSet (S j)) (hmeasR : ∀ j i, MeasurableSet (R j i)) :
    lambda.restrict (⋃ j, disjointed S j) =
      Measure.sum (fun n => lambda.restrict (globalRefinedRootPiece S R n)) := by
  have hdisj : Pairwise (Function.onFun Disjoint (globalRefinedRootPiece S R)) :=
    pairwiseDisjoint_globalRefinedRootPiece S R
  have hmeas : ∀ n, MeasurableSet (globalRefinedRootPiece S R n) := fun n =>
    (MeasurableSet.disjointed (hmeasR (globalRefinedParent n))
      (globalRefinedChild n)).inter
      (MeasurableSet.disjointed hmeasS (globalRefinedParent n))
  rw [← iUnion_globalRefinedRootPiece S R hcover]
  rw [Measure.restrict_iUnion hdisj hmeas]


/-! ## (3) Assembly -/

/-- **Global root-piece refinement and its C(a)/C(b) consequences.**  Given the
per-parent producer map, a coherent refined patch family (labels and curves through
the parent chart datum), matched label reference laws, and measurability of the root
sets, the parent reference-root family and the refined reference-root family
satisfy the block/global forms of the root-piece refinement: cover and subset of
each parent, pairwise disjointness of the global refined pieces, block cover and
the global C(b) exactly-one-window form, the per-parent lambda-level C(a)
restriction sum, and the global lambda-level restriction sum. -/
theorem rootPieceRefinement_of_chartProducer
    {P : ℕ → F.CalibratedSeedWindow u} (Q : ParentChartProducer F u P)
    (A : ℕ → ℕ → F.CalibratedLevelSeedPatch u)
    (e : ∀ j i, (A j i).covector.ker ≃L[ℝ] (Q.chartData j).p.ker)
    (hAlab : ∀ j i, (A j i).labels = (e j i) ⁻¹'
      ((Q.chartData j).V ∩ (Q.chartData j).σ ⁻¹'
        (Q.parentCore j ∩ closedBall ((Q.chartData j).σ 0) (i : ℝ))))
    (hAcur : ∀ j i (w : (A j i).covector.ker) (t : ℝ),
      (A j i).curve w t = (Q.chartData j).Γ ((Q.chartData j).σ ((e j i) w)) t)
    (a : M → Z) (κ0 : ∀ j, Measure (Q.parentPatch j).covector.ker)
    (κ : ∀ j i, Measure (A j i).covector.ker) (lambda : Measure Z)
    (hlabref : ∀ j i, populationSeedLabelReference (A j i) a (κ j i) =
      populationSeedLabelReference (Q.parentPatch j) a (κ0 j))
    (hmeasS : ∀ j, MeasurableSet (parentRefRootSets Q a κ0 lambda j))
    (hmeasR : ∀ j i, MeasurableSet (refinedRefRootSets A a κ lambda j i)) :
    let S := parentRefRootSets Q a κ0 lambda
    let R := refinedRefRootSets A a κ lambda
    (∀ j, S j ⊆ ⋃ i, R j i) ∧
    (∀ j i, R j i ⊆ S j) ∧
    Pairwise (Function.onFun Disjoint (globalRefinedRootPiece S R)) ∧
    (∀ j, disjointed S j ⊆
      ⋃ n ∈ {n | globalRefinedParent n = j}, globalRefinedRootPiece S R n) ∧
    (∀ j z, z ∈ disjointed S j →
      ∃! n, globalRefinedParent n = j ∧ z ∈ globalRefinedRootPiece S R n) ∧
    (∀ j, lambda.restrict (disjointed S j) =
      Measure.sum (fun i => lambda.restrict (refinedBlockPiece S R j i))) ∧
    (lambda.restrict (⋃ j, disjointed S j) =
      Measure.sum (fun n => lambda.restrict (globalRefinedRootPiece S R n))) := by
  dsimp only
  have hcov : ∀ j, parentRefRootSets Q a κ0 lambda j ⊆
      ⋃ i, refinedRefRootSets A a κ lambda j i := by
    intro j
    exact parentReferenceRoots_subset_union_refined (Q.parentPatch j) a (κ0 j) lambda
      (A j) (κ j)
      (parentRootDomain_subset_union_refined (Q.chartData j) (Q.parentPatch j)
        (Q.parentEquiv j) (Q.parent_labels j) (Q.parent_curves j) (A j) (e j)
        (hAlab j) (hAcur j))
      (hlabref j)
  have hsub : ∀ j i, refinedRefRootSets A a κ lambda j i ⊆
      parentRefRootSets Q a κ0 lambda j := by
    intro j i
    exact refinedReferenceRoots_subset_parent (Q.parentPatch j) a (κ0 j) lambda
      (A j i) (κ j i)
      (refinedRootDomain_subset_parent (Q.chartData j) (Q.parentPatch j)
        (Q.parentEquiv j) (Q.parent_labels j) (Q.parent_curves j) (A j) (e j)
        (hAlab j) (hAcur j) i)
      (hlabref j i)
  refine ⟨hcov, hsub, pairwiseDisjoint_globalRefinedRootPiece _ _, ?_, ?_, ?_, ?_⟩
  · intro j z hz
    have hzu : z ∈ ⋃ i, refinedBlockPiece (parentRefRootSets Q a κ0 lambda)
        (refinedRefRootSets A a κ lambda) j i := by
      rw [iUnion_refinedBlockPiece (parentRefRootSets Q a κ0 lambda)
        (refinedRefRootSets A a κ lambda) hcov j]
      exact hz
    obtain ⟨i, hzi⟩ := mem_iUnion.mp hzu
    exact mem_iUnion₂.mpr ⟨Nat.pair j i,
      by
        show (Nat.unpair (Nat.pair j i)).1 = j
        rw [Nat.unpair_pair],
      by simpa [globalRefinedRootPiece, globalRefinedParent, globalRefinedChild,
        Nat.unpair_pair] using hzi⟩
  · intro j z hz
    exact existsUnique_globalRefinedRootPiece (parentRefRootSets Q a κ0 lambda)
      (refinedRefRootSets A a κ lambda) hcov hz
  · intro j
    exact refinedBlockPiece_restrict_eq_sum (parentRefRootSets Q a κ0 lambda)
      (refinedRefRootSets A a κ lambda) lambda hcov hmeasS hmeasR j
  · exact globalRefinedRootPiece_restrict_eq_sum (parentRefRootSets Q a κ0 lambda)
      (refinedRefRootSets A a κ lambda) lambda hcov hmeasS hmeasR

/-- **The producer map yields the refined family and its global root-piece
refinement.**  Choosing the concentric-core families of the producer map produces
patches, label identifications, label equations and curve equations; combining with
the assembly theorem gives the global C(a)/C(b) consequences for any matched label
reference laws. -/
theorem exists_rootPieceRefinement_of_producer
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {P : ℕ → F.CalibratedSeedWindow u} (Q : ParentChartProducer F u P) :
    ∃ (A : ℕ → ℕ → F.CalibratedLevelSeedPatch u)
      (e : ∀ j i, (A j i).covector.ker ≃L[ℝ] (Q.chartData j).p.ker),
      (∀ j i, (A j i).labels = (e j i) ⁻¹'
        ((Q.chartData j).V ∩ (Q.chartData j).σ ⁻¹'
          (Q.parentCore j ∩ closedBall ((Q.chartData j).σ 0) (i : ℝ)))) ∧
      (∀ j i (w : (A j i).covector.ker) (t : ℝ),
        (A j i).curve w t = (Q.chartData j).Γ ((Q.chartData j).σ ((e j i) w)) t) := by
  choose A e hprops using fun j => exists_parentRefinedFamily_withCurves Q hF hcomplete hu j
  exact ⟨A, e, fun j i => (hprops j).1 i, fun j i => (hprops j).2 i⟩

end OTSelector.Reconstruction
