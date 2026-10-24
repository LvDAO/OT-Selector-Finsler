import OTSelector.Reconstruction.FinslerCoefficientCoreTaylorCover
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Measurable finite cells for original coefficient neighborhoods

The finite Taylor neighborhoods split the original compact root set exactly.
Every cell retains its original reference center and actual distance estimate;
restriction identities keep the original root masses without renormalization.
-/

open Set Function MeasureTheory ProbabilityTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

/-- A finite measurable partition subordinate to a given family of neighborhoods. -/
structure FiniteRootNeighborhoodPartition {Z : Type*} [MeasurableSpace Z]
    (K centers : Set Z) (U : Z → Set Z) where
  count : ℕ
  center : Fin count → Z
  center_mem : ∀ i, center i ∈ centers
  cell : Fin count → Set Z
  measurable_cell : ∀ i, MeasurableSet (cell i)
  cell_subset : ∀ i, cell i ⊆ K ∩ U (center i)
  disjoint : Pairwise (fun i j ↦ Disjoint (cell i) (cell j))
  union_eq : (⋃ i, cell i) = K

/-- Finite measurable neighborhoods covering a measurable root set split it
without discarding any root or changing any reference center. -/
theorem exists_finiteRootNeighborhoodPartition {Z : Type*} [MeasurableSpace Z]
    {K centers : Set Z} {U : Z → Set Z} (hK : MeasurableSet K)
    (hfinite : centers.Finite) (hU : ∀ z ∈ centers, MeasurableSet (U z))
    (hcover : K ⊆ ⋃ z ∈ centers, U z) :
    Nonempty (FiniteRootNeighborhoodPartition K centers U) := by
  classical
  let : Fintype centers := hfinite.fintype
  let e : Fin (Fintype.card centers) ≃ centers := (Fintype.equivFin centers).symm
  let c : Fin (Fintype.card centers) → Z := fun i ↦ (e i).val
  let s : Fin (Fintype.card centers) → Set Z := fun i ↦ K ∩ U (c i)
  have hs : ∀ i, MeasurableSet (s i) := fun i ↦ hK.inter (hU _ (e i).property)
  have hscov : (⋃ i, s i) = K := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact hi.1
    · intro z hz
      obtain ⟨z₀, hz₀, hU₀⟩ := mem_iUnion₂.mp (hcover hz)
      refine mem_iUnion.mpr ⟨e.symm ⟨z₀, hz₀⟩, hz, ?_⟩
      simpa only [c, Equiv.apply_symm_apply] using hU₀
  exact ⟨{
    count := Fintype.card centers
    center := c
    center_mem := fun i ↦ (e i).property
    cell := disjointed s
    measurable_cell := fun i ↦ by
      rw [disjointed_eq_inter_compl]
      exact (hs i).inter (MeasurableSet.iInter fun j ↦
        MeasurableSet.iInter fun _ ↦ (hs j).compl)
    cell_subset := disjointed_subset s
    disjoint := disjoint_disjointed s
    union_eq := iUnion_disjointed.trans hscov }⟩

/-- The original root measure is exactly the sum of its cell restrictions. -/
theorem FiniteRootNeighborhoodPartition.sum_restrict
    {Z : Type*} [MeasurableSpace Z] {K centers : Set Z} {U : Z → Set Z}
    (D : FiniteRootNeighborhoodPartition K centers U) (lambda : Measure Z) :
    Measure.sum (fun i ↦ lambda.restrict (D.cell i)) = lambda.restrict K := by
  rw [← Measure.restrict_iUnion D.disjoint D.measurable_cell, D.union_eq]

/-- The original reference center on each cell, extended by the identity outside
the retained root core. -/
def FiniteRootNeighborhoodPartition.reference
    {Z : Type*} [MeasurableSpace Z] {K centers : Set Z} {U : Z → Set Z}
    (D : FiniteRootNeighborhoodPartition K centers U) (z : Z) : Z := by
  classical
  exact if h : ∃ i, z ∈ D.cell i then D.center h.choose else z

/-- Every member of a cell reads its actual retained reference center. -/
theorem FiniteRootNeighborhoodPartition.reference_eq
    {Z : Type*} [MeasurableSpace Z] {K centers : Set Z} {U : Z → Set Z}
    (D : FiniteRootNeighborhoodPartition K centers U) (i : Fin D.count)
    {z : Z} (hz : z ∈ D.cell i) : D.reference z = D.center i := by
  classical
  let h : ∃ j, z ∈ D.cell j := ⟨i, hz⟩
  have hi : h.choose = i := by
    by_contra hne
    exact Set.disjoint_left.mp (D.disjoint hne) h.choose_spec hz
  simp only [reference, dite_eq_left h, hi]

/-- The reference extension leaves roots outside the retained core unchanged. -/
theorem FiniteRootNeighborhoodPartition.reference_eq_self
    {Z : Type*} [MeasurableSpace Z] {K centers : Set Z} {U : Z → Set Z}
    (D : FiniteRootNeighborhoodPartition K centers U) {z : Z} (hz : z ∉ K) :
    D.reference z = z := by
  have hn : ¬∃ i, z ∈ D.cell i := by
    rintro ⟨i, hi⟩
    exact hz (D.cell_subset i hi).1
  simp only [reference, dite_eq_right hn]

/-- Reference centers are read measurably from the original root, so measurable
sampling never requires an additional reference-selection hypothesis. -/
theorem FiniteRootNeighborhoodPartition.measurable_reference
    {Z : Type*} [MeasurableSpace Z] {K centers : Set Z} {U : Z → Set Z}
    (D : FiniteRootNeighborhoodPartition K centers U) : Measurable D.reference := by
  classical
  have hK : MeasurableSet K := D.union_eq ▸ MeasurableSet.iUnion D.measurable_cell
  intro s hs
  have heq : D.reference ⁻¹' s = (Kᶜ ∩ s) ∪ ⋃ i, if D.center i ∈ s then D.cell i else ∅ := by
    ext z
    constructor
    · intro hz
      by_cases hzK : z ∈ K
      · obtain ⟨i, hi⟩ := mem_iUnion.mp (D.union_eq.symm ▸ hzK)
        have hci : D.center i ∈ s := D.reference_eq i hi ▸ hz
        exact Or.inr (mem_iUnion.mpr ⟨i, by simpa only [ite_eq_left hci] using hi⟩)
      · exact Or.inl ⟨hzK, by simpa only [mem_preimage, D.reference_eq_self hzK] using hz⟩
    · rintro (hz | hz)
      · simpa only [mem_preimage, D.reference_eq_self hz.1] using hz.2
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
        by_cases hci : D.center i ∈ s
        · have hzi : z ∈ D.cell i := by simpa only [ite_eq_left hci] using hi
          simpa only [mem_preimage, D.reference_eq i hzi] using hci
        · simp only [ite_eq_right hci, mem_empty_iff_false] at hi
  rw [heq]
  exact (hK.compl.inter hs).union (MeasurableSet.iUnion fun i ↦ by
    split_ifs
    · exact D.measurable_cell i
    · exact MeasurableSet.empty)

/-- Original physical populations split on the same root cells exactly. -/
theorem FiniteRootNeighborhoodPartition.sum_restrict_preimage
    {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    {K centers : Set Z} {U : Z → Set Z}
    (D : FiniteRootNeighborhoodPartition K centers U)
    (μ : Measure X) {a : X → Z} (ha : Measurable a) :
    Measure.sum (fun i ↦ μ.restrict (a ⁻¹' D.cell i)) = μ.restrict (a ⁻¹' K) := by
  have hd : Pairwise (fun i j ↦ Disjoint (a ⁻¹' D.cell i) (a ⁻¹' D.cell j)) :=
    fun i j hij ↦ (D.disjoint hij).preimage a
  rw [← Measure.restrict_iUnion hd (fun i ↦ ha (D.measurable_cell i)),
    ← preimage_iUnion, D.union_eq]

/-- Every original conditional pairing kernel retains its exact root weighting
under the finite partition, without independent resampling or renormalization. -/
theorem FiniteRootNeighborhoodPartition.sum_compProd
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    {K centers : Set Z} {U : Z → Set Z}
    (D : FiniteRootNeighborhoodPartition K centers U)
    (lambda : Measure Z) [SFinite lambda] (π : ProbabilityTheory.Kernel Z Y) :
    Measure.sum (fun i ↦ (lambda.restrict (D.cell i)) ⊗ₘ π) =
      (lambda.restrict K) ⊗ₘ π := by
  rw [← Measure.compProd_sum_left, D.sum_restrict]

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

namespace OriginalPopulationCoefficientCore

variable {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}

omit [BorelSpace E] in
/-- The actual finite Taylor cover has a measurable disjoint refinement preserving
all original roots, with no further mass loss or coefficient selection. -/
theorem TaylorRootCover.nonempty_partition [T2Space Z] [BorelSpace Z]
    (D : C.TaylorRootCover ε) :
    Nonempty (FiniteRootNeighborhoodPartition C.roots D.centers D.neighborhood) :=
  exists_finiteRootNeighborhoodPartition C.roots_compact.measurableSet D.finite
    (fun z hz ↦ (D.open_neighborhood z hz).measurableSet) D.covers

/-- Every pair of original roots in a retained cell obeys the same frozen
quadratic comparison, now on measurable disjoint events. -/
theorem TaylorRootCover.relative_distance_on_cell
    [T2Space M] [PreconnectedSpace M] [BorelSpace M]
    [MeasurableSpace.CountablySeparated Z]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instCellMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (D : C.TaylorRootCover ε)
    (Q : FiniteRootNeighborhoodPartition C.roots D.centers D.neighborhood)
    (hε : 0 ≤ ε) (i : Fin Q.count) {z z' : Z}
    (hz : z ∈ Q.cell i) (hz' : z' ∈ Q.cell i)
    {p : ℝ × ℝ} (hp : p ∈ C.window.region) :
    let S := (P C.seedIndex).seed
    let w := populationSeedRootLabelValue S a
    let v := (Module.finBasis ℝ S.covector.ker).equivFun (w z' - w z)
    |populationSeedPairDeficit S p (w z, w z') -
        matrixQuadratic (C.matrix (Q.center i) p) v| ≤
      (2 * ε) * matrixQuadratic (C.matrix (Q.center i) p) v :=
  D.relative_distance hF hcomplete hu ha hinj hε (Q.center_mem i)
    (Q.cell_subset i hz) (Q.cell_subset i hz') hp

end OriginalPopulationCoefficientCore
end OTSelector.Reconstruction
