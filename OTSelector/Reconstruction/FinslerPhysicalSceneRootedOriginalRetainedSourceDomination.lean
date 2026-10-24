import OTSelector.Reconstruction.FinslerPhysicalSceneRootedRetainedCoreCarrierInclusion
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMarginals

/-!
# Retained original near unions are dominated by the same original source rows

Restricting a physical plan to the retained near union inside one fixed original
seed piece uses only rows of the original finite cores with that same seed.
After the same spatial observation and rooting, its entire source marginal is
dominated by the sum of those original source restrictions. Every target remains
in the source test, and the original allocation columns are unchanged.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability
open scoped Topology ContDiff ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section SourceRows
variable {X : Type*} [MeasurableSpace X] {I : Type*} [Fintype I]
  {ι : Type*} [Fintype ι]

/-- A finite physical row domination transfers to the entire source marginal
in the same rooted coordinates, with its literal original scaling factor. -/
theorem physicalSceneRootedPlan_source_le_sum_original_rows
    (Γ : Measure (X × X)) (μ : Measure X) (hfst : Γ.fst = μ)
    (E : Set (X × X)) (H : I → Set X) (hH : ∀ i, MeasurableSet (H i))
    (selected : I → Prop) [DecidablePred selected]
    (hrows : Γ.restrict E ≤ ∑ i, if selected i then Γ.restrict (H i ×ˢ univ) else 0)
    (coord : X → (ι → ℝ)) (hcoord : Measurable coord)
    (clock : X → ℝ) (hclock : Measurable clock) (N : ℝ) (root : ι → ℝ) :
    (physicalSceneRootedPlan (Γ.restrict E) coord clock N root).fst ≤
      ∑ i, if selected i then
        ENNReal.ofReal N • (μ.restrict (H i)).map (fun x ↦ (coord x - root, clock x))
      else 0 := by
  let endpoint := fun x : X ↦ (coord x - root, clock x)
  have he : Measurable endpoint := (hcoord.sub measurable_const).prodMk hclock
  have hrow (i : I) :
      (if selected i then Γ.restrict (H i ×ˢ univ) else 0).fst =
        if selected i then μ.restrict (H i) else 0 := by
    split_ifs with hi
    · have hpre : (Prod.fst : X × X → X) ⁻¹' H i = H i ×ˢ univ := by
        ext e
        simp
      have hrestrict : (Γ.restrict (H i ×ˢ univ)).fst = Γ.fst.restrict (H i) := by
        change (Γ.restrict (H i ×ˢ univ)).map Prod.fst = (Γ.map Prod.fst).restrict (H i)
        rw [Measure.restrict_map measurable_fst (hH i), hpre]
      rw [hrestrict, hfst]
    · simp [Measure.fst]
  have hs : (Γ.restrict E).fst ≤ ∑ i, if selected i then μ.restrict (H i) else 0 := by
    have hh := Measure.fst_mono hrows
    rw [← Measure.sum_fintype, Measure.fst_sum, Measure.sum_fintype] at hh
    simpa only [hrow] using hh
  have hm := smul_le_smul_left (ENNReal.ofReal N) (Measure.map_mono hs he)
  have hmap :
      (∑ i, if selected i then μ.restrict (H i) else 0).map endpoint =
        ∑ i, if selected i then (μ.restrict (H i)).map endpoint else 0 := by
    rw [← Measure.sum_fintype, Measure.map_sum he.aemeasurable, Measure.sum_fintype]
    congr 1
    funext i
    split_ifs <;> simp
  rw [(physicalSceneRootedPlan_marginals (Γ.restrict E) coord hcoord clock hclock N root).1]
  rw [hmap, Finset.smul_sum] at hm
  simpa only [smul_ite, smul_zero, endpoint] using hm

end SourceRows

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

namespace PopulationLocalPressureCore
variable (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)

/-- The original retained near union in a fixed seed uses only source rows
from original coefficient cores belonging to that same seed. -/
theorem restrict_retainedNearCarrier_fixed_seed_le_sum_original_rows
    (Γ : Measure (M × M)) (j : ℕ) (A B : Set M) (nearRadius : ℝ) :
    Γ.restrict (D.retainedNearCarrierEvent A B nearRadius ∩
      (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
        (lambda := lambda) j ×ˢ univ)) ≤
      ∑ i : Fin D.haar.continuous.count,
        if (D.haar.continuous.coefficient i).seedIndex = j then
          Γ.restrict ((a ⁻¹' (D.haar.continuous.coefficient i).roots) ×ˢ univ)
        else 0 := by
  let rows : Fin D.haar.continuous.count → Set (M × M) := fun i ↦
    if (D.haar.continuous.coefficient i).seedIndex = j then
      (a ⁻¹' (D.haar.continuous.coefficient i).roots) ×ˢ univ else ∅
  have hsub : D.retainedNearCarrierEvent A B nearRadius ∩
      (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
        (lambda := lambda) j ×ˢ univ) ⊆ ⋃ i, rows i := by
    intro e he
    obtain ⟨i, hi⟩ := mem_iUnion.mp he.1.1
    have hseed := (D.nearDisplacement_source_mem_fixed_seed_iff i j hi).mp he.2.1
    apply mem_iUnion.mpr ⟨i, ?_⟩
    simpa only [rows, ite_eq_left hseed, mem_prod, mem_preimage, mem_univ, and_true]
      using hi.1
  calc
    _ ≤ Γ.restrict (⋃ i, rows i) := Measure.restrict_mono_set Γ hsub
    _ ≤ Measure.sum (fun i ↦ Γ.restrict (rows i)) := Measure.restrict_iUnion_le
    _ = _ := by
      rw [Measure.sum_fintype]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [rows]
      split_ifs <;> simp

/-- The entire rooted retained source, with all targets, is bounded by the
same original physical source rows in any measurable common observation. -/
theorem rooted_retainedNearCarrier_fixed_seed_source_le_sum_original_rows
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (ha : Measurable a)
    (Γ : Measure (M × M)) (hfst : Γ.fst = μ)
    (j : ℕ) (A B : Set M) (nearRadius : ℝ)
    {ι : Type*} [Fintype ι] (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (hu : Measurable u) (N : ℝ) (root : ι → ℝ) :
    (physicalSceneRootedPlan
      (Γ.restrict (D.retainedNearCarrierEvent A B nearRadius ∩
        (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
          (lambda := lambda) j ×ˢ univ))) coord u N root).fst ≤
      ∑ i : Fin D.haar.continuous.count,
        if (D.haar.continuous.coefficient i).seedIndex = j then
          ENNReal.ofReal N •
            (μ.restrict (a ⁻¹' (D.haar.continuous.coefficient i).roots)).map
              (fun x ↦ (coord x - root, u x))
        else 0 := by
  let _originalRetainedSourceDominationMetric : MetricSpace M := F.metricSpace
  let _originalRetainedSourceDominationProper : ProperSpace M :=
    F.properSpace_of_complete hcomplete
  let _originalRetainedSourceDominationPolish : PolishSpace M := inferInstance
  exact physicalSceneRootedPlan_source_le_sum_original_rows Γ μ hfst _
    (fun i : Fin D.haar.continuous.count ↦ a ⁻¹' (D.haar.continuous.coefficient i).roots)
    (fun i ↦ (D.haar.continuous.coefficient i).roots_compact.measurableSet.preimage ha)
    (fun i ↦ (D.haar.continuous.coefficient i).seedIndex = j)
    (D.restrict_retainedNearCarrier_fixed_seed_le_sum_original_rows Γ j A B nearRadius)
    coord hcoord u hu N root

/-- Every source test, including an arbitrary test intersected with a spatial
window and the full clock axis, keeps its literal original row-source bound. -/
theorem rooted_retainedNearCarrier_fixed_seed_source_test_le_sum_original_rows
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (ha : Measurable a)
    (Γ : Measure (M × M)) (hfst : Γ.fst = μ)
    (j : ℕ) (A B : Set M) (nearRadius : ℝ)
    {ι : Type*} [Fintype ι] (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (hu : Measurable u) (N : ℝ) (root : ι → ℝ)
    (T : Set ((ι → ℝ) × ℝ)) (U : Set (ι → ℝ)) :
    (physicalSceneRootedPlan
      (Γ.restrict (D.retainedNearCarrierEvent A B nearRadius ∩
        (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
          (lambda := lambda) j ×ˢ univ))) coord u N root).fst (T ∩ (U ×ˢ univ)) ≤
      ∑ i : Fin D.haar.continuous.count,
        if (D.haar.continuous.coefficient i).seedIndex = j then
          ENNReal.ofReal N *
            ((μ.restrict (a ⁻¹' (D.haar.continuous.coefficient i).roots)).map
              (fun x ↦ (coord x - root, u x))) (T ∩ (U ×ˢ univ))
        else 0 := by
  have hh := D.rooted_retainedNearCarrier_fixed_seed_source_le_sum_original_rows
    hcomplete ha Γ hfst j A B nearRadius coord hcoord hu N root (T ∩ (U ×ˢ univ))
  simp only [Measure.finsetSum_apply] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [Measure.smul_apply]

/-- The source observation is the fixed original seed frame, independent of
the auxiliary finite cores, and the rooted multiplicity remains the original N. -/
theorem rooted_retainedNearCarrier_original_seed_source_le_sum_original_rows
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (Γ : Measure (M × M)) (hfst : Γ.fst = μ)
    (j : ℕ) (A B : Set M) (nearRadius scale N : ℝ)
    (root : Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) :
    let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j scale
    (physicalSceneRootedPlan
      (Γ.restrict (D.retainedNearCarrierEvent A B nearRadius ∩
        (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
          (lambda := lambda) j ×ˢ univ))) coord u N root).fst ≤
      ∑ i : Fin D.haar.continuous.count,
        if (D.haar.continuous.coefficient i).seedIndex = j then
          ENNReal.ofReal N •
            (μ.restrict (a ⁻¹' (D.haar.continuous.coefficient i).roots)).map
              (fun x ↦ (coord x - root, u x))
        else 0 := by
  let _originalRetainedSourceDominationFixedMetric : MetricSpace M := F.metricSpace
  intro coord
  exact D.rooted_retainedNearCarrier_fixed_seed_source_le_sum_original_rows hcomplete ha Γ
    hfst j A B nearRadius coord
    (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j scale)
    hu.continuous.measurable N root

/-- A globally feasible original allocation satisfies the same row domination
with its original target cloud and every original column left in place. -/
theorem original_allocation_rooted_retainedNearCarrier_source_le_sum_original_rows
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (ha : Measurable a)
    {n : ℕ} (allocation : M → Fin (n + 1) → ℝ) {weights : Fin (n + 1) → ℝ}
    (hfeas : IsSemidiscreteAllocation μ weights allocation) (Y : Fin (n + 1) → M)
    (j : ℕ) (A B : Set M) (nearRadius : ℝ)
    {ι : Type*} [Fintype ι] (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (hu : Measurable u) (N : ℝ) (root : ι → ℝ) :
    (physicalSceneRootedPlan
      ((physicalSceneAllocationPlan μ allocation Y).restrict
        (D.retainedNearCarrierEvent A B nearRadius ∩
          (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
            (lambda := lambda) j ×ˢ univ))) coord u N root).fst ≤
      ∑ i : Fin D.haar.continuous.count,
        if (D.haar.continuous.coefficient i).seedIndex = j then
          ENNReal.ofReal N •
            (μ.restrict (a ⁻¹' (D.haar.continuous.coefficient i).roots)).map
              (fun x ↦ (coord x - root, u x))
        else 0 :=
  D.rooted_retainedNearCarrier_fixed_seed_source_le_sum_original_rows hcomplete ha
    (physicalSceneAllocationPlan μ allocation Y) (physicalSceneAllocationPlan_fst hfeas Y)
    j A B nearRadius coord hcoord hu N root

end PopulationLocalPressureCore
end OTSelector.Reconstruction
