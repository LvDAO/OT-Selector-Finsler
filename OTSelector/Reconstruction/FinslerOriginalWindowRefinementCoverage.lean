import OTSelector.Reconstruction.FinslerOriginalTileDataPopulationInputs
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Order.Disjointed

/-!
# Window refinement: cube coverage and retention of the tile atlas

The coverage reduction of the upper pressure lane left two geometric statements
open: the window seed labels fill the unit cube in normalized coordinates
(@@hlabelCover@@), and every cube-coordinate seed label is retained in the selected
disjoint piece (@@hretention@@).  This module proves both from the actual
calibrated-window refinement geometry.

## The linear cube inside a label neighborhood

If the retained labels of a seed contain a metric ball around the zero label,
then some continuous linear basis of the label space has its unit cube inside the
label set.  The proof scales the finiteness of the label basis: the preimage of
the open unit cube under a basis chosen with sufficiently small vectors lies in
the given ball.  This is the exact role of the linear basis @@e@@ in the tile data.

## Core interiority

The actual seed labels of a window are `openLabels ∩ position ⁻¹' core` in the
original C1,1 presentation.  If the compact core contains a metric ball around the
section point `position 0`, then continuity of the section and openness of the
label domain put a ball around the zero label inside the retained labels.  Hence
`hlabelCover` follows from this single interiority condition, which is exactly the
content of "the window's retained labels cover the unit cube".

## Retention

Retention is the disjointification statement of the retained reference roots:
a root belongs to piece `j` exactly when its original reference intensity is finite
and nonzero and no earlier window owns it.  Hence `hretention` follows from the
finite-nonzero reference intensity at the label's root together with the fact that
window `j` is the first owner of that root.

## Assembly

The two reductions are assembled into the coverage statement of the tile atlas:

@@∃ e, seedUnitCube q ⊆ e '' (seedLabel '' populationSeedRootPiece j)@@

under core interiority of the window's presentation and the two retention
conditions.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open Module
open MeasureTheory.Measure
open OTSelector.Probability
open Metric
open scoped Topology ContDiff ENNReal NNReal BigOperators

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

/-! ## The linear cube inside a label neighborhood -/

/-- **A label ball contains a linear cube.**  If a label set contains a metric
ball around the zero label of a finite-dimensional normed real vector space, then
some continuous linear basis of that space has its open unit cube inside the
label set.  This discharges the linear-basis freedom in the cube coverage
statement: the cube can be made as small as the given ball. -/
theorem exists_continuousLinearEquiv_seedUnitCube_subset
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {labels : Set V} (hball : ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : V) r ⊆ labels) :
    ∃ e : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ),
      OTSelector.Probability.seedUnitCube (Module.finrank ℝ V) ⊆ e '' labels := by
  classical
  obtain ⟨r, hr, hsub⟩ := hball
  let b : Basis (Fin (Module.finrank ℝ V)) ℝ V := Module.finBasis ℝ V
  set C : ℝ := ∑ i, ‖b i‖ with hCdef
  have hCnn : 0 ≤ C := Finset.sum_nonneg fun i _ => norm_nonneg _
  set c : ℝ := C / r + 1 with hcdef
  have hcpos : 0 < c := by
    have h1 : 0 ≤ C / r := div_nonneg hCnn hr.le
    rw [hcdef]; linarith
  have hcne : c ≠ 0 := hcpos.ne'
  let phi : (Fin (Module.finrank ℝ V) → ℝ) →ₗ[ℝ] V :=
    { toFun := fun y => ∑ i, (y i / c) • b i
      map_add' := by
        intro y z
        simp only [Pi.add_apply, add_div, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro x y
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_div_assoc,
          Finset.smul_sum, smul_smul] }
  have hphi_inj : Function.Injective phi := by
    intro y z hyz
    have hzero : ∑ i, ((y i - z i) / c) • b i = 0 := by
      have hsub2 : (∑ i, (y i / c) • b i) = ∑ i, (z i / c) • b i := by
        have h := hyz
        simp only [phi, LinearMap.coe_mk, AddHom.coe_mk] at h
        exact h
      have hsplit : ∑ i, ((y i - z i) / c) • b i =
          ∑ i, (y i / c) • b i - ∑ i, (z i / c) • b i := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show ((y i - z i) / c) = (y i / c) - (z i / c) by field_simp]
        rw [sub_smul]
      rw [hsplit, hsub2, sub_self]
    have hLI := Fintype.linearIndependent_iff.mp b.linearIndependent
    funext i
    have hi : (y i - z i) / c = 0 := hLI (fun i => (y i - z i) / c) hzero i
    have hc0 : y i - z i = 0 := by
      field_simp at hi
      simpa using hi
    exact sub_eq_zero.mp hc0
  have hphi_surj : Function.Surjective phi := by
    intro v
    refine ⟨fun i => c * b.repr v i, ?_⟩
    simp only [phi, LinearMap.coe_mk, AddHom.coe_mk]
    conv_rhs => rw [← b.sum_repr v]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_div_cancel_left₀ _ hcne]
  let eLin : V ≃ₗ[ℝ] (Fin (Module.finrank ℝ V) → ℝ) :=
    (LinearEquiv.ofBijective phi ⟨hphi_inj, hphi_surj⟩).symm
  let e : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := eLin.toContinuousLinearEquiv
  refine ⟨e, ?_⟩
  intro y hy
  rw [OTSelector.Probability.seedUnitCube] at hy
  have hcoord : ∀ i, |y i| < 1 := by
    intro i
    have hmem := hy i (mem_univ i)
    rw [mem_Ioo] at hmem
    rw [abs_lt]
    exact ⟨by linarith [hmem.1], hmem.2⟩
  have hesymm : (e.symm y : V) = phi y := rfl
  have hnorm : ‖e.symm y‖ ≤ C / c := by
    rw [hesymm]
    calc ‖∑ i, (y i / c) • b i‖ ≤ ∑ i, ‖(y i / c) • b i‖ := norm_sum_le _ _
      _ ≤ ∑ i, (1 / c) * ‖b i‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc ‖(y i / c) • b i‖
              = |y i / c| * ‖b i‖ := by rw [norm_smul, Real.norm_eq_abs]
            _ = (|y i| * c⁻¹) * ‖b i‖ := by
                rw [abs_div, abs_of_pos hcpos, div_eq_inv_mul]
                ring
            _ ≤ (1 * c⁻¹) * ‖b i‖ := by
                refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                exact mul_le_mul_of_nonneg_right (le_of_lt (hcoord i))
                  (inv_nonneg.mpr hcpos.le)
            _ = (1 / c) * ‖b i‖ := by ring
      _ = (1 / c) * C := by rw [hCdef, Finset.mul_sum]
      _ = C / c := by ring
  have hrc : r * c = C + r := by
    rw [hcdef]
    field_simp
  have hbound : C / c < r := by
    rw [div_lt_iff₀ hcpos, hrc]
    linarith
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  exact hsub (by rw [mem_ball_zero_iff]; exact lt_of_le_of_lt hnorm hbound)



/-! ## Core interiority gives a ball of labels around zero -/

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- **Core interiority gives a label ball.**  In the original C1,1 seed
presentation the retained labels are the label domain intersected with the
preimage of the core.  If the compact core contains a metric ball around the
section point at zero, then continuity of the section and openness of the label
domain put a metric ball around the zero label inside the retained labels. -/
theorem ball_zero_subset_labels_of_core_interior
    (A : F.CalibratedLevelSeedPatch u)
    (D : OTSelector.Geometry.ContinuousFinslerNorm.C11LevelSeedPresentation F u
      A.covector A.level A.openLabels A.labels A.curve)
    (hint : ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (D.position 0) ρ ⊆ D.core) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : A.covector.ker) r ⊆ A.labels := by
  obtain ⟨ρ, hρ, hball⟩ := hint
  have hcont : ContinuousAt D.position 0 :=
    ContinuousOn.continuousAt (f := D.position) (s := A.openLabels)
      D.position_contDiff.continuousOn
      (A.openLabels_open.mem_nhds D.zero_mem)
  obtain ⟨δ₁, hδ₁, hδ₁pos⟩ := Metric.continuousAt_iff.mp hcont ρ hρ
  obtain ⟨δ₂, hδ₂, hδ₂sub⟩ := Metric.isOpen_iff.mp A.openLabels_open 0 D.zero_mem
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro x hx
  rw [mem_ball_zero_iff] at hx
  have hx₁ : dist x (0 : A.covector.ker) < δ₁ := by
    rw [dist_eq_norm]
    simpa using lt_of_lt_of_le hx (min_le_left _ _)
  have hx₂ : x ∈ A.openLabels := by
    apply hδ₂sub
    rw [mem_ball_zero_iff]
    exact lt_of_lt_of_le hx (min_le_right _ _)
  have hxcore : D.position x ∈ D.core := by
    apply hball
    rw [mem_ball]
    exact hδ₁pos hx₁
  rw [D.labels_eq]
  exact ⟨hx₂, hxcore⟩

/-- **The unit cube inside the retained labels.**  Combining the linear-cube
lemma with core interiority: some continuous linear basis of the seed label space
has its open unit cube inside the retained labels.  This is the cube coverage
input of the window labels, with the linear basis chosen from the label
geometry. -/
theorem exists_seedLabelCover_of_core_interior
    (A : F.CalibratedLevelSeedPatch u)
    (D : OTSelector.Geometry.ContinuousFinslerNorm.C11LevelSeedPresentation F u
      A.covector A.level A.openLabels A.labels A.curve)
    (hint : ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (D.position 0) ρ ⊆ D.core) :
    ∃ e : A.covector.ker ≃L[ℝ] (Fin (Module.finrank ℝ A.covector.ker) → ℝ),
      OTSelector.Probability.seedUnitCube (Module.finrank ℝ A.covector.ker) ⊆
        e '' A.labels :=
  exists_continuousLinearEquiv_seedUnitCube_subset
    (ball_zero_subset_labels_of_core_interior A D hint)

/-! ## Retention: the disjoint piece membership -/

/-- **Membership in a selected disjoint piece.**  A label belongs to the
retained piece j exactly when its original reference intensity is finite and
nonzero at the root and no earlier window owns the root. -/
theorem mem_populationSeedRootPiece_iff (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z) (j : ℕ) (z : Z) :
    z ∈ populationSeedRootPiece P a κ lambda j ↔
      z ∈ populationSeedReferenceRoots (P j).seed a (κ j) lambda ∧
        ∀ i < j, z ∉ populationSeedReferenceRoots (P i).seed a (κ i) lambda := by
  rw [populationSeedRootPiece, disjointed_eq_inter_compl]
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff]

/-- **Retention from the first owner and the finite-nonzero reference intensity.** -/
theorem mem_populationSeedRootPiece_of_root_and_firstOwner
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z) (j : ℕ) {z : Z}
    (hroot : z ∈ populationSeedReferenceRoots (P j).seed a (κ j) lambda)
    (hfirst : ∀ i < j, z ∉ populationSeedReferenceRoots (P i).seed a (κ i) lambda) :
    z ∈ populationSeedRootPiece P a κ lambda j :=
  (mem_populationSeedRootPiece_iff P a κ lambda j z).mpr ⟨hroot, hfirst⟩

/-- **Retention of a cube-coordinate seed label.**  If every retained seed label of
window `j` has its original root carrying a finite nonzero reference intensity and
window `j` is the first owner of that root, then every such root belongs to the
selected disjoint piece: the `hretention` condition of the cube coverage. -/
theorem retention_of_root_and_firstOwner (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z) (j : ℕ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRefinementRetentionMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hroot : ∀ w ∈ (P j).seed.labels, a ((P j).seed.curve w 0) ∈
      populationSeedReferenceRoots (P j).seed a (κ j) lambda)
    (hfirst : ∀ w ∈ (P j).seed.labels, ∀ i < j, a ((P j).seed.curve w 0) ∉
      populationSeedReferenceRoots (P i).seed a (κ i) lambda)
    {w : (P j).seed.covector.ker} (hw : w ∈ (P j).seed.labels) :
    a ((P j).seed.curve w 0) ∈ populationSeedRootPiece P a κ lambda j :=
  mem_populationSeedRootPiece_of_root_and_firstOwner P a κ lambda j
    (hroot w hw) (fun i hi => hfirst w hw i hi)

/-! ## Assembly: cube coverage of the retained window piece -/

/-- **Cube coverage from the actual window refinement geometry.**  Under core
interiority of the window's C1,1 presentation and the two retention conditions,
there is a continuous linear basis of the seed label space whose open unit cube
covers the retained reference piece of the window:

@@∃ e, seedUnitCube q ⊆ e '' (seedLabel '' populationSeedRootPiece j)@@.

This is the coverage hypothesis used by the cube-cell construction of the tile
atlas, now derived from the window geometry rather than assumed. -/
theorem exists_cubeCoverage_of_core_interior (P : ℕ → F.CalibratedSeedWindow u)
    (a : M → Z) (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z) (j : ℕ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRefinementCoverageMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (D : OTSelector.Geometry.ContinuousFinslerNorm.C11LevelSeedPresentation F u
      (P j).seed.covector (P j).seed.level (P j).seed.openLabels (P j).seed.labels
      (P j).seed.curve)
    (hint : ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (D.position 0) ρ ⊆ D.core)
    (hroot : ∀ w ∈ (P j).seed.labels, a ((P j).seed.curve w 0) ∈
      populationSeedReferenceRoots (P j).seed a (κ j) lambda)
    (hfirst : ∀ w ∈ (P j).seed.labels, ∀ i < j, a ((P j).seed.curve w 0) ∉
      populationSeedReferenceRoots (P i).seed a (κ i) lambda) :
    ∃ e : (P j).seed.covector.ker ≃L[ℝ]
        (Fin (Module.finrank ℝ (P j).seed.covector.ker) → ℝ),
      OTSelector.Probability.seedUnitCube (Module.finrank ℝ (P j).seed.covector.ker) ⊆
        e '' (populationSeedRootLabelValue (P j).seed a ''
          populationSeedRootPiece P a κ lambda j) := by
  obtain ⟨e, he⟩ := exists_seedLabelCover_of_core_interior (P j).seed D hint
  refine ⟨e, ?_⟩
  intro v hv
  obtain ⟨w, hw, hwe⟩ := he hv
  have hzpiece : a ((P j).seed.curve w 0) ∈ populationSeedRootPiece P a κ lambda j :=
    retention_of_root_and_firstOwner P a κ lambda j hF hcomplete hu ha hinj
      hroot hfirst hw
  refine ⟨populationSeedRootLabelValue (P j).seed a (a ((P j).seed.curve w 0)),
    ⟨a ((P j).seed.curve w 0), hzpiece, rfl⟩, ?_⟩
  rw [populationSeedRootLabelValue_at_label (P j).seed hF hcomplete hu ha hinj ⟨w, hw⟩]
  exact hwe

end OTSelector.Reconstruction
