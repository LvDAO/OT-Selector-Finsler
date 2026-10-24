import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Topology.MetricSpace.Thickening

/-!
## Lemma skeleton

* **Conditions:** A finite Borel coordinate measure, a measurable set inside a specified open region, and positive mesh/error bounds; simultaneous-volume version also has finite volume of that open region. Plan/clock/label versions provide exact marginal or measurable-embedding data.
* **Objects:** Finite pairwise disjoint equal grid cubes inside the region, of arbitrarily small mesh, approximate the original set in symmetric-difference mass; exact marginal laws transfer that error.
* **Proof detail:** Use regularity to put a compact inner carrier inside a suitable open approximation. A sufficiently fine grid has only finitely many cells meeting the compact core and all lie in the open region. Bound symmetric difference, apply to the sum measure for simultaneous control, and transport through exact marginals/embeddings.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4*, Theorem 433C(a)–(b), p. 12; Corollary 416H, p. 69.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=12
* D. H. Fremlin, *Measure Theory, Volume 4, Appendix*, Sections 4A2G(e), pp. 15–16; 4A2N(b), p. 22; 4A2Q(h) and proof, pp. 24–25.
  https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=24
* D. H. Fremlin, *Measure Theory, Volume 2*, Section 235G, integration along an inverse-measure-preserving map.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf

**Relationship to the sources:** Derived finite-grid regular approximation. The target measure need not be uniform on a cube; the legal-plan wrapper only restricts an already almost-everywhere legal plan.
-/

/-!
Finite disjoint equal cubes approximate each original measurable label cell
in its original finite measure. Cubes lie inside a specified open atlas region
and can be made arbitrarily small. No exact cube law is imposed on the cell.
-/

open Set MeasureTheory Filter Metric BoxIntegral
open scoped Topology ENNReal symmDiff

noncomputable section
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

/-- Fine grid cubes meeting a compact core remain inside any prescribed open
neighborhood of that core. The index family is actually finite and its cubes
are pairwise disjoint. -/
theorem exists_finite_disjoint_grid_cubes_around_compact
    {ι : Type*} [Fintype ι] {K U : Set (ι → ℝ)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {mesh : ℝ} (hmesh : 0 < mesh) :
    ∃ n : ℕ, ∃ hn : NeZero n, ∃ F : Finset (ι → ℤ),
      (1 / (n : ℝ) < mesh) ∧
      K ⊆ ⋃ ν ∈ F, ((unitPartition.box n ν) : Set (ι → ℝ)) ∧
      (⋃ ν ∈ F, ((unitPartition.box n ν) : Set (ι → ℝ))) ⊆ U ∧
      Set.PairwiseDisjoint (↑F : Set (ι → ℤ))
        (fun ν ↦ ((unitPartition.box n ν) : Set (ι → ℝ))) ∧
      ∀ ν ∈ F, (((unitPartition.box n ν) : Set (ι → ℝ)) ∩ K).Nonempty := by
  classical
  obtain ⟨d, hd, hdU⟩ := hK.exists_thickening_subset_open hU hKU
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (lt_min hd hmesh)
  let n := m + 1
  haveI hn : NeZero n := ⟨Nat.succ_ne_zero _⟩
  have hnd : (1 : ℝ) / n < d := by
    simpa only [n, Nat.cast_add, Nat.cast_one] using hm.trans_le (min_le_left _ _)
  have hnm : (1 : ℝ) / n < mesh := by
    simpa only [n, Nat.cast_add, Nat.cast_one] using hm.trans_le (min_le_right _ _)
  obtain ⟨B, hB, hKB⟩ := BoxIntegral.le_hasIntegralVertices_of_isBounded hK.isBounded
  let F : Finset (ι → ℤ) := (unitPartition.admissibleIndex n B).filter
    (fun ν ↦ (((unitPartition.box n ν) : Set (ι → ℝ)) ∩ K).Nonempty)
  refine ⟨n, hn, F, hnm, ?_, ?_, ?_, ?_⟩
  · intro x hx
    refine mem_iUnion.mpr ⟨unitPartition.index n x, mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr
        ⟨unitPartition.mem_admissibleIndex_of_mem_box n hB (hKB hx),
          ⟨x, (unitPartition.mem_box_iff_index).mpr rfl, hx⟩⟩
    · exact (unitPartition.mem_box_iff_index).mpr rfl
  · intro x hx
    obtain ⟨ν, hν, hxν⟩ := mem_iUnion₂.mp hx
    obtain ⟨y, hyν, hyK⟩ := (Finset.mem_filter.mp hν).2
    apply hdU
    apply Metric.mem_thickening_iff.mpr
    refine ⟨y, hyK, ?_⟩
    have hdist : dist x y ≤ Metric.diam (Box.Icc (unitPartition.box n ν)) :=
      Metric.dist_le_diam_of_mem (Box.isBounded_Icc _)
        (Box.coe_subset_Icc hxν) (Box.coe_subset_Icc hyν)
    exact (hdist.trans (unitPartition.diam_boxIcc n ν)).trans_lt hnd
  · intro ν hν ν' hν' hne
    exact unitPartition.disjoint.mp hne
  · intro ν hν
    exact (Finset.mem_filter.mp hν).2

/-- Finite disjoint equal cubes approximate an actual measurable cell in its
unchanged finite law, inside a specified open atlas neighborhood. Both lost
and added original masses are explicitly bounded by the symmetric difference.
The mesh can be prescribed before the approximation is produced. -/
theorem exists_finite_disjoint_grid_cubes_approx_inside_open
    {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    {s V : Set (ι → ℝ)} (hs : MeasurableSet s) (hV : IsOpen V) (hsV : s ⊆ V)
    {ε : ℝ≥0∞} (hε : 0 < ε) {mesh : ℝ} (hmesh : 0 < mesh) :
    ∃ n : ℕ, ∃ hn : NeZero n, ∃ F : Finset (ι → ℤ),
      (1 / (n : ℝ) < mesh) ∧
      Set.PairwiseDisjoint (↑F : Set (ι → ℤ))
        (fun ν ↦ ((unitPartition.box n ν) : Set (ι → ℝ))) ∧
      (⋃ ν ∈ F, ((unitPartition.box n ν) : Set (ι → ℝ))) ⊆ V ∧
      μ ((⋃ ν ∈ F, ((unitPartition.box n ν) : Set (ι → ℝ))) ∆ s) < ε := by
  classical
  obtain ⟨K, hKs, hK, hsmallK⟩ := hs.exists_isCompact_sdiff_lt
    (measure_ne_top μ s) (ENNReal.half_pos hε.ne').ne'
  obtain ⟨U, hsU, hU, _, hsmallU⟩ := hs.exists_isOpen_sdiff_lt
    (measure_ne_top μ s) (ENNReal.half_pos hε.ne').ne'
  obtain ⟨n, hn, F, hnm, hKF, hFU, hdisj, _⟩ :=
    exists_finite_disjoint_grid_cubes_around_compact hK (hU.inter hV)
      (fun x hx ↦ ⟨hsU (hKs hx), hsV (hKs hx)⟩) hmesh
  refine ⟨n, hn, F, hnm, hdisj, hFU.trans inter_subset_right, ?_⟩
  let cubes : Set (ι → ℝ) := ⋃ ν ∈ F, ((unitPartition.box n ν) : Set (ι → ℝ))
  have hsub : cubes ∆ s ⊆ (U \ s) ∪ (s \ K) := by
    intro x hx
    rcases hx with h | h
    · exact Or.inl ⟨(hFU h.1).1, h.2⟩
    · exact Or.inr ⟨h.1, fun hxK ↦ h.2 (hKF hxK)⟩
  calc μ (cubes ∆ s) ≤ μ ((U \ s) ∪ (s \ K)) := measure_mono hsub
    _ ≤ μ (U \ s) + μ (s \ K) := measure_union_le _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hsmallU hsmallK
    _ = ε := ENNReal.add_halves _


/-- The same cubes control both the unchanged finite population label law and
Lebesgue volume. The latter controls the frozen uniform label mass added outside
the actual cell. No regularity assumption on the boundary of the cell is needed. -/
theorem exists_grid_cubes_approx_original_and_volume
    {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    {s V : Set (ι → ℝ)} (hs : MeasurableSet s) (hV : IsOpen V) (hsV : s ⊆ V)
    (hvolV : volume V < ∞) {ε : ℝ≥0∞} (hε : 0 < ε)
    {mesh : ℝ} (hmesh : 0 < mesh) :
    ∃ n : ℕ, ∃ hn : NeZero n, ∃ F : Finset (ι → ℤ),
      (1 / (n : ℝ) < mesh) ∧
      Set.PairwiseDisjoint (↑F : Set (ι → ℤ))
        (fun ν ↦ ((unitPartition.box n ν) : Set (ι → ℝ))) ∧
      (⋃ ν ∈ F, ((unitPartition.box n ν) : Set (ι → ℝ))) ⊆ V ∧
      μ ((⋃ ν ∈ F, ((unitPartition.box n ν) : Set (ι → ℝ))) ∆ s) < ε ∧
      volume ((⋃ ν ∈ F, ((unitPartition.box n ν) : Set (ι → ℝ))) ∆ s) < ε := by
  classical
  haveI : IsFiniteMeasure (volume.restrict V) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hvolV⟩
  obtain ⟨n, hn, F, hnm, hdisj, hsub, hsmall⟩ :=
    exists_finite_disjoint_grid_cubes_approx_inside_open (μ + volume.restrict V)
      hs hV hsV hε hmesh
  refine ⟨n, hn, F, hnm, hdisj, hsub, ?_, ?_⟩
  · exact (le_add_right le_rfl).trans_lt hsmall
  · let C : Set (ι → ℝ) := ⋃ ν ∈ F, ((unitPartition.box n ν) : Set (ι → ℝ))
    have hC : MeasurableSet C := MeasurableSet.iUnion fun ν ↦
      MeasurableSet.iUnion fun _ ↦ (unitPartition.box n ν).measurableSet_coe
    have hdiff : C ∆ s ⊆ V := by
      intro x hx
      rcases hx with h | h
      · exact hsub h.1
      · exact hsV h.1
    have hv : (volume.restrict V) (C ∆ s) = volume (C ∆ s) := by
      rw [Measure.restrict_apply (hC.symmDiff hs), inter_eq_left.mpr hdiff]
    rw [← hv]
    exact (le_add_left le_rfl).trans_lt hsmall

/-- Root-shape mismatch is charged exactly once in the original joint law.
This applies in particular to each original conditional clock kernel, whose
joint root marginal remains the original population label law. -/
theorem root_shape_mismatch_mass_eq
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    (μ : Measure Z) (plan : Measure (Z × Y)) (hplan : plan.map Prod.fst = μ)
    {s C : Set Z} (hs : MeasurableSet s) (hC : MeasurableSet C) :
    plan ((Prod.fst ⁻¹' C) ∆ (Prod.fst ⁻¹' s)) = μ (C ∆ s) := by
  rw [← preimage_symmDiff, ← Measure.map_apply measurable_fst (hC.symmDiff hs), hplan]

/-- A single finite cube approximation works simultaneously for the two
unchanged original conditional clock kernels. Their spatial coordinates are
not replaced, nor is their dependence on the original label removed. -/
theorem exists_grid_cubes_approx_original_clock_laws
    {ι Y : Type*} [Fintype ι] [MeasurableSpace Y]
    (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (clock : Fin 2 → ProbabilityTheory.Kernel (ι → ℝ) Y)
    [∀ color, ProbabilityTheory.IsMarkovKernel (clock color)]
    {s V : Set (ι → ℝ)} (hs : MeasurableSet s) (hV : IsOpen V) (hsV : s ⊆ V)
    {ε : ℝ≥0∞} (hε : 0 < ε) {mesh : ℝ} (hmesh : 0 < mesh) :
    ∃ n : ℕ, ∃ hn : NeZero n, ∃ F : Finset (ι → ℤ),
      (1 / (n : ℝ) < mesh) ∧
      Set.PairwiseDisjoint (↑F : Set (ι → ℤ))
        (fun ν ↦ ((unitPartition.box n ν) : Set (ι → ℝ))) ∧
      (⋃ ν ∈ F, ((unitPartition.box n ν) : Set (ι → ℝ))) ⊆ V ∧
      ∀ color : Fin 2,
        (μ.compProd (clock color))
          ((Prod.fst ⁻¹' (⋃ ν ∈ F, ((unitPartition.box n ν) : Set (ι → ℝ)))) ∆
            (Prod.fst ⁻¹' s)) < ε := by
  classical
  obtain ⟨n, hn, F, hnm, hdisj, hsub, hsmall⟩ :=
    exists_finite_disjoint_grid_cubes_approx_inside_open μ hs hV hsV hε hmesh
  refine ⟨n, hn, F, hnm, hdisj, hsub, fun color ↦ ?_⟩
  have hC : MeasurableSet (⋃ ν ∈ F, ((unitPartition.box n ν) : Set (ι → ℝ))) :=
    MeasurableSet.iUnion fun ν ↦
      MeasurableSet.iUnion fun _ ↦ (unitPartition.box n ν).measurableSet_coe
  rw [← preimage_symmDiff, ← Measure.fst_apply (hC.symmDiff hs), Measure.fst_compProd]
  exact hsmall

/-- Restricting an original legal joint law to the retained actual labels
preserves legality. The cube approximation changes only the retained label
set and its loss is measured in that same original joint law. -/
theorem exists_grid_cubes_approx_original_legal_plan
    {ι Y : Type*} [Fintype ι] [MeasurableSpace Y]
    (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (plan : Measure ((ι → ℝ) × Y)) (hplan : plan.map Prod.fst = μ)
    {Legal : ((ι → ℝ) × Y) → Prop} (hlegal : ∀ᵐ p ∂plan, Legal p)
    {s V : Set (ι → ℝ)} (hs : MeasurableSet s) (hV : IsOpen V) (hsV : s ⊆ V)
    {ε : ℝ≥0∞} (hε : 0 < ε) {mesh : ℝ} (hmesh : 0 < mesh) :
    ∃ n : ℕ, ∃ hn : NeZero n, ∃ F : Finset (ι → ℤ),
      (1 / (n : ℝ) < mesh) ∧
      Set.PairwiseDisjoint (↑F : Set (ι → ℤ))
        (fun ν ↦ ((unitPartition.box n ν) : Set (ι → ℝ))) ∧
      (⋃ ν ∈ F, ((unitPartition.box n ν) : Set (ι → ℝ))) ⊆ V ∧
      plan ((Prod.fst ⁻¹' (⋃ ν ∈ F, ((unitPartition.box n ν) : Set (ι → ℝ)))) ∆
          (Prod.fst ⁻¹' s)) < ε ∧
      (∀ᵐ p ∂plan.restrict (Prod.fst ⁻¹'
        (s ∩ (⋃ ν ∈ F, ((unitPartition.box n ν) : Set (ι → ℝ))))), Legal p) := by
  classical
  obtain ⟨n, hn, F, hnm, hdisj, hsub, hsmall⟩ :=
    exists_finite_disjoint_grid_cubes_approx_inside_open μ hs hV hsV hε hmesh
  have hC : MeasurableSet (⋃ ν ∈ F, ((unitPartition.box n ν) : Set (ι → ℝ))) :=
    MeasurableSet.iUnion fun ν ↦
      MeasurableSet.iUnion fun _ ↦ (unitPartition.box n ν).measurableSet_coe
  refine ⟨n, hn, F, hnm, hdisj, hsub, ?_, ae_restrict_of_ae hlegal⟩
  rw [root_shape_mismatch_mass_eq μ plan hplan hs hC]
  exact hsmall


/-- Measurable seed coordinates transport the finite-cube approximation back
to the unchanged original labels. The retained cells are literal inverse
images of the disjoint coordinate cubes; their original mass error is small. -/
theorem exists_grid_cubes_approx_original_labels
    {Z ι : Type*} [MeasurableSpace Z] [Fintype ι]
    (μ : Measure Z) [IsFiniteMeasure μ] (coord : Z → (ι → ℝ))
    (hcoord : MeasurableEmbedding coord)
    {s : Set Z} (hs : MeasurableSet s) {V : Set (ι → ℝ)}
    (hV : IsOpen V) (hsV : coord '' s ⊆ V)
    {ε : ℝ≥0∞} (hε : 0 < ε) {mesh : ℝ} (hmesh : 0 < mesh) :
    ∃ n : ℕ, ∃ hn : NeZero n, ∃ F : Finset (ι → ℤ),
      (1 / (n : ℝ) < mesh) ∧
      Set.PairwiseDisjoint (↑F : Set (ι → ℤ))
        (fun ν ↦ coord ⁻¹' ((unitPartition.box n ν) : Set (ι → ℝ))) ∧
      (⋃ ν ∈ F, coord ⁻¹' ((unitPartition.box n ν) : Set (ι → ℝ))) ⊆ coord ⁻¹' V ∧
      μ ((⋃ ν ∈ F, coord ⁻¹' ((unitPartition.box n ν) : Set (ι → ℝ))) ∆ s) < ε := by
  classical
  obtain ⟨n, hn, F, hnm, hdisj, hsub, hsmall⟩ :=
    exists_finite_disjoint_grid_cubes_approx_inside_open (μ.map coord)
      (hcoord.measurableSet_image.mpr hs) hV hsV hε hmesh
  refine ⟨n, hn, F, hnm, ?_, ?_, ?_⟩
  · intro ν hν ν' hν' hne
    exact Set.disjoint_left.mpr fun x hx hx' ↦ Set.disjoint_left.mp
      (hdisj hν hν' hne) hx hx'
  · intro x hx
    obtain ⟨ν, hν, hxν⟩ := mem_iUnion₂.mp hx
    exact hsub (mem_iUnion₂.mpr ⟨ν, hν, hxν⟩)
  · have hC : MeasurableSet (⋃ ν ∈ F, ((unitPartition.box n ν) : Set (ι → ℝ))) :=
      MeasurableSet.iUnion fun ν ↦
        MeasurableSet.iUnion fun _ ↦ (unitPartition.box n ν).measurableSet_coe
    rw [Measure.map_apply hcoord.measurable (hC.symmDiff
      (hcoord.measurableSet_image.mpr hs)), preimage_symmDiff,
      hcoord.injective.preimage_image, preimage_iUnion] at hsmall
    simpa only [preimage_iUnion] using hsmall

end OTSelector.Reconstruction
