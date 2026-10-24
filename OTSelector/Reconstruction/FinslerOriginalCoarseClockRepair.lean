import OTSelector.Reconstruction.FinslerOriginalScalarRangeClockModel
import OTSelector.Reconstruction.MarkedStationaryValueLegalScalarRepair

/-! One fixed coarse scalar partition controls exact legal source
neighborhoods of arbitrarily fine original coefficient bins, on the actual
separated original clock populations and their retained outer interval. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-- The original scalar order, retaining both actual outer-window endpoints. -/
def screenedScalarClockLegalGraph {m n : ℕ} (outer : Set ℝ)
    (source : Fin m → ℝ) (target : Fin n → ℝ) : Finset (Fin m × Fin n) :=
  Finset.univ.filter (fun e ↦ source e.1 ∈ outer ∧ target e.2 ∈ outer ∧ source e.1 < target e.2)

/-- One fixed coarse bin and one outer-window flag determine all legal target
neighbors in the original separated clock populations. The number of source
classes is twice the coarse count, independently of any finer cost bins. -/
theorem FiniteScalarBins.exists_screened_source_neighborhood_classes
    {range : Set ℝ} {gap : ℝ} (coarse : FiniteScalarBins range gap) (hgap : 0 < gap)
    (outer : Set ℝ) {m n : ℕ} (source : Fin m → range) (target : Fin n → range)
    (hsep : ∀ i j, gap ≤ |(target j).val - (source i).val|) :
    ∃ label : Fin m → Fin coarse.count × Bool,
      ∃ allows : (Fin coarse.count × Bool) → Fin n → Prop,
      ∀ i j, (i,j) ∈ screenedScalarClockLegalGraph outer
          (fun i ↦ (source i).val) (fun j ↦ (target j).val) ↔ allows (label i) j := by
  classical
  let label := fun i ↦ (coarse.rangeClassify (source i),decide ((source i).val ∈ outer))
  let allows := fun a j ↦ a.2 = true ∧ (target j).val ∈ outer ∧
    ∃ i, label i = a ∧ (source i).val < (target j).val
  have hsame i i' (heq : label i = label i') j :
      (source i).val < (target j).val ↔ (source i').val < (target j).val := by
    apply scalar_forward_iff_of_close_sources _ (hsep i j) (hsep i' j)
    have hbin := congrArg Prod.fst heq
    change coarse.rangeClassify (source i) = coarse.rangeClassify (source i') at hbin
    have hd := coarse.diameter (coarse.rangeClassify (source i)) (source i).val
      (coarse.rangeClassify_mem (source i)) (source i').val
      (hbin.symm ▸ coarse.rangeClassify_mem (source i'))
    linarith
  refine ⟨label,allows,?_⟩
  intro i j
  simp only [screenedScalarClockLegalGraph,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hi,hj,horder⟩
    exact ⟨by simpa only [label,decide_eq_true_eq] using hi,hj,⟨i,rfl,horder⟩⟩
  · rintro ⟨hi,hj,i',heq,horder⟩
    exact ⟨by simpa only [label,decide_eq_true_eq] using hi,hj,(hsame i' i heq j).mp horder⟩

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- On the original absolutely separated populations, the produced fine mask
is exactly scalar order inside its retained original outer interval. -/
theorem OriginalPopulationCoefficientCore.fine_clock_mask_iff_screened_order
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width gap : ℝ} (fine : FiniteScalarBins range width)
    (hwindowGap : (C.window.val.2.2 : ℝ) ≤ gap)
    (hfull : ∀ i j, C.clockClassAllowed fine i j →
      ∀ x ∈ fine.cell i, ∀ y ∈ fine.cell j,
        x ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
        y ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧ x < y)
    (x y : range) (hsep : gap ≤ |y.val - x.val|) :
    C.clockClassAllowed fine (fine.rangeClassify x) (fine.rangeClassify y) ↔
      x.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
      y.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧ x.val < y.val := by
  constructor
  · exact fun h ↦ hfull _ _ h _ (fine.rangeClassify_mem x) _ (fine.rangeClassify_mem y)
  · rintro ⟨hx,hy,hxy⟩
    have hg : (C.window.val.2.2 : ℝ) ≤ y.val - x.val := by
      rw [abs_of_pos (sub_pos.mpr hxy)] at hsep
      exact hwindowGap.trans hsep
    exact ⟨(x.val,y.val),⟨⟨hx,hy⟩,hg⟩,fine.rangeClassify_mem x,fine.rangeClassify_mem y⟩

/-- The same original fine graph admits a source-neighborhood description
with twice the fixed coarse count. Its reconfiguration constant therefore
does not grow when the original coefficient bins are refined. -/
theorem OriginalPopulationCoefficientCore.exists_fine_clock_mask_coarse_source_classes
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width gap : ℝ} (fine : FiniteScalarBins range width)
    (coarse : FiniteScalarBins range gap) (hgap : 0 < gap)
    (hwindowGap : (C.window.val.2.2 : ℝ) ≤ gap)
    (hfull : ∀ i j, C.clockClassAllowed fine i j →
      ∀ x ∈ fine.cell i, ∀ y ∈ fine.cell j,
        x ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
        y ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧ x < y)
    {m n : ℕ} (source : Fin m → range) (target : Fin n → range)
    (hsep : ∀ i j, gap ≤ |(target j).val - (source i).val|) :
    ∃ label : Fin m → Fin coarse.count × Bool,
      ∃ allows : (Fin coarse.count × Bool) → Fin n → Prop,
      ∀ i j, C.clockClassAllowed fine (fine.rangeClassify (source i))
        (fine.rangeClassify (target j)) ↔ allows (label i) j := by
  obtain ⟨label,allows,hclasses⟩ := coarse.exists_screened_source_neighborhood_classes hgap
    (Icc (C.window.val.1 : ℝ) C.window.val.2.1) source target hsep
  refine ⟨label,allows,?_⟩
  intro i j
  rw [C.fine_clock_mask_iff_screened_order fine hwindowGap hfull _ _ (hsep i j)]
  simpa only [screenedScalarClockLegalGraph,Finset.mem_filter,Finset.mem_univ,true_and]
    using hclasses i j


/-- Actual parent reconfiguration for the unchanged fine graph pays a fixed
coarse constant. The displayed bound is independent of the fine bin count,
clock laws, samples, and the chosen legal child blocks. -/
theorem OriginalPopulationCoefficientCore.legalMaximumValue_le_sum_blocks_add_coarse_deficit
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width gap : ℝ} (fine : FiniteScalarBins range width)
    (coarse : FiniteScalarBins range gap) (hgap : 0 < gap)
    (hwindowGap : (C.window.val.2.2 : ℝ) ≤ gap)
    (hfull : ∀ i j, C.clockClassAllowed fine i j →
      ∀ x ∈ fine.cell i, ∀ y ∈ fine.cell j,
        x ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
        y ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧ x < y)
    {m n : ℕ} (source : Fin m → range) (target : Fin n → range)
    (hsep : ∀ i j, gap ≤ |(target j).val - (source i).val|)
    (allowed : Finset (Fin m × Fin n))
    (hallowed : ∀ i j, (i,j) ∈ allowed ↔ C.clockClassAllowed fine
      (fine.rangeClassify (source i)) (fine.rangeClassify (target j)))
    {BType : Type*} [Fintype BType] (block : BType → Finset (Fin m × Fin n))
    (hsub : ∀ b, block b ⊆ allowed)
    (hrows : Pairwise (fun b b' ↦ Disjoint ((block b).image Prod.fst) ((block b').image Prod.fst)))
    (hcols : Pairwise (fun b b' ↦ Disjoint ((block b).image Prod.snd) ((block b').image Prod.snd)))
    (c : Fin m → Fin n → ℝ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i j, |c i j| ≤ B) :
    PartialMatching.legalMaximumValue allowed c ≤
      (∑ b, PartialMatching.legalMaximumValue (block b) c) +
        ((PartialMatching.legalMaximumCard allowed -
          ∑ b, PartialMatching.legalMaximumCard (block b) : ℕ) : ℝ) *
            ((4 * (coarse.count : ℝ) - 1) * B) := by
  obtain ⟨label,allows,hclasses⟩ := C.exists_fine_clock_mask_coarse_source_classes fine
    coarse hgap hwindowGap hfull source target hsep
  have hb := PartialMatching.legalMaximumValue_le_sum_blocks_add_class_deficit allowed
    block hsub hrows hcols label allows (fun i j ↦ (hallowed i j).trans (hclasses i j)) c hB0 hB
  have hcoeff : 2 * (Fintype.card (Fin coarse.count × Bool) : ℝ) - 1 =
      4 * (coarse.count : ℝ) - 1 := by
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat]
    ring
  simpa only [hcoeff] using hb


/-- One actual compact coefficient bound works simultaneously for every
subsequent scalar partition. It therefore stays fixed when coefficient bins
are refined or the original conditional laws are varied. -/
theorem OriginalPopulationCoefficientCore.exists_all_clockClassKinetic_bound
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) :
    ∃ K ≥ 0, ∀ {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width),
      ∀ i j v, |C.clockClassKinetic Q z₀ i j v| ≤ K * ∑ l, v l ^ 2 := by
  classical
  have hc : ContinuousOn (C.matrix z₀) C.window.region :=
    C.coefficient_continuous.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun p hp ↦ ⟨hz₀,hp⟩)
  obtain ⟨K,hK,hbound⟩ := exists_compact_matrixQuadratic_sum_bound C.window.isCompact_region hc
  refine ⟨K,hK,fun Q i j v ↦ ?_⟩
  by_cases h : C.clockClassAllowed Q i j
  · simpa only [OriginalPopulationCoefficientCore.clockClassKinetic,
      OriginalPopulationCoefficientCore.clockClassMatrix,ite_eq_left h] using
      hbound _ (C.clockClassReference_mem Q h).1 v
  · simp only [OriginalPopulationCoefficientCore.clockClassKinetic,
      OriginalPopulationCoefficientCore.clockClassMatrix,ite_eq_right h,matrixQuadratic,
      Matrix.zero_mulVec,dotProduct_zero,mul_zero,abs_zero]
    exact mul_nonneg hK (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

end OTSelector.Reconstruction
