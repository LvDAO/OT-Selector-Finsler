import OTSelector.Reconstruction.FinslerOriginalRetainedClockLaw
import OTSelector.Probability.CellwisePopulation

/-! Literal original continuous clock masks are measurable retained subkernels.
No selection of conditional probability laws is made. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The exact scalar pair event of an original finite clock mask. -/
def FiniteScalarBins.originalClockMaskSet {range : Set ℝ} {width : ℝ}
    (Q : FiniteScalarBins range width) (allowed : Fin Q.count → Fin Q.count → Prop) : Set (ℝ × ℝ) :=
  {p | ∃ i j, allowed i j ∧ p.1 ∈ Q.cell i ∧ p.2 ∈ Q.cell j}

/-- The original finite mask is Borel, including all original bin boundaries. -/
theorem FiniteScalarBins.measurableSet_originalClockMaskSet {range : Set ℝ} {width : ℝ}
    (Q : FiniteScalarBins range width) (allowed : Fin Q.count → Fin Q.count → Prop) :
    MeasurableSet (Q.originalClockMaskSet allowed) := by
  simp only [FiniteScalarBins.originalClockMaskSet,ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  by_cases h : allowed i j
  · have heq : {p : ℝ × ℝ | allowed i j ∧ p.1 ∈ Q.cell i ∧ p.2 ∈ Q.cell j} =
        Q.cell i ×ˢ Q.cell j := by
      ext p
      simp only [mem_ofPred_eq,h,true_and,mem_prod]
    rw [heq]
    exact (Q.measurable_cell i).prod (Q.measurable_cell j)
  · simp only [h,false_and,ofPred_false]
    exact MeasurableSet.empty

/-- The real-clock mask is exactly the original range-lift mask. -/
theorem FiniteScalarBins.preimage_originalClockMaskSet {range : Set ℝ} {width : ℝ}
    (Q : FiniteScalarBins range width) (allowed : Fin Q.count → Fin Q.count → Prop) :
    (Prod.map Subtype.val Subtype.val : range × range → ℝ × ℝ) ⁻¹'
      Q.originalClockMaskSet allowed = {p | allowed (Q.rangeClassify p.1) (Q.rangeClassify p.2)} := by
  ext p
  change (∃ i j, allowed i j ∧ p.1.val ∈ Q.cell i ∧ p.2.val ∈ Q.cell j) ↔ allowed (Q.rangeClassify p.1) (Q.rangeClassify p.2)
  constructor
  · rintro ⟨i,j,hij,hi,hj⟩
    have hI := (Q.rangeClassify_eq_iff p.1 i).mpr hi
    have hJ := (Q.rangeClassify_eq_iff p.2 j).mpr hj
    simpa only [hI,hJ] using hij
  · intro h
    exact ⟨Q.rangeClassify p.1,Q.rangeClassify p.2,h,Q.rangeClassify_mem p.1,Q.rangeClassify_mem p.2⟩

/-- Retained mass is exact under the original scalar-range coordinate lift. -/
theorem FiniteScalarBins.real_restrict_originalClockMaskSet_eq
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (allowed : Fin Q.count → Fin Q.count → Prop) (π : Measure (range × range)) :
    ((π.map (Prod.map Subtype.val Subtype.val)).restrict (Q.originalClockMaskSet allowed)).real univ =
      (π.restrict {p | allowed (Q.rangeClassify p.1) (Q.rangeClassify p.2)}).real univ := by
  rw [Measure.restrict_map (measurable_subtype_coe.prodMap measurable_subtype_coe)
    (Q.measurableSet_originalClockMaskSet allowed),Q.preimage_originalClockMaskSet]
  exact map_measureReal_apply (measurable_subtype_coe.prodMap measurable_subtype_coe) MeasurableSet.univ

/-- Each original population core retains its literal masked continuous pair
law. The finite measurable disjoint original root cells choose the same kernel. -/
def originalFiniteClockMaskPairKernel
    {C Z : Type*} [Fintype C] [MeasurableSpace Z]
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    {range : Set ℝ} {width : C → ℝ} (Q : ∀ c, FiniteScalarBins range (width c))
    (allowed : ∀ c, Fin (Q c).count → Fin (Q c).count → Prop)
    (γ : Kernel Z (ℝ × ℝ)) : Kernel Z (ℝ × ℝ) :=
  finiteCellPairKernel cell hcell (fun c ↦ γ.restrict ((Q c).measurableSet_originalClockMaskSet (allowed c)))

/-- The literal retained kernel equals its exact original restriction on an
active original cell and is dominated by the same original conditional law. -/
theorem originalFiniteClockMaskPairKernel_eq_on_cell
    {C Z : Type*} [Fintype C] [MeasurableSpace Z]
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    {range : Set ℝ} {width : C → ℝ} (Q : ∀ c, FiniteScalarBins range (width c))
    (allowed : ∀ c, Fin (Q c).count → Fin (Q c).count → Prop)
    (γ : Kernel Z (ℝ × ℝ)) (c : C) (z : Z) (hz : z ∈ cell c) :
    originalFiniteClockMaskPairKernel cell hcell Q allowed γ z =
      (γ z).restrict ((Q c).originalClockMaskSet (allowed c)) :=
  finiteCellPairKernel_eq cell hcell hdisj _ c hz

theorem originalFiniteClockMaskPairKernel_le
    {C Z : Type*} [Fintype C] [MeasurableSpace Z]
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    {range : Set ℝ} {width : C → ℝ} (Q : ∀ c, FiniteScalarBins range (width c))
    (allowed : ∀ c, Fin (Q c).count → Fin (Q c).count → Prop)
    (γ : Kernel Z (ℝ × ℝ)) (z : Z) :
    originalFiniteClockMaskPairKernel cell hcell Q allowed γ z ≤ γ z := by
  by_cases hz : z ∈ ⋃ c, cell c
  · obtain ⟨c,hc⟩ := mem_iUnion.mp hz
    rw [originalFiniteClockMaskPairKernel_eq_on_cell cell hcell hdisj Q allowed γ c z hc]
    exact Measure.restrict_le_self
  · have heq : originalFiniteClockMaskPairKernel cell hcell Q allowed γ z = 0 :=
      finiteCellPairKernel_eq_zero cell hcell _ hz
    rw [heq]
    exact bot_le

end OTSelector.Reconstruction
