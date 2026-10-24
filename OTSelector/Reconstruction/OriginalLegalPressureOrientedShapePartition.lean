import OTSelector.Reconstruction.MarkedStationaryValueLegalSpatialTypesOriginal
import OTSelector.Reconstruction.MarkedStationaryValueLegalScalarRepair
import OTSelector.Reconstruction.MarkedStationaryValueLegalCloud
import OTSelector.Reconstruction.MarkedStationaryValueLegalRegularity

/-! Actual original-index legal optima on arbitrary finite spatial partitions. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {q : ℕ} {Cell : Type*} [Fintype Cell] [DecidableEq Cell]

private def originalOrientedShapeFixedCellValue (m n : ℕ)
    (cell : (Fin q → ℝ) → Cell) (b : Cell)
    (r : ℝ) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) : ℝ :=
  PartialMatching.legalMaximumValue (spatialLegalMarkedGraph q m n cell id id b ω)
    (fun i j ↦ mKineticCost q r kin ω i j+t*mProbe g ω i j)

/-- The true maximum-cardinality legal optimum within one spatial cell. All
edges retain their original whole-cloud source and target indices. -/
def originalOrientedShapeCellValue (cell : (Fin q → ℝ) → Cell) (b : Cell)
    (r : ℝ) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) : ℝ :=
  originalOrientedShapeFixedCellValue (mSourceCount ω) (mTargetCount ω) cell b r kin g t ω

variable [MeasurableSpace Cell] [MeasurableSingletonClass Cell]

theorem measurable_originalOrientedShapeCellValue
    {cell : (Fin q → ℝ) → Cell} (hcell : Measurable cell) (b : Cell)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (r t : ℝ) :
    Measurable (originalOrientedShapeCellValue cell b r kin g t) := by
  have hfixed (m n : ℕ) :
      Measurable (originalOrientedShapeFixedCellValue m n cell b r kin g t) := by
    apply PartialMatching.measurable_legalMaximumValue
      (spatialLegalMarkedGraph q m n cell id id b)
      (measurableSet_spatialLegalMarkedGraph_eq q m n hcell measurable_id measurable_id b)
    intro i j
    exact (measurable_mKineticCost q r hk i j).add
      ((measurable_mProbe q hg i j).const_mul t)
  intro S hS
  have hpre : (originalOrientedShapeCellValue cell b r kin g t) ⁻¹' S =
      ⋃ m : ℕ, ⋃ n : ℕ,
        ({ω : TwoMarkedCloudSpace q ℝ ℝ | mSourceCount ω = m} ∩
          {ω | mTargetCount ω = n}) ∩
        (originalOrientedShapeFixedCellValue m n cell b r kin g t) ⁻¹' S := by
    ext ω
    simp only [mem_preimage,mem_iUnion,mem_inter_iff,mem_ofPred_eq]
    constructor
    · intro hω
      exact ⟨mSourceCount ω,mTargetCount ω,⟨rfl,rfl⟩,hω⟩
    · rintro ⟨m,n,⟨hm,hn⟩,hω⟩
      simpa only [originalOrientedShapeCellValue,hm,hn] using hω
  rw [hpre]
  exact MeasurableSet.iUnion fun m ↦ MeasurableSet.iUnion fun n ↦
    ((measurableSet_eq_fun (measurable_mSourceCount q) measurable_const).inter
      (measurableSet_eq_fun (measurable_mTargetCount q) measurable_const)).inter
      (hfixed m n hS)

/-- Poisson first moments give L1 of each signed actual cell optimum. -/
theorem integrable_originalOrientedShapeCellValue
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {cell : (Fin q → ℝ) → Cell} (hcell : Measurable cell) (b : Cell)
    (r : ℝ≥0) {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkb : ∀ a d v, |kin a d v| ≤ C*∑ l, v l^2)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a d, |g a d| ≤ G) (t : ℝ) :
    Integrable (originalOrientedShapeCellValue cell b r kin g t)
      (twoMarkedCloudLaw q ℝ ℝ α β r) := by
  let B := (r : ℝ)^(2/(q : ℝ))*(C*q)+|t| * G
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ((integrable_mSourceCount q α β r).mul_const B).mono'
    (measurable_originalOrientedShapeCellValue hcell b hk hg r t).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact (PartialMatching.abs_legalMaximumValue_le_of_allowed _ _
    (fun i j _ ↦ abs_legalMarkedEdge_le q r.coe_nonneg hC hkb hgb t ω i j)).trans
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr
      ((PartialMatching.legalMaximumCard_le_min _).trans (min_le_left _ _))) hB)

omit [MeasurableSpace Cell] [MeasurableSingletonClass Cell] in
/-- Actual scalar-bin augmentation glues arbitrary original-index cell optima.
The repair uses their literal Hall deficiencies, including empty cells. -/
theorem FiniteScalarBins.legalMarkedTilted_le_spatial_cells
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (cell : (Fin q → ℝ) → Cell) {r C G : ℝ} (hr : 0 ≤ r)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hkb : ∀ a d v, |kin a d v| ≤ C*∑ l, v l^2)
    (g : ℝ → ℝ → ℝ) (hgb : ∀ a d, |g a d| ≤ G) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ)
    (hsource : ∀ i : Fin (mSourceCount ω), mSourceMark ω i ∈ I)
    (hsep : ∀ (i : Fin (mSourceCount ω)) (j : Fin (mTargetCount ω)),
      gap ≤ |mTargetMark ω j-mSourceMark ω i|) :
    legalMarkedTilted q id id r kin g t ω ≤
      (∑ b : Cell, originalOrientedShapeCellValue cell b r kin g t ω) +
      spatialLegalMarkedSourceDefectSum q cell id id ω *
        (2*((D.count : ℝ)+1)*(r^(2/(q : ℝ))*(C*q)+|t| * G)) := by
  let allowed := legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω
  let s := fun i : Fin (mSourceCount ω) ↦ cell (mSourcePoint ω i)
  let u := fun j : Fin (mTargetCount ω) ↦ cell (mTargetPoint ω j)
  let block := fun b ↦ PartialMatching.spatialLegalBlock allowed s u b
  let B := r^(2/(q : ℝ))*(C*q)+|t| * G
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hv := D.legalMaximumValue_le_sum_blocks_add_deficit hgap
    (fun i ↦ mSourceMark ω i) (fun j ↦ mTargetMark ω j) hsource hsep block
    (fun _ ↦ Finset.filter_subset _ _)
    (PartialMatching.spatialLegalBlock_pairwise_rows allowed s u)
    (PartialMatching.spatialLegalBlock_pairwise_cols allowed s u)
    (fun i j ↦ mKineticCost q r kin ω i j+t*mProbe g ω i j) hB
    (fun i j ↦ abs_legalMarkedEdge_le q hr hC hkb hgb t ω i j)
  have hsum := PartialMatching.sum_spatialLegalBlock_card_le allowed s u
  have hcard := (PartialMatching.legalMaximumCard_le_min allowed).trans (min_le_left _ _)
  have hdef : (((PartialMatching.legalMaximumCard allowed-∑ b, PartialMatching.legalMaximumCard
      (block b) : ℕ) : ℝ)) ≤ spatialLegalMarkedSourceDefectSum q cell id id ω := by
    rw [Nat.cast_sub hsum,Nat.cast_sum]
    change (PartialMatching.legalMaximumCard allowed : ℝ)-_ ≤ (mSourceCount ω : ℝ)-_
    have hcR : (PartialMatching.legalMaximumCard allowed : ℝ) ≤ (mSourceCount ω : ℝ) :=
      Nat.cast_le.mpr hcard
    exact sub_le_sub_right hcR _
  have hcoef : (2*(D.count : ℝ)-1)*B ≤ 2*((D.count : ℝ)+1)*B := by nlinarith
  have hδ : 0 ≤ ((PartialMatching.legalMaximumCard allowed-∑ b,
      PartialMatching.legalMaximumCard (block b) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hfinal := (mul_le_mul_of_nonneg_left hcoef hδ).trans
    (mul_le_mul_of_nonneg_right hdef (by positivity : 0 ≤ 2*((D.count : ℝ)+1)*B))
  exact hv.trans (add_le_add le_rfl hfinal)

end OTSelector.Reconstruction
