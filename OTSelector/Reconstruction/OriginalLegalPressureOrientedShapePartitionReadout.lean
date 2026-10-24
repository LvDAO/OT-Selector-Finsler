import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapePartitionExpectation
import OTSelector.Reconstruction.MarkedStationaryValueLegalShape
import OTSelector.Reconstruction.MarkedStationaryValueLegalEmbedding

/-! Spatial cell optima are literal original Poisson shape restrictions. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {q : ℕ}

private theorem mem_range_shapeCloudEmbedding (S : Set (Fin q → ℝ))
    (z : MarkedCloudSpace q ℝ) (i : Fin z.1) (hi : (z.2 i).1 ∈ S) :
    i ∈ range (shapeCloudEmbedding S z) := by
  have him : i ∈ shapeCloudIndices S z := by
    simp only [shapeCloudIndices,Finset.mem_filter,Finset.mem_univ,true_and,
      shapeCloudLabel,hi,↓reduceIte]
  let a : shapeCloudIndices S z := ⟨i,him⟩
  refine ⟨((shapeCloudIndices S z).orderIsoOfFin rfl).symm a, ?_⟩
  change (((shapeCloudIndices S z).orderIsoOfFin rfl)
    (((shapeCloudIndices S z).orderIsoOfFin rfl).symm a)).val = i
  rw [OrderIso.apply_symm_apply]

/-- Re-enumerating one actual cell changes neither its true legal rank nor
its signed optimum; repeated physical points and empty cells are retained. -/
theorem originalOrientedShapeCellValue_eq_shapeLegalMarkedTilted
    {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (cell : (Fin q → ℝ) → Cell) (b : Cell) (r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    originalOrientedShapeCellValue cell b r kin g t ω =
      shapeLegalMarkedTilted q id id (cell ⁻¹' {b}) r kin g t ω := by
  let S := cell ⁻¹' {b}
  let e := shapeCloudEmbedding S ω.1
  let f := shapeCloudEmbedding S ω.2
  let allowed := spatialLegalMarkedGraph q (mSourceCount ω) (mTargetCount ω) cell id id b ω
  let cost := fun i : Fin (mSourceCount ω) ↦ fun j : Fin (mTargetCount ω) ↦
    mKineticCost q r kin ω i j+t*mProbe g ω i j
  have hcarry : ∀ p ∈ allowed, p.1 ∈ range e ∧ p.2 ∈ range f := by
    intro p hp
    have h := (Finset.mem_filter.mp hp).2
    exact ⟨mem_range_shapeCloudEmbedding S ω.1 p.1 h.1,
      mem_range_shapeCloudEmbedding S ω.2 p.2 h.2⟩
  change PartialMatching.legalMaximumValue allowed cost = _
  rw [← PartialMatching.legalMaximumValue_inducedLegalGraph allowed e f hcarry cost]
  have hg : PartialMatching.inducedLegalGraph allowed e f =
      scalarClockLegalGraph (fun i ↦ (shapeCloud S ω.1).2 i |>.2)
        (fun j ↦ (shapeCloud S ω.2).2 j |>.2) := by
    ext p
    have hs := shapeCloudEmbedding_mem S ω.1 p.1
    have ht := shapeCloudEmbedding_mem S ω.2 p.2
    change cell (mSourcePoint ω (e p.1)) = b at hs
    change cell (mTargetPoint ω (f p.2)) = b at ht
    dsimp only [e] at hs
    dsimp only [f] at ht
    simp only [PartialMatching.inducedLegalGraph,allowed,spatialLegalMarkedGraph,
      PartialMatching.spatialLegalBlock,legalMarkedGraph,scalarClockLegalGraph,
      Finset.mem_filter,Finset.mem_univ,true_and,shapeCloud_point,
      mSourceMark,mTargetMark,id_eq,e,f]
    exact ⟨fun h ↦ h.1,fun h ↦ ⟨h,hs,ht⟩⟩
  rw [hg]
  unfold shapeLegalMarkedTilted blockLegalTilted
  simp only [shapeCloud_point]
  rfl


/-- The true native pressure splits into the actual inner shape, its literal
complementary hole, and only an original square-root Hall repair budget. -/
theorem FiniteScalarBins.legalMarkedPressure_le_shape_and_complement
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (hIm : MeasurableSet I) (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hπ : Vlasov.IsCoupling π α β) (hI : ∀ᵐ p ∂π, p.1 ∈ I ∧ p.2 ∈ I)
    (hforward : ∀ᵐ p ∂π, gap ≤ p.2-p.1)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |p.2-p.1|)
    (q : ℕ) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S) (r : ℝ≥0)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkb : ∀ a d v, |kin a d v| ≤ C*∑ l, v l^2)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a d, |g a d| ≤ G) (t : ℝ) :
    legalMarkedPressure q id id α β r kin g t ≤
      (∫ ω, shapeLegalMarkedTilted q id id S r kin g t ω ∂twoMarkedCloudLaw q ℝ ℝ α β r) +
      (∫ ω, shapeLegalMarkedTilted q id id Sᶜ r kin g t ω ∂twoMarkedCloudLaw q ℝ ℝ α β r) +
      Real.sqrt (2*(r : ℝ)*(2*(D.count*D.count+1))) *
        (2*((D.count : ℝ)+1)*((r : ℝ)^(2/(q : ℝ))*(C*q)+|t| * G)) := by
  let cell : (Fin q → ℝ) → Bool := fun x ↦ if x ∈ S then true else false
  have hc : Measurable cell := measurable_const.ite hS measurable_const
  have ht : cell ⁻¹' {true} = S := by ext x; simp [cell]
  have hf : cell ⁻¹' {false} = Sᶜ := by ext x; simp [cell]
  have h := D.legalMarkedPressure_le_spatial_cells hgap hIm π α β hπ hI hforward hsep
    q cell hc r hC hG hk hkb hg hgb t
  simp_rw [originalOrientedShapeCellValue_eq_shapeLegalMarkedTilted] at h
  simpa only [Fintype.sum_bool,ht,hf,Fintype.card_bool,Nat.cast_ofNat,add_comm] using h

end OTSelector.Reconstruction
