import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapePartition
import OTSelector.Reconstruction.MarkedStationaryValueLegalDyadicComparison

/-! True original Poisson expectations of finite spatial legal decompositions. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Every finite measurable spatial partition has a true original-cloud legal
pressure bound. Its actual local optima and Hall defects are produced internally;
no spatial volume balance or coefficient lower bound is needed. -/
theorem FiniteScalarBins.legalMarkedPressure_le_spatial_cells
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (hIm : MeasurableSet I) (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hπ : Vlasov.IsCoupling π α β) (hI : ∀ᵐ p ∂π, p.1 ∈ I ∧ p.2 ∈ I)
    (hforward : ∀ᵐ p ∂π, gap ≤ p.2-p.1)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |p.2-p.1|)
    (q : ℕ) {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    (cell : (Fin q → ℝ) → Cell) (hcell : Measurable cell) (r : ℝ≥0)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkb : ∀ a d v, |kin a d v| ≤ C*∑ l, v l^2)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a d, |g a d| ≤ G) (t : ℝ) :
    legalMarkedPressure q id id α β r kin g t ≤
      (∑ b : Cell, ∫ ω, originalOrientedShapeCellValue cell b r kin g t ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β r) +
      Real.sqrt (2*(r : ℝ)*(Fintype.card Cell*(D.count*D.count+1))) *
        (2*((D.count : ℝ)+1)*((r : ℝ)^(2/(q : ℝ))*(C*q)+|t| * G)) := by
  let : MeasurableSpace (Option (Unit × Fin D.count × Fin D.count)) := ⊤
  let : MeasurableSingletonClass (Option (Unit × Fin D.count × Fin D.count)) := ⟨fun _ ↦ trivial⟩
  have hdef := scalarBinPopulationTypes_poisson_spatialSourceDefect D hgap
    (fun _ : ℝ × ℝ ↦ ()) id id π α β hπ measurable_const measurable_id measurable_id
    hI hforward q cell hcell r
  let P := twoMarkedCloudLaw q ℝ ℝ α β r
  let B := 2*((D.count : ℝ)+1)*((r : ℝ)^(2/(q : ℝ))*(C*q)+|t| * G)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hlocal (b : Cell) : Integrable (originalOrientedShapeCellValue cell b r kin g t) P :=
    integrable_originalOrientedShapeCellValue α β hcell b r hC hG hk hkb hg hgb t
  have hlocalSum := integrable_finsetSum (Finset.univ : Finset Cell) (fun b _ ↦ hlocal b)
  have hrepair : Integrable (fun ω ↦ spatialLegalMarkedSourceDefectSum q cell id id ω*B) P :=
    hdef.1.mul_const B
  have hsourceI : ∀ᵐ a ∂α, a ∈ I := by
    rw [← hπ.1]
    exact (ae_map_iff measurable_fst.aemeasurable hIm).mpr (hI.mono fun _ h ↦ h.1)
  have hsource := ae_all_sourceMarks q α β r (fun a ↦ a ∈ I) hsourceI
  have hcross := ae_all_crossMarks q α β r (fun p ↦ gap ≤ |p.2-p.1|) hsep
  have hpoint : ∀ᵐ ω ∂P, legalMarkedTilted q id id r kin g t ω ≤
      (∑ b : Cell, originalOrientedShapeCellValue cell b r kin g t ω) +
        spatialLegalMarkedSourceDefectSum q cell id id ω*B := by
    filter_upwards [hsource,hcross] with ω hs hc
    exact D.legalMarkedTilted_le_spatial_cells hgap cell r.coe_nonneg hC hG kin hkb g hgb t ω
      (fun i ↦ hs i) (fun i j ↦ hc i j)
  have h := integral_mono_ae
    (integrable_legalMarkedTilted q measurable_id measurable_id α β r hC hG hk hkb hg hgb t)
    (hlocalSum.add hrepair) hpoint
  change (∫ ω, legalMarkedTilted q id id r kin g t ω ∂P) ≤
    ∫ ω, (∑ b : Cell, originalOrientedShapeCellValue cell b r kin g t ω) +
      spatialLegalMarkedSourceDefectSum q cell id id ω*B ∂P at h
  rw [integral_add hlocalSum hrepair,integral_finsetSum _ (fun b _ ↦ hlocal b),
    integral_mul_const] at h
  refine h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ hB))
  simpa only [Fintype.card_option,Fintype.card_prod,Fintype.card_unit,Fintype.card_fin,
    one_mul,Nat.cast_add,Nat.cast_one,Nat.cast_mul] using hdef.2

end OTSelector.Reconstruction
