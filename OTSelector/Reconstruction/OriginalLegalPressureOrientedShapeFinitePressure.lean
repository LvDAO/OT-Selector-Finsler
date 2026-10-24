import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapePartitionReadout
import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeInnerExpectation

/-! A genuine finite-pressure comparison between the native cube, inner oriented cube, and hole. -/

open Set Function MeasureTheory ProbabilityTheory
open OTSelector.Probability
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

/-- Only the complementary spatial hole and the actual finite Poisson Hall repair remain. -/
theorem FiniteScalarBins.legalMarkedPressure_le_oriented_inner_and_hole
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (hIm : MeasurableSet I) (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hπ : Vlasov.IsCoupling π α β) (hI : ∀ᵐ p ∂π, p.1 ∈ I ∧ p.2 ∈ I)
    (hforward : ∀ᵐ p ∂π, gap ≤ p.2-p.1)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |p.2-p.1|)
    {q : ℕ} (hq : 0 < q)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {s : ℝ} (hs : 0 < s)
    (hsub : originalCenteredPhysicalCubeRegion b s ⊆ haarRootCube (Fin q) (1 / 2))
    (r : ℝ≥0)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkb : ∀ a d v, |kin a d v| ≤ C*∑ l, v l^2)
    (hhom : ∀ a d (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a d (fun i ↦ c * v i) = c ^ 2 * kin a d v)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a d, |g a d| ≤ G) (t : ℝ) :
    legalMarkedPressure q id id α β r kin g t ≤
      legalMarkedPressure q id id α β (r * Real.toNNReal (s ^ q))
        (originalScreeningFrameKinetic b kin) g t +
      (∫ ω, shapeLegalMarkedTilted q id id (originalOrientedShapeUnitInner b s)ᶜ r kin g t ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β r) +
      Real.sqrt (2*(r : ℝ)*(2*(D.count*D.count+1))) *
        (2*((D.count : ℝ)+1)*((r : ℝ)^(2/(q : ℝ))*(C*q)+|t| * G)) := by
  have h := D.legalMarkedPressure_le_shape_and_complement hgap hIm π α β hπ hI
    hforward hsep q (measurableSet_originalOrientedShapeUnitInner b s) r
    hC hG hk hkb hg hgb t
  rw [integral_originalOrientedShape_inner_eq_pressure hq b hs hsub α β r kin hk hhom
    g hg t] at h
  exact h

end OTSelector.Reconstruction
