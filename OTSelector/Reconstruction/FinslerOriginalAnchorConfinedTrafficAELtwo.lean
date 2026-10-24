import OTSelector.Reconstruction.OriginalAnchorConfinedTrafficSquare
import OTSelector.Reconstruction.OriginalBirthNormalizerQuadraticMoment
import OTSelector.MeasureTheory.Lp.NonnegativeSquareReadout
import OTSelector.Reconstruction.OriginalCompletePathAbsoluteTraffic

/-! Actual original bounded-phase physical traffic has L2 from its own finite
contributor count and source confinement. Its momentum moment is internal. -/
open Set Function Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The actual source-confined original physical traffic is L2 with the exact
physical source volume and same-band normalized momentum square. Original kinetic
integrability internally supplies that moment; no new moment premise is required. -/
theorem OriginalSeedConditionalMoments.goodEvent_original_anchorConfined_traffic_memLp_two_ae
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (anchor : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) →
      Fin (finrank ℝ S.covector.ker) → ℝ) (ha : Measurable anchor)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {h : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞} (hh : Measurable h)
    (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞)
    (hmask : Measurable mask)
    {A : Set (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))} (hA : MeasurableSet A)
    {W : Set (Fin (finrank ℝ S.covector.ker) → ℝ)} (hW : MeasurableSet W)
    (hWfin : volume W ≠ (∞ : ℝ≥0∞))
    {B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))} (hB : MeasurableSet B)
    (V : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) →
      Set ((Fin (finrank ℝ S.covector.ker) → ℝ) × PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))))
    (hV : ∀ s, MeasurableSet (V s)) {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) :
    let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      originalSeedPathOffset S w z.2 z.1
    let f := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z
    (∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))), s ∉ A →
      (∀ a ∈ V s, a.1 + anchor a.2 ∈ W ∧ a.2 ∈ B) ∧
      physicalScenePairKernel s.1 (V s) ≤ ENNReal.ofReal K ∧
      (∀ᵐ a ∂physicalScenePairKernel s.1, a ∉ V s →
        (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) = 0) ∧
      (∀ᵐ a ∂(physicalScenePairKernel s.1).restrict (V s),
        (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) ≤
          ENNReal.ofReal C * ENNReal.ofReal ‖T *ᵥ originalSeedPairMomentum S w a.2‖)) →
    MemLp (Aᶜ.indicator (fun s ↦
      (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker) d h f s).toReal)) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
    (∫ s, (Aᶜ.indicator (fun z ↦
      (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker) d h f z).toReal) s) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
      K * C ^ 2 * (volume W).toReal *
        (∫⁻ m in B, ENNReal.ofReal (‖T *ᵥ originalSeedPairMomentum S w m‖ ^ 2)
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal := by
  dsimp only
  intro hdata
  have hp : Measurable (fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
      T *ᵥ originalSeedPairMomentum S w m) :=
    (Matrix.toLin' T).continuous_of_finiteDimensional.measurable.comp
      (measurable_originalSeedPairMomentum S hF hw)
  have hI := D.integrable_original_normalizedMomentum_sq hF hw hgap hbounds Q T
  have hfull : (∫⁻ m, ENNReal.ofReal (‖T *ᵥ originalSeedPairMomentum S w m‖ ^ 2)
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (∞ : ℝ≥0∞) :=
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hI.2).ne
  have hband : (∫⁻ m in B, (ENNReal.ofReal ‖T *ᵥ originalSeedPairMomentum S w m‖) ^ 2
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (∞ : ℝ≥0∞) := by
    simp_rw [← ENNReal.ofReal_pow (norm_nonneg _) 2]
    exact ne_top_of_le_ne_top hfull (setLIntegral_le_lintegral B _)
  have hd := measurable_originalSeedPathOffset_joint S hF hw
  have hf : Measurable (fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z) :=
    (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul hmask
  have hsquare := Q.lintegral_goodEvent_anchorConfined_traffic_sq_le_ae _ hd hh hf
    anchor ha _ hp.norm.ennreal_ofReal hW hB V hV hdata
  have hright : ENNReal.ofReal K * (ENNReal.ofReal C) ^ 2 * volume W *
      (∫⁻ m in B, (ENNReal.ofReal ‖T *ᵥ originalSeedPairMomentum S w m‖) ^ 2
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) hWfin) hband
  have hL2 := memLp_two_of_goodEvent_lintegral_sq_le
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
    (measurable_legalMarkedCompletePathTraffic _ hd hh hf) hA hright hsquare
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hK,
    ENNReal.toReal_ofReal hC, ← ENNReal.ofReal_pow (norm_nonneg _) 2] using hL2

end OTSelector.Reconstruction
