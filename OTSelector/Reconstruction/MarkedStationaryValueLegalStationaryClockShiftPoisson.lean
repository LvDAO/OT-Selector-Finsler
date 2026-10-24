import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryClockShift
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonLaplace

/-!
# Actual original Poisson inputs survive continuous clock-dependent shifts

The finite original array formula produces the whole compact Poisson Laplace
functional of any genuine original stationary matching. Haar invariance then
proves that the actual pushed scene has the same original independent Poisson
input functional. No preservation of the input law is assumed.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalStationaryClockShiftPoissonInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalStationaryClockShiftPoissonPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The actual pushed joint scene has the full unchanged original compact
Poisson Laplace functional, because its literal Haar-clock intensities agree. -/
theorem LegalWeightedStationaryPoissonMatching.clockShift_input_laplace_eq_global_exp
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (b : Fin 2 → C(ℝ, Fin q → ℝ))
    (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x) :
    (∫ s, legalMarkedInputSceneLaplace q F hF s
      ∂(legalMarkedInputClockShiftLaw q b M.law : Measure (LegalMarkedOptimalInputScene q))) =
      Real.exp ((∫ x, (Real.exp (-F (x, 0)) - 1)
        ∂(volume : Measure (Fin q → ℝ)).prod α) +
          ∫ y, (Real.exp (-F (y, 1)) - 1)
            ∂(volume : Measure (Fin q → ℝ)).prod β) := by
  let G := F.comp (legalClockShiftColoredPoint q b).toCocompactMap
  have hG : ∀ x, 0 ≤ G x := fun x ↦ hF _
  have hread : (fun s ↦ legalMarkedInputSceneLaplace q F hF
      (legalMarkedInputSceneClockShift q b s)) = fun s ↦ legalMarkedInputSceneLaplace q G hG s := by
    funext s
    change Real.exp (-LocalFiniteMeasure.testIntegral (legalMarkedInputSceneClockShift q b s).2 F) = _
    rw [legalMarkedInputSceneClockShift_testIntegral]
    rfl
  change (∫ s, legalMarkedInputSceneLaplace q F hF s
    ∂(M.law : Measure (LegalMarkedOptimalInputScene q)).map (legalMarkedInputSceneClockShift q b)) = _
  rw [integral_map (continuous_legalMarkedInputSceneClockShift q b).measurable.aemeasurable
    (legalMarkedInputSceneLaplace q F hF).continuous.aestronglyMeasurable, hread,
    M.input_laplace_eq_global_exp G hG]
  have hI (γ : Measure ℝ) [IsProbabilityMeasure γ] (c : Fin 2) :
      (∫ x, (Real.exp (-G (x, c)) - 1) ∂(volume : Measure (Fin q → ℝ)).prod γ) =
        ∫ x, (Real.exp (-F (x, c)) - 1) ∂(volume : Measure (Fin q → ℝ)).prod γ := by
    change (∫ x, (Real.exp (-F (legalClockShiftPoint q (b c) x, c)) - 1)
      ∂(volume : Measure (Fin q → ℝ)).prod γ) = _
    exact (measurePreserving_legalClockShiftPoint q (b c) γ).integral_comp
      (legalClockShiftPoint q (b c)).toMeasurableEquiv.measurableEmbedding
      (fun x ↦ Real.exp (-F (x, c)) - 1)
  rw [hI α 0, hI β 1]

/-- The actual shifted original scene satisfies exactly the prescribed
finite-window compact Poisson input field required by a genuine matching. -/
theorem LegalWeightedStationaryPoissonMatching.clockShift_input_laplace
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) (S : ℝ) (hS : 0 < S)
    (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x)
    (hz : ∀ (x : LegalMarkedPhysicalPoint q) (c : Fin 2),
      x.1 ∉ haarRootCube (Fin q) S → F (x, c) = 0) :
    (∫ s, legalMarkedInputSceneLaplace q F hF s
      ∂(legalMarkedInputClockShiftLaw q b M.law : Measure (LegalMarkedOptimalInputScene q))) =
      ∫ z, legalInputBlockLaplace (fun x ↦ F (x, 0)) (fun x ↦ F (x, 1)) z
        ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β := by
  rw [M.clockShift_input_laplace_eq_global_exp b F hF]
  symm
  have hfin : volume (haarRootCube (Fin q) S) ≠ ∞ := by
    rw [volume_haarRootCube (Fin q) hS.le]
    exact ENNReal.ofReal_ne_top
  have hpos : volume (haarRootCube (Fin q) S) ≠ 0 := by
    rw [volume_haarRootCube (Fin q) hS.le]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity : 0 < 2 * S) _)).ne'
  apply integral_legalInputPoissonWindowLaw_laplace_eq_global_exp q hfin hpos α β
    (F.continuous.measurable.comp (measurable_id.prodMk measurable_const))
    (F.continuous.measurable.comp (measurable_id.prodMk measurable_const))
    (fun x ↦ hF (x, 0)) (fun x ↦ hF (x, 1))
  · exact fun x hx ↦ hz x 0 hx
  · exact fun x hx ↦ hz x 1 hx

end OTSelector.Reconstruction
