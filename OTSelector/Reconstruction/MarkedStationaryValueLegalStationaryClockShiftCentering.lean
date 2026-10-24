import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryClockShiftEnergyPolynomial

/-!
# Actual stationary first variation centers the original momentum

The clock-dependent shifts are genuine competitors of the same original
weighted matching problem. Comparing their exact energy polynomial therefore
forces the momentum pairing to vanish at a minimizing law. The quantitative
version keeps the actual value error for a nearly minimizing law.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace Matrix Module Manifold
open scoped ENNReal NNReal CompactlySupported Classical ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option linter.unusedSectionVars false

variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
  {F : ContinuousFinslerNorm E N} {u : N → ℝ}

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The exact family of genuine competitors bounds the square of the
original momentum pairing by four times its actual pure-shift energy and the
actual value error. No second displacement moment is assumed. -/
theorem sq_integral_clockShift_momentum_le_of_value_error
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap) (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (b : Fin 2 → C(ℝ, Fin (finrank ℝ S.covector.ker) → ℝ)) (t δ : ℝ)
    (hvalue : ∀ ε : ℝ, Q.value t ≤
      (D.clockShiftWeightedStationaryMatching hF hw hgap hbounds Q
        (fun c ↦ ε • b c)).value t + δ) :
    (∫ m, originalSeedPairMomentum S w m ⬝ᵥ legalPairClockShiftDifference _ b m
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ^ 2 ≤
        4 * (∫ m, D.originalFocalKinetic gap m.1.1 m.1.2
          (legalPairClockShiftDifference _ b m)
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) * δ := by
  let L := ∫ m, originalSeedPairMomentum S w m ⬝ᵥ legalPairClockShiftDifference _ b m
    ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  let A := ∫ m, D.originalFocalKinetic gap m.1.1 m.1.2
    (legalPairClockShiftDifference _ b m)
    ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  have hpoly : ∀ ε : ℝ, 0 ≤ A * (ε * ε) + L * ε + δ := by
    intro ε
    have h := hvalue ε
    rw [D.value_clockShiftWeightedStationaryMatching_scaled_polynomial
      hF hw hgap hbounds Q b ε t] at h
    change Q.value t ≤ Q.value t + ε * L + ε ^ 2 * A + δ at h
    nlinarith
  have hdiscrim := discrim_le_zero hpoly
  dsimp only [discrim] at hdiscrim
  change L ^ 2 ≤ 4 * A * δ
  linarith

/-- Minimizing the actual original weighted stationary value forces the
pairing with every produced continuous clock-shift direction to vanish. -/
theorem integral_clockShift_momentum_eq_zero_of_minimal_value
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap) (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (t : ℝ)
    (hmin : ∀ R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value t ≤ R.value t)
    (b : Fin 2 → C(ℝ, Fin (finrank ℝ S.covector.ker) → ℝ)) :
    (∫ m, originalSeedPairMomentum S w m ⬝ᵥ legalPairClockShiftDifference _ b m
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) = 0 := by
  have hshift : ∀ ε : ℝ, Q.value t ≤
      (D.clockShiftWeightedStationaryMatching hF hw hgap hbounds Q
        (fun c ↦ ε • b c)).value t + 0 := by
    intro ε
    simpa only [add_zero] using
      hmin (D.clockShiftWeightedStationaryMatching hF hw hgap hbounds Q (fun c ↦ ε • b c))
  have h := D.sq_integral_clockShift_momentum_le_of_value_error hF hw hgap hbounds Q b t 0 hshift
  rw [mul_zero] at h
  exact sq_eq_zero_iff.mp (le_antisymm h (sq_nonneg _))

/-- Source clock shifts and target clock shifts may be varied separately.
The original momentum therefore has zero pairing with every continuous
function of either original clock, component by component. -/
theorem integral_momentum_clock_pairings_eq_zero_of_minimal_value
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap) (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (t : ℝ)
    (hmin : ∀ R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value t ≤ R.value t)
    (f : C(ℝ, ℝ)) (i : Fin (finrank ℝ S.covector.ker)) :
    (∫ m, originalSeedPairMomentum S w m i * f m.1.1
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) = 0 ∧
    (∫ m, originalSeedPairMomentum S w m i * f m.1.2
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) = 0 := by
  let b : C(ℝ, Fin (finrank ℝ S.covector.ker) → ℝ) :=
    ⟨fun a ↦ Pi.single i (f a), by
      apply continuous_pi
      intro j
      by_cases hji : j = i
      · subst j; simpa using f.continuous
      · simpa only [Pi.single_apply, hji, ↓reduceIte] using
          (continuous_const : Continuous (fun _ : ℝ ↦ (0 : ℝ)))⟩
  have hs := D.integral_clockShift_momentum_eq_zero_of_minimal_value hF hw hgap hbounds Q t hmin
    (fun c ↦ if c = 0 then b else 0)
  have ht := D.integral_clockShift_momentum_eq_zero_of_minimal_value hF hw hgap hbounds Q t hmin
    (fun c ↦ if c = 1 then b else 0)
  constructor
  · simpa [legalPairClockShiftDifference, b, dotProduct_neg, dotProduct_single,
      integral_neg] using hs
  · simpa [legalPairClockShiftDifference, b, dotProduct_single] using ht

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
