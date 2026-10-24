import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonCandidate

/-!
# Common Palm readouts of a legal stationary matching

The kinetic and probe integrals use the same actual source-anchored Palm.
Their affine combination is the legal value, for both stationary pressure data
and measurable reserve liftings.
-/

open MeasureTheory

noncomputable section

namespace OTSelector.Reconstruction

variable {q : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- The kinetic Palm readout of a legal weighted stationary matching. -/
noncomputable def legalKineticReadout
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) : ℝ :=
  ∫ m, kin m.1.1 m.1.2 m.2 ∂legalMarkedJointPalm q M.law

/-- The probe Palm readout of a legal weighted stationary matching. -/
noncomputable def legalProbeReadout
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) : ℝ :=
  ∫ m, g m.1.1 m.1.2 ∂legalMarkedJointPalm q M.law

/-- The legal value is exactly the datum pressure K + v * P. -/
theorem legal_value_eq_kinetic_add_tilt_mul_probe
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (v : ℝ) :
    M.value v = legalKineticReadout M + v * legalProbeReadout M := rfl

/-- The kinetic readout is nonnegative for a nonnegative kinetic coefficient. -/
theorem legalKineticReadout_nonneg
    (hkin_nonneg : ∀ a b (v : Fin q → ℝ), 0 ≤ kin a b v)
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    0 ≤ legalKineticReadout M :=
  integral_nonneg (fun m => hkin_nonneg m.1.1 m.1.2 m.2)

/-- The probe readout is bounded by the probe bound. -/
theorem legalProbeReadout_abs_le {G : ℝ} (hgb : ∀ a b, |g a b| ≤ G)
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    |legalProbeReadout M| ≤ G := by
  have : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  have h1 : |∫ m, g m.1.1 m.1.2 ∂legalMarkedJointPalm q M.law| ≤
      ∫ m, |g m.1.1 m.1.2| ∂legalMarkedJointPalm q M.law :=
    abs_integral_le_integral_abs
  have h2 : ∫ m, |g m.1.1 m.1.2| ∂legalMarkedJointPalm q M.law ≤
      ∫ _m, G ∂legalMarkedJointPalm q M.law :=
    integral_mono M.probe_integrable.abs (integrable_const G) (fun m => hgb _ _)
  have h3 : ∫ _m, G ∂legalMarkedJointPalm q M.law = G := by simp
  exact h1.trans (h2.trans_eq h3)

end OTSelector.Reconstruction
