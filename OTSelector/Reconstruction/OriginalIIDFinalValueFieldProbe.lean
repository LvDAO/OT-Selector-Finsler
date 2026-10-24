import OTSelector.Reconstruction.OriginalIIDFinalValueFieldKinetic

/-! The same original stationary candidate law keeps every signed value under actual readout recovery. -/
open Set Function Filter MeasureTheory
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Replacing the probe by its actual almost-everywhere recovered physical readout
keeps the same original inputs, matching law, kinetic cost and integrability. -/
def LegalWeightedStationaryPoissonMatching.withAEEqProbe
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g g' : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (heq : ∀ᵐ m ∂legalMarkedJointPalm q Q.law, g' m.1.1 m.1.2 = g m.1.1 m.1.2) :
    LegalWeightedStationaryPoissonMatching q α β kin g' where
  law := Q.law
  stationary := Q.stationary
  full_matching := Q.full_matching
  forward := Q.forward
  input_laplace := Q.input_laplace
  palm_probability := Q.palm_probability
  source_clock := Q.source_clock
  target_clock := Q.target_clock
  kinetic_integrable := Q.kinetic_integrable
  probe_integrable := Q.probe_integrable.congr (heq.mono (fun _ h ↦ h.symm))

/-- The actual recovered probe preserves every signed value on the same law. -/
theorem LegalWeightedStationaryPoissonMatching.withAEEqProbe_value
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g g' : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (heq : ∀ᵐ m ∂legalMarkedJointPalm q Q.law, g' m.1.1 m.1.2 = g m.1.1 m.1.2)
    (t : ℝ) : (Q.withAEEqProbe heq).value t = Q.value t := by
  change _ + t*(∫ m, g' m.1.1 m.1.2 ∂legalMarkedJointPalm q Q.law) = _
  rw [integral_congr_ae heq]
  rfl

/-- Exact original parameter identities preserve the literal scene law and all
signed values; this isolates proof-irrelevant transport from analytic readout recovery. -/
theorem LegalWeightedStationaryPoissonMatching.exists_sameLaw_of_eq_parameters
    {q : ℕ} {α β α' β' : Measure ℝ}
    {kin kin' : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g g' : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hα : α=α') (hβ : β=β') (hkin : kin=kin') (hg : g=g') :
    ∃ Q' : LegalWeightedStationaryPoissonMatching q α' β' kin' g',
      Q'.law = Q.law ∧ ∀ t, Q'.value t = Q.value t := by
  subst α'; subst β'; subst kin'; subst g'
  exact ⟨Q,rfl,fun _ ↦ rfl⟩

end OTSelector.Reconstruction
