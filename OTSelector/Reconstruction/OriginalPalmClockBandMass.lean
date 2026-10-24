import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonCandidate

/-! Actual true-Palm mark-band masses come from the immutable original source
or target clock marginal, even when the band also restricts matching momentum. -/
open Set Function MeasureTheory
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Any true-Palm mark subfamily in an original shifted source-clock band has
mass at most that same original source band; no momentum independence is used. -/
theorem LegalWeightedStationaryPoissonMatching.palm_sourceClockBand_mass_le
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (level : ℝ) {J : Set ℝ} (hJ : MeasurableSet J)
    {B : Set (PhysicalPairPalmMark (Fin q))}
    (hB : ∀ m ∈ B, m.1.1 - level ∈ J) :
    legalMarkedJointPalm q Q.law B ≤ (α.map (fun a : ℝ ↦ a - level)) J := by
  have hJs : MeasurableSet ((fun a : ℝ ↦ a - level) ⁻¹' J) :=
    hJ.preimage (measurable_id.sub_const level)
  calc
    _ ≤ legalMarkedJointPalm q Q.law
        ((fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.1) ⁻¹'
          ((fun a : ℝ ↦ a - level) ⁻¹' J)) := measure_mono hB
    _ = α ((fun a : ℝ ↦ a - level) ⁻¹' J) := by
      rw [← Measure.map_apply measurable_fst.fst hJs, Q.source_clock]
    _ = _ := (Measure.map_apply (measurable_id.sub_const level) hJ).symm

/-- The corresponding unchanged target-clock marginal controls every actual
true-Palm target band, including further correlated restrictions. -/
theorem LegalWeightedStationaryPoissonMatching.palm_targetClockBand_mass_le
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (level : ℝ) {J : Set ℝ} (hJ : MeasurableSet J)
    {B : Set (PhysicalPairPalmMark (Fin q))}
    (hB : ∀ m ∈ B, m.1.2 - level ∈ J) :
    legalMarkedJointPalm q Q.law B ≤ (β.map (fun a : ℝ ↦ a - level)) J := by
  have hJs : MeasurableSet ((fun a : ℝ ↦ a - level) ⁻¹' J) :=
    hJ.preimage (measurable_id.sub_const level)
  calc
    _ ≤ legalMarkedJointPalm q Q.law
        ((fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.2) ⁻¹'
          ((fun a : ℝ ↦ a - level) ⁻¹' J)) := measure_mono hB
    _ = β ((fun a : ℝ ↦ a - level) ⁻¹' J) := by
      rw [← Measure.map_apply measurable_fst.snd hJs, Q.target_clock]
    _ = _ := (Measure.map_apply (measurable_id.sub_const level) hJ).symm

end OTSelector.Reconstruction
