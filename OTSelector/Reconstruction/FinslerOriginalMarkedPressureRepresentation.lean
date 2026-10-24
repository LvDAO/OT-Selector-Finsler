import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryTightCutScene

/-!
# Marked pressure representation as a Palm integral

This module isolates sub-gap (a) of
FinslerOriginalPalmPressureIdentification: the marked pressure representation
p t = int x, J x dmu, identifying the finite-volume optimal cost limit with a
Palm readout J of the candidate weighted stationary matching.

The mechanism is the exact Campbell factorization available for a genuine
weighted stationary matching:

  physicalScenePairCampbell (legalMarkedInputPairLaw q M.law)
    = volume.prod (legalMarkedJointPalm q M.law)
  (LegalWeightedStationaryPoissonMatching.campbell_eq_volume_prod_palm).

1. **Campbell factorization** (markedPressure_campbellFactor): the candidate's
   pair Campbell measure is the product of Lebesgue volume and its probability
   Palm.

2. **Palm readout transfer** (palmReadout_factorization): for every measurable
   window U and every local mark readout J, the Campbell integral of the window
   indicator times J is volume(U) times the Palm integral of J.  This is the
   marked Mecke/Campbell transfer turning a windowed scene readout into a Palm
   integral.

3. **Marked pressure representation** (markedPressureRepresentation_of_window
   Readout): if the finite-volume marked pressure readouts are the windowed
   Campbell integrals of a fixed local readout J, then their volume-normalized
   limit p is exactly the Palm integral of J.  This is precisely the
   representation p t = int x, J x dmu needed by the (Palm) hypothesis, with
   J the local readout of the candidate value at the origin.

## Remaining sub-gap

Only the readout identification remains: that the actual finite-volume optimal
tilted value legalMarkedTilted, restricted to a window, IS the windowed Campbell
integral of the local candidate-value readout J (the local optimality/readout
formula for the finite legal maximum).  The Campbell factorization, the
transfer and the normalization are proved here; no measure-theoretic or
integrational step is missing.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open OTSelector.Probability
open scoped ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **Campbell factorization for a genuine weighted stationary matching.**  The
candidate's pair Campbell measure is Lebesgue volume times its probability Palm. -/
theorem markedPressure_campbellFactor
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    physicalScenePairCampbell (legalMarkedInputPairLaw q M.law :
      Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) =
      (volume : Measure (Fin q → ℝ)).prod (legalMarkedJointPalm q M.law) :=
  LegalWeightedStationaryPoissonMatching.campbell_eq_volume_prod_palm M

/-- **Palm readout transfer (marked Mecke/Campbell identity).**  For a measurable
window U and a local mark readout J, the Campbell integral of the windowed
readout is the window volume times the Palm integral of J. -/
theorem palmReadout_factorization
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (J : PhysicalPairPalmMark (Fin q) → ℝ) :
    (∫ z, (U.indicator (fun _ => (1 : ℝ))) z.1 * J z.2
        ∂(physicalScenePairCampbell (legalMarkedInputPairLaw q M.law :
          Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))))) =
      (volume.real U) * (∫ m, J m ∂legalMarkedJointPalm q M.law) := by
  haveI : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  have hvol : (∫ x : Fin q → ℝ, (U.indicator (fun _ => (1 : ℝ))) x ∂volume) =
      volume.real U := by
    rw [integral_indicator hU, setIntegral_const, smul_eq_mul, mul_one]
  rw [markedPressure_campbellFactor M, integral_prod_mul, hvol]

/-- **Marked pressure representation as a Palm integral.**  If the finite-volume
marked pressure readouts are the windowed Campbell integrals of a fixed local
readout J and their volume-normalized limit is p, then p is the Palm integral
of J. -/
theorem markedPressureRepresentation_of_windowReadout
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (J : PhysicalPairPalmMark (Fin q) → ℝ)
    (U : ℕ → Set (Fin q → ℝ)) (hU : ∀ n, MeasurableSet (U n))
    (hVol : ∀ n, volume.real (U n) ≠ 0)
    (hVoltop : Tendsto (fun n => volume.real (U n)) atTop atTop)
    (readout : ℕ → ℝ)
    (hread : ∀ n, readout n =
      ∫ z, (U n).indicator (fun _ => (1 : ℝ)) z.1 * J z.2
        ∂(physicalScenePairCampbell (legalMarkedInputPairLaw q M.law :
          Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))))
    {p : ℝ}
    (hp : Tendsto (fun n => readout n / volume.real (U n)) atTop (𝓝 p)) :
    p = ∫ m, J m ∂legalMarkedJointPalm q M.law := by
  have hconst : ∀ n, readout n / volume.real (U n) =
      ∫ m, J m ∂legalMarkedJointPalm q M.law := by
    intro n
    rw [hread n, palmReadout_factorization M (hU n) J]
    exact mul_div_cancel_left₀ _ (hVol n)
  have hfun : (fun n => readout n / volume.real (U n)) =
      fun _ => ∫ m, J m ∂legalMarkedJointPalm q M.law := funext hconst
  rw [hfun] at hp
  exact tendsto_nhds_unique hp tendsto_const_nhds

/-- **Unit-window specialization.**  If the window has volume one, the windowed
Campbell readout is exactly the Palm integral of the local readout. -/
theorem palmReadout_factorization_of_unitVolume
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U) (hvol1 : volume.real U = 1)
    (J : PhysicalPairPalmMark (Fin q) → ℝ) :
    (∫ z, (U.indicator (fun _ => (1 : ℝ))) z.1 * J z.2
        ∂(physicalScenePairCampbell (legalMarkedInputPairLaw q M.law :
          Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))))) =
      ∫ m, J m ∂legalMarkedJointPalm q M.law := by
  rw [palmReadout_factorization M hU J, hvol1, one_mul]

end OTSelector.Reconstruction
