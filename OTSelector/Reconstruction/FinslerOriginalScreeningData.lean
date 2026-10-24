import OTSelector.Reconstruction.FinslerOriginalReadoutGlue

/-!
# Screening data for the frozen stationary readout datum

FinslerOriginalReadoutGlue.lean leaves open the screening data
StationaryScreening datum (the RHS of
StationaryPressureDatum.Iw_eq_I2_iff_screening).  This module produces it from
the legal-pressure value-equality lane.

## Contents

1. **Abstract production of the screening data.**  For a probe-indexed
   stationary datum,

   * stationaryScreening_of_c2_univ: if the second-moment class is everything at
     every probe, screening holds (take the same matching);
   * stationaryScreening_of_classesEq: if the two admissible classes coincide at
     every probe, screening holds;
   * stationaryScreening_of_valueBudget: a value-gap budget Bres <= 0 (the
     reserve-zero case of the Palm repair estimate) gives screening;
   * finalValueIdentification_of_c2_univ / finalValueIdentification_of_valueBudget:
     the resulting value identification for the actual pressure pair through the
     readout bridges of FinslerOriginalReadoutGlue.lean.

2. **The uniform elliptic regime of the legal lane.**  The legal-pressure
   value-equality lane proves that a uniformly elliptic kinetic coefficient
   forces every legal weighted matching to be a finite-second-moment matching
   (secondMomentSubclass_of_uniform_elliptic).  Hence the second-moment
   subclass/class is everything and the screening data of the original focal
   kinetic cost holds unconditionally:

   * legalSecondMomentSubset_eq_univ_of_uniform_elliptic;
   * legalScreening_of_uniform_elliptic (generic legal matching family);
   * originalSecondMomentSubclass_mem_of_uniform_elliptic, and
     originalScreening_of_uniform_elliptic: the exact RHS of
     originalWeightedStationaryInf_eq_secondMomentInf_iff_screening;
   * originalWeightedStationaryInf_eq_secondMomentInf_of_uniform_elliptic: the
     resulting unconditional value identification of the actual original
     legal pressures, obtained from the lane equivalence.

3. **The reserve-zero budget regime.**  From the quantitative original value
   gap control (originalSecondMomentStationaryInf_le_weighted_add) with budget
   Bres <= 0 one gets the screening data
   (originalScreening_of_zeroBudget) and hence the original value
   identification (originalWeightedStationaryInf_eq_secondMomentInf_of_zeroBudget).

## Exact remaining data

* To instantiate an actual StationaryPressureDatum over the legal matching space
  one needs one competitor matching in the weighted class and one in the
  second-moment class with finite kinetic energy (the fields competitor,
  competitor2, kinetic_competitor_le).  The original lane produces the
  second-moment competitor (originalSecondMomentSubclass_nonempty); a single
  such matching serves both roles.  Once the datum exists, the elliptic
  screening above turns into StationaryScreening datum immediately via
  stationaryScreening_of_c2_univ.
* In the non-elliptic regime the screening data is exactly the open screening /
  Palm reserve analysis; the budget-zero branch shows the precise quantitative
  form that remains.

No sorry, admit or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Topology TopologicalSpace
open OTSelector.Geometry OTSelector.Geometry.ContinuousFinslerNorm OTSelector.Probability Module
open scoped ContDiff Topology ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## 1. Abstract production of the screening data -/

section Abstract

variable {A B : Set M} {W : Type*} {G Cb : ℝ}

/-- If the second-moment class is everything at every probe, the screening
approximation holds: the same matching is a second-moment competitor. -/
theorem stationaryScreening_of_c2_univ
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (h2 : ∀ f : FinalProbeSpace A B, (datum f).C2 = Set.univ) :
    StationaryScreening datum := by
  intro f v Q _hQ ε hε
  exact ⟨Q, by rw [h2 f]; exact Set.mem_univ Q, by linarith⟩

/-- If the two admissible classes coincide at every probe, the screening
approximation holds. -/
theorem stationaryScreening_of_classesEq
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hclass : ∀ f : FinalProbeSpace A B, (datum f).Cw = (datum f).C2) :
    StationaryScreening datum := by
  intro f v Q hQ ε hε
  exact ⟨Q, (hclass f) ▸ hQ, by linarith⟩

/-- A value-gap budget Bres <= 0 gives the screening approximation: the same
positive-tolerance inequality follows from the budget. -/
theorem stationaryScreening_of_valueBudget
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    {Bres : ℝ} (hB : Bres ≤ 0)
    (hbudget : ∀ (f : FinalProbeSpace A B) (v : ℝ) (Q : W), Q ∈ (datum f).Cw →
      ∃ Q' ∈ (datum f).C2,
        (datum f).K Q' + v * (datum f).P Q' ≤
          (datum f).K Q + v * (datum f).P Q + Bres) :
    StationaryScreening datum := by
  intro f v Q hQ ε hε
  obtain ⟨Q', hQ', hle⟩ := hbudget f v Q hQ
  exact ⟨Q', hQ', by linarith⟩

/-- The value identification for the actual pressure pair in the elliptic
regime: if the second-moment class is everything at every probe, the readout
bridges alone identify the two pressures. -/
theorem finalValueIdentification_of_c2_univ
    (pressureLower pressureUpper : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (h2 : ∀ f : FinalProbeSpace A B, (datum f).C2 = Set.univ)
    (hL : LowerStationaryReadout pressureLower datum)
    (hU : UpperStationaryReadout pressureUpper datum) :
    FinalValueIdentification pressureLower pressureUpper :=
  finalValueIdentification_of_readoutBridges pressureLower pressureUpper datum hL hU
    (stationaryScreening_of_c2_univ datum h2)

/-- The value identification for the actual pressure pair in the reserve-zero
budget regime. -/
theorem finalValueIdentification_of_valueBudget
    (pressureLower pressureUpper : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    {Bres : ℝ} (hB : Bres ≤ 0)
    (hbudget : ∀ (f : FinalProbeSpace A B) (v : ℝ) (Q : W), Q ∈ (datum f).Cw →
      ∃ Q' ∈ (datum f).C2,
        (datum f).K Q' + v * (datum f).P Q' ≤
          (datum f).K Q + v * (datum f).P Q + Bres)
    (hL : LowerStationaryReadout pressureLower datum)
    (hU : UpperStationaryReadout pressureUpper datum) :
    FinalValueIdentification pressureLower pressureUpper :=
  finalValueIdentification_of_readoutBridges pressureLower pressureUpper datum hL hU
    (stationaryScreening_of_valueBudget datum hB hbudget)

end Abstract

/-! ## 2. The uniform elliptic regime of the legal lane -/

section LegalElliptic

variable {q : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- Under a uniformly elliptic kinetic coefficient the legal second-moment
subclass is all of the weighted class. -/
theorem legalSecondMomentSubset_eq_univ_of_uniform_elliptic
    {c : ℝ} (hc : 0 < c)
    (hkin : ∀ a b (v : Fin q → ℝ), c * ∑ i, v i ^ 2 ≤ kin a b v) :
    {Q : LegalWeightedStationaryPoissonMatching q α β kin g |
      Q.secondMomentSubclass} = Set.univ := by
  ext Q
  simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact secondMomentSubclass_of_uniform_elliptic hc hkin Q

/-- **Unconditional legal screening in the uniformly elliptic regime.**  Every
legal weighted matching is approached in value from above by a second-moment
matching: take the matching itself. -/
theorem legalScreening_of_uniform_elliptic
    {c : ℝ} (hc : 0 < c)
    (hkin : ∀ a b (v : Fin q → ℝ), c * ∑ i, v i ^ 2 ≤ kin a b v)
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (t : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q' : LegalWeightedStationaryPoissonMatching q α β kin g,
      Q'.secondMomentSubclass ∧ Q'.value t < Q.value t + ε :=
  ⟨Q, secondMomentSubclass_of_uniform_elliptic hc hkin Q, by linarith⟩

end LegalElliptic

/-! ### The actual original focal kinetic cost -/

section OriginalElliptic

variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- Under a uniformly elliptic original focal kinetic coefficient, every legal
weighted matching of the original focal kinetic cost is a finite-second-moment
matching. -/
theorem originalSecondMomentSubclass_mem_of_uniform_elliptic
    {gap : ℝ} {g : ℝ → ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hkin : ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      c * ∑ i, v i ^ 2 ≤ D.originalFocalKinetic gap a b v)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    Q ∈ D.originalSecondMomentSubclass gap g :=
  secondMomentSubclass_of_uniform_elliptic hc hkin Q

/-- Under a uniformly elliptic original focal kinetic coefficient the original
second-moment subclass is everything. -/
theorem originalSecondMomentSubclass_eq_univ_of_uniform_elliptic
    {gap : ℝ} {g : ℝ → ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hkin : ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      c * ∑ i, v i ^ 2 ≤ D.originalFocalKinetic gap a b v) :
    D.originalSecondMomentSubclass gap g = Set.univ := by
  ext Q
  simp only [Set.mem_univ, iff_true]
  exact originalSecondMomentSubclass_mem_of_uniform_elliptic D hc hkin Q

/-- **The exact screening RHS of the lane equivalence, unconditionally in the
uniformly elliptic regime.**  Every legal weighted matching of the original
focal kinetic cost is approached in value from above by a finite-second-moment
matching, at every tilt. -/
theorem originalScreening_of_uniform_elliptic
    {gap : ℝ} {g : ℝ → ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hkin : ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      c * ∑ i, v i ^ 2 ≤ D.originalFocalKinetic gap a b v)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q' : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g,
      Q' ∈ D.originalSecondMomentSubclass gap g ∧ Q'.value t < Q.value t + ε :=
  ⟨Q, originalSecondMomentSubclass_mem_of_uniform_elliptic D hc hkin Q, by linarith⟩

/-- **The original value identification in the uniformly elliptic regime.**  The
original weighted and second-moment legal pressures coincide at every tilt,
unconditionally in the elliptic regime, by the lane equivalence. -/
theorem originalWeightedStationaryInf_eq_secondMomentInf_of_uniform_elliptic
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (hpi : Vlasov.IsCoupling pi μ ν) (horder : ∀ᵐ p ∂pi, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    {c : ℝ} (hc : 0 < c)
    (hkin : ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      c * ∑ i, v i ^ 2 ≤ D.originalFocalKinetic gap a b v) (t : ℝ) :
    D.originalWeightedStationaryInf gap g t =
      D.originalSecondMomentStationaryInf gap g t :=
  (D.originalWeightedStationaryInf_eq_secondMomentInf_iff_screening hF hw hq hgap
    hbounds pi hpi horder hg hgb t).mpr
    (fun Q ε hε => originalScreening_of_uniform_elliptic D hc hkin Q t hε)

end OriginalElliptic

/-! ## 3. The reserve-zero budget regime -/

section OriginalZeroBudget

variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- **Screening from a zero reserve budget.**  The quantitative original value
gap control with budget Bres <= 0 gives the exact screening RHS of the lane
equivalence. -/
theorem originalScreening_of_zeroBudget
    {gap : ℝ} {g : ℝ → ℝ → ℝ} {Bres : ℝ} (hB : Bres ≤ 0)
    (hbudget : ∀ (Q : LegalWeightedStationaryPoissonMatching
        (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g) (t : ℝ),
      ∃ Q' : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
          (D.originalFocalKinetic gap) g,
        Q' ∈ D.originalSecondMomentSubclass gap g ∧
          Q'.value t ≤ Q.value t + Bres)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q' : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g,
      Q' ∈ D.originalSecondMomentSubclass gap g ∧ Q'.value t < Q.value t + ε := by
  obtain ⟨Q', hQ', hle⟩ := hbudget Q t
  exact ⟨Q', hQ', by linarith⟩

/-- **The original value identification in the reserve-zero budget regime.** -/
theorem originalWeightedStationaryInf_eq_secondMomentInf_of_zeroBudget
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (hpi : Vlasov.IsCoupling pi μ ν) (horder : ∀ᵐ p ∂pi, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    {Bres : ℝ} (hB : Bres ≤ 0)
    (hbudget : ∀ (Q : LegalWeightedStationaryPoissonMatching
        (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g) (t : ℝ),
      ∃ Q' : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
          (D.originalFocalKinetic gap) g,
        Q' ∈ D.originalSecondMomentSubclass gap g ∧
          Q'.value t ≤ Q.value t + Bres) (t : ℝ) :
    D.originalWeightedStationaryInf gap g t =
      D.originalSecondMomentStationaryInf gap g t :=
  (D.originalWeightedStationaryInf_eq_secondMomentInf_iff_screening hF hw hq hgap
    hbounds pi hpi horder hg hgb t).mpr
    (fun Q ε hε => originalScreening_of_zeroBudget D hB hbudget Q t hε)

end OriginalZeroBudget

end OTSelector.Reconstruction