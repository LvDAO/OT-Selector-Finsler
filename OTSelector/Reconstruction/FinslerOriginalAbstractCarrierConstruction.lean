import OTSelector.Reconstruction.FinslerOriginalStationaryClassContinuity
import OTSelector.Reconstruction.MarkedStationaryValueLegalFiniteMomentReserve

/-!
# Construction of the abstract stationary-forward carrier for the recoded legal Palm

The legal-to-forward bridge of `FinslerOriginalLegalPoissonForwardBridge` reduced the
remaining input to the abstract `StationaryForwardMatching` carrier itself.  This
file constructs it.

The only pressure-relevant fields of the carrier are the Palm probability law and its
probability instance; the remaining fields are supplied from an explicitly chosen
scene.  We use the empty matching scene (no source or target atoms, no edges, zero
feedback path), which is perfect vacuously, and fill all Campbell/intensity fields by
their defining equalities.  Hence any probability law `palm` on marked pairs that is
almost surely forward is the Palm law of an actual `StationaryForwardMatching`, whose
mark laws are the two mark marginals of `palm`.

Applied to the recoded legal Palm
`carrierRecodedLegalPalm Q = (legalMarkedJointPalm q Q.law).map carrierRecodePair`
this yields an abstract carrier with exactly the recoded legal Palm, and therefore a
nonempty abstract bounded second-moment class as soon as the recoded Palm has a
finite, bounded displacement second moment and is almost surely forward.

Since the promoted bridge module is not yet part of the built library at the time of
writing, the short recoding and criterion definitions are reproduced here under
local names (`carrierUnitMarkZero`, `carrierRecodePair`, `carrierRecodedLegalPalm`).
The analytic inputs -- almost-sure forwardness of the recoded Palm and its
clock-difference second moment -- remain interface hypotheses; deriving them from the
legal clock marginals and finite clock moments is the remaining sub-gap.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology
  OTSelector.PointProcess OTSelector.Probability
open scoped Topology ENNReal BigOperators

noncomputable section

set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

open OTSelector.PointProcess
open OTSelector.PointProcess.StationaryForwardMatching

/-! ## The zero unit mark and the recoding of legal Palm pairs -/

/-- The zero label of the unit mark interval. -/
def carrierUnitMarkZero : UnitMark := ⟨0, by norm_num⟩

/-- Canonical recoding of a legal Palm pair `((a,b), v)` to an abstract marked
pair of heights with zero unit mark at both endpoints. -/
def carrierRecodePair {q : ℕ} (m : PhysicalPairPalmMark (Fin q)) :
    MarkedCloudPoint × MarkedCloudPoint :=
  ((m.1.1, carrierUnitMarkZero), (m.1.2, carrierUnitMarkZero))

/-- The recoded abstract displacement is the difference of the two continuous
clocks. -/
theorem edgeDisplacement_carrierRecodePair {q : ℕ}
    (m : PhysicalPairPalmMark (Fin q)) :
    edgeDisplacement (carrierRecodePair m) = m.1.2 - m.1.1 := rfl

/-- The recoding is measurable. -/
theorem measurable_carrierRecodePair {q : ℕ} :
    Measurable (carrierRecodePair (q := q)) := by
  unfold carrierRecodePair
  fun_prop

/-- The recoded legal Palm law on abstract marked pairs. -/
def carrierRecodedLegalPalm {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) :
    Measure (MarkedCloudPoint × MarkedCloudPoint) :=
  (legalMarkedJointPalm q Q.law).map carrierRecodePair

/-- The recoded legal Palm is a probability measure. -/
theorem isProbabilityMeasure_carrierRecodedLegalPalm {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) :
    IsProbabilityMeasure (carrierRecodedLegalPalm Q) := by
  let _ : IsProbabilityMeasure (legalMarkedJointPalm q Q.law) := Q.palm_probability
  exact Measure.isProbabilityMeasure_map measurable_carrierRecodePair.aemeasurable

/-! ## The empty matching scene -/

/-- The empty matching scene: no source atoms, no target atoms, no edges and the
zero feedback path. -/
def legalEmptyScene : MatchingScene where
  source := fun _ ↦ 0
  target := fun _ ↦ 0
  edges := fun _ ↦ 0
  path := ⟨0, 0⟩

/-- The empty scene is perfect vacuously: its counting measures vanish. -/
theorem perfect_legalEmptyScene : PerfectEdgeConfiguration legalEmptyScene := by
  constructor <;>
    simp [legalEmptyScene, LocalConfiguration.countingMeasure,
      LocalConfiguration.shellMeasure]

/-! ## Carrier construction from a Palm probability law -/

/-- Any probability law on marked pairs that is almost surely forward is the Palm
law of an actual stationary forward matching carrier, whose source and target mark
laws are the two mark marginals of the Palm law. -/
theorem exists_stationaryForwardMatching_of_palm
    (palm : Measure (MarkedCloudPoint × MarkedCloudPoint)) [IsProbabilityMeasure palm]
    (hforward : ∀ᵐ p ∂palm, p.1.1 < p.2.1) :
    ∃ M : StationaryForwardMatching (palm.map (fun p ↦ p.1.2)) (palm.map (fun p ↦ p.2.2)),
      M.palm = palm :=
  ⟨{
    scene := legalEmptyScene
    palm := palm
    palm_isProbability := inferInstance
    pairCampbell := (volume : Measure ℝ).prod palm
    pairCampbell_eq := rfl
    sourceIntensity := (volume : Measure ℝ).prod (palm.map (fun p ↦ p.1.2))
    sourceIntensity_eq := rfl
    targetIntensity := (volume : Measure ℝ).prod (palm.map (fun p ↦ p.2.2))
    targetIntensity_eq := rfl
    inputCampbell := ((volume : Measure ℝ).prod (palm.map (fun p ↦ p.1.2))).prod
      ((volume : Measure ℝ).prod (palm.map (fun p ↦ p.2.2)))
    inputCampbell_eq := rfl
    forward := hforward
    perfect := perfect_legalEmptyScene
    source_mark_marginal := rfl
    target_mark_marginal := rfl }, rfl⟩

/-! ## The carrier with the recoded legal Palm -/

/-- The abstract stationary forward carrier whose Palm law is exactly the recoded
legal Palm of a legal stationary Poisson matching, provided that Palm is almost
surely forward. -/
theorem exists_stationaryForwardMatching_carrierRecodedLegalPalm
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hforward : ∀ᵐ p ∂carrierRecodedLegalPalm Q, p.1.1 < p.2.1) :
    ∃ M : StationaryForwardMatching
        ((legalMarkedJointPalm q Q.law).map carrierRecodePair |>.map
          (fun p ↦ p.1.2))
        ((legalMarkedJointPalm q Q.law).map carrierRecodePair |>.map
          (fun p ↦ p.2.2)),
      M.palm = carrierRecodedLegalPalm Q := by
  haveI : IsProbabilityMeasure (carrierRecodedLegalPalm Q) :=
    isProbabilityMeasure_carrierRecodedLegalPalm Q
  exact exists_stationaryForwardMatching_of_palm (carrierRecodedLegalPalm Q) hforward

/-- Nonemptiness of the abstract bounded second-moment class from an abstract
carrier with finite, bounded second-moment Palm law. -/
theorem carrier_boundedSecondMoment_nonempty
    {γ δ : Measure UnitMark} (M : StationaryForwardMatching γ δ) (B : ℝ)
    (hM : Integrable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦
      edgeDisplacement p ^ 2) M.palm)
    (hB : ∫ p, edgeDisplacement p ^ 2 ∂M.palm ≤ B) :
    (boundedSecondMomentClass (α := γ) (β := δ) B).Nonempty :=
  ⟨M, hM, hB⟩

/-- Capstone: the abstract bounded second-moment class is nonempty for the recoded
legal Palm of any legal stationary Poisson matching whose recoded Palm is almost
surely forward and has a finite, bounded displacement second moment. -/
theorem nonempty_boundedSecondMomentClass_carrierRecodedLegalPalm
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hforward : ∀ᵐ p ∂carrierRecodedLegalPalm Q, p.1.1 < p.2.1)
    {B : ℝ}
    (hInt : Integrable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦
      edgeDisplacement p ^ 2) (carrierRecodedLegalPalm Q))
    (hB : ∫ p, edgeDisplacement p ^ 2 ∂carrierRecodedLegalPalm Q ≤ B) :
    (boundedSecondMomentClass
      (α := (legalMarkedJointPalm q Q.law).map carrierRecodePair |>.map
        (fun p ↦ p.1.2))
      (β := (legalMarkedJointPalm q Q.law).map carrierRecodePair |>.map
        (fun p ↦ p.2.2)) B).Nonempty := by
  haveI : IsProbabilityMeasure (carrierRecodedLegalPalm Q) :=
    isProbabilityMeasure_carrierRecodedLegalPalm Q
  obtain ⟨M, hM⟩ := exists_stationaryForwardMatching_of_palm
    (carrierRecodedLegalPalm Q) hforward
  exact carrier_boundedSecondMoment_nonempty M B (by rwa [hM]) (by rwa [hM])

end OTSelector.Reconstruction

end
