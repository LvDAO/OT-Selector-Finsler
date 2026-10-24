import OTSelector.Reconstruction.FinslerOriginalSceneCardinalityIdentity
import OTSelector.Reconstruction.FinslerOriginalSceneCloudCountTransfer
import OTSelector.Reconstruction.FinslerOriginalAeFullMatching
import OTSelector.Reconstruction.FinslerOriginalRealizedCloudCount

/-!
# Reduction of the Palm mass transfer to a pure count identity

The PalmSceneCloudMassTransfer hypothesis of
FinslerOriginalSceneCloudCountTransfer contains the kinetic and probe data
(L, r, kin, g, t) only through the realized plan.  This module shows it is
EQUIVALENT to a pure count identity in which the kinetic data disappears, and
wires that reduced form into the a.e. count chain.

1. **PalmSceneCloudCountTransfer**: the reduced hypothesis
   (s.1.1).univ = legalMaximumCard (legalMarkedGraph ...) - a pure scene-support
   cardinality versus realized legal graph cardinality identity.
2. **palmSceneCloudMassTransfer_iff_countTransfer**: unconditional equivalence
   of the Palm mass transfer with the reduced count identity (the plan-mass
   theorem legalMarkedOptimalPlan_univ eliminates L, r, kin, g, t).
3. **ae_scene_mass_eq_minCount_of_countTransfer**: given the reduced identity
   a.e. under the cloud law (with a.e. increasing clocks), a.e. the scene edge
   total mass equals min (mSourceCount) (mTargetCount).

## Repository check for a unit-weight Campbell mass lane

The repository possesses a Campbell FACTORIZATION
(campbell_eq_volume_prod_palm in PointProcess/Campbell.lean and
campbell_eq_volume_prod_cubePalm in MarkedStationaryValuePalmCube) for measures
on a product of the clock line with a mark space, and a cost-averaged collapse
campbellAveragedFrozenCost_eq_tsum_mass_mul_palmReadout in
FinslerOriginalRootCocycle.  Neither is a unit-weight mass identity for the
SCENE edge measure: the scene edge measure lives on LegalMarkedPhysicalEdge q
(product of mark-clock pairs), not on a clock-line x mark-space product, so the
Campbell factorization does not apply to it and no unit-weight version exists.

## Exact remaining gap

The reduced identity PalmSceneCloudCountTransfer itself remains unproved: it is
the pure numeric statement "scene support cardinality = realized legal maximum
cardinality".  The scene side of it is unconditional (scene cardinality identity:
support edges are in bijection with occupied source atoms), and the cloud side is
unconditional (realized plan mass = legalMaximumCard, a.e. equal to
min counts); what is missing is the identification of the SCENE's counted pairs
with the CLOUD's realized matching pairs, i.e. a cardinality transport along the
Palm coupling.  The Palm construction transports probability and clock laws only,
and the Campbell modules transport cost averages, not unit weights.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open OTSelector.Probability OTSelector.PointProcess
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-- **Reduced Palm count transfer hypothesis**: scene edge total mass equals the
realized legal maximum cardinality.  Kinetic and probe data do not appear. -/
def PalmSceneCloudCountTransfer {q : ℕ} (s : LegalMarkedOptimalInputScene q)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) : Prop :=
  (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) Set.univ =
    ((PartialMatching.legalMaximumCard
      (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) : ℕ) :
        ℝ≥0∞)

/-- **The Palm mass transfer is EQUIVALENT to the pure count identity.** -/
theorem palmSceneCloudMassTransfer_iff_countTransfer
    {q : ℕ} {s : LegalMarkedOptimalInputScene q} (ω : TwoMarkedCloudSpace q ℝ ℝ)
    (L r : ℝ) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ) :
    PalmSceneCloudMassTransfer L r kin g t s ω ↔
      PalmSceneCloudCountTransfer s ω := by
  unfold PalmSceneCloudMassTransfer PalmSceneCloudCountTransfer
  rw [legalMarkedOptimalPlan_univ]

/-- **A.e. scene mass equals the minimum cloud count** under the reduced
identity. -/
theorem ae_scene_mass_eq_minCount_of_countTransfer
    {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0)
    (horder : ∀ᵐ p ∂α.prod β, p.1 < p.2)
    (htransfer : ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      PalmSceneCloudCountTransfer s ω) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) Set.univ =
        ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ≥0∞) := by
  filter_upwards [ae_legalMaximumCard_eq_min q α β ρ id id horder, htransfer]
    with ω hmin h
  unfold PalmSceneCloudCountTransfer at h
  rw [h, hmin]

end OTSelector.Reconstruction
