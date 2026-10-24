import OTSelector.Reconstruction.FinslerOriginalSceneCountIdentity
import OTSelector.Reconstruction.FinslerOriginalAeFullMatching
import OTSelector.Reconstruction.FinslerOriginalCloudCountDefinitionalAudit

/-!
# Scene-to-cloud count transfer through the Palm construction

This module states and uses the exact missing hypothesis for the scene-to-cloud
count transfer, and wires the transfer into the unconditional scene count chain.

## What the Palm construction actually transfers

The scene law (legalMarkedOptimalRootedSceneLaw) and the cloud law
(twoMarkedCloudLaw) are related by the Palm/rooted construction: the scene edge
measure is the rooted scene's local finite measure, while the cloud side supplies
the count strata.  The Palm field palm_probability of
LegalWeightedStationaryPoissonMatching transfers Palm-square probabilities but
does NOT transport the total edge mass to the cloud count coordinates.  The
missing bridge is exactly the following named hypothesis:

  **PalmSceneCloudMassTransfer L r kin g t s w**:
  (s.1.1).univ = (legalMarkedOptimalPlan q L r kin g t w).univ,

i.e. the scene edge total mass equals the realized cloud plan total mass on the
Palm-coupling event.  It is a statement about the Palm coupling, not about the
raw cloud law (where the count equality fails, cf. the definitional audit).

## Proved

1. **scene_totalMass_eq_sourceCount_of_palm_transfer**: under the mass transfer
   hypothesis and the realized plan mass = mSourceCount, the scene shell
   cardinality sum equals the cloud source count.
2. **ae_scene_totalMass_eq_minCount_of_palm_transfer**: if the mass transfer
   holds a.e. under the cloud law (with a.e. increasing clocks), then a.e. the
   scene shell cardinality sum equals min (mSourceCount) (mTargetCount).
3. **ae_scene_totalMass_eq_sourceCount_of_palm_transfer_and_counts_eq**: under
   the additional Palm count equality mSourceCount = mTargetCount, a.e. the scene
   shell cardinality sum equals mSourceCount - the full scene-to-cloud count
   identity, conditional only on the Palm transfer and Palm count equality.
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

/-- **Named Palm scene-to-cloud mass transport hypothesis.**  The scene edge
total mass equals the realized cloud plan total mass. -/
def PalmSceneCloudMassTransfer {q : ℕ} (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (s : LegalMarkedOptimalInputScene q) (ω : TwoMarkedCloudSpace q ℝ ℝ) : Prop :=
  (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) Set.univ =
    legalMarkedOptimalPlan q L r kin g t ω Set.univ

/-- **Scene total mass equals the cloud source count** under the Palm mass
transfer and the realized plan mass identity. -/
theorem scene_totalMass_eq_sourceCount_of_palm_transfer
    {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) (ω : TwoMarkedCloudSpace q ℝ ℝ)
    (L r : ℝ) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (hmass : PalmSceneCloudMassTransfer L r kin g t s ω)
    (hplan : legalMarkedOptimalPlan q L r kin g t ω Set.univ =
      (mSourceCount ω : ℝ≥0∞)) :
    (∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞)) = (mSourceCount ω : ℝ≥0∞) := by
  rw [← scene_edge_totalMass hs]
  exact hmass.trans hplan

/-- **A.e. scene total mass equals the minimum of the cloud counts** under the
Palm mass transfer. -/
theorem ae_scene_totalMass_eq_minCount_of_palm_transfer
    {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s)
    (L r : ℝ) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0)
    (horder : ∀ᵐ p ∂α.prod β, p.1 < p.2)
    (htransfer : ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      PalmSceneCloudMassTransfer L r kin g t s ω) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      (∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞)) =
        ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ≥0∞) := by
  filter_upwards [ae_legalMarkedOptimalPlan_univ_eq_min q L r kin g t α β ρ horder,
    htransfer] with ω hplan hm
  rw [← scene_edge_totalMass hs]
  exact hm.trans hplan

/-- **A.e. scene total mass equals the cloud source count** under the Palm mass
transfer and the Palm count equality. -/
theorem ae_scene_totalMass_eq_sourceCount_of_palm_transfer_and_counts_eq
    {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s)
    (L r : ℝ) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0)
    (horder : ∀ᵐ p ∂α.prod β, p.1 < p.2)
    (htransfer : ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      PalmSceneCloudMassTransfer L r kin g t s ω)
    (hcounts : ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      mSourceCount ω = mTargetCount ω) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      (∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞)) = (mSourceCount ω : ℝ≥0∞) := by
  filter_upwards [ae_scene_totalMass_eq_minCount_of_palm_transfer hs L r kin g t
    α β ρ horder htransfer, hcounts] with ω htotal hc
  rw [htotal, hc, min_self]

end OTSelector.Reconstruction
