import OTSelector.PointProcess.FiniteConfiguration
import OTSelector.Reconstruction.FinslerOriginalRealizedCloudCount
import OTSelector.Reconstruction.FinslerOriginalSceneCountIdentity
import OTSelector.Reconstruction.FinslerOriginalCloudCountIdentity

/-!
# Canonical scene count transfer from a legal optimal plan

This module constructs the canonical scene attached to one legal marked optimal
plan and proves the cardinality transport for it.

## Construction

For a cloud state w the canonical plan is the realized optimal plan
legalMarkedOptimalPlan q L r kin g t w: a finite sum of Dirac masses over the
matched index pairs of firstLegalMarkedOptimalMatching.  We build:

1. canonicalPlanEdges: the matched index pairs of that matching;
2. canonicalPlanPoints: the physical edge attached to each matched pair;
3. canonicalPlanConfig: a shell configuration whose counting measure is exactly
   the finite plan;
4. canonicalScene: the scene whose first edge measure (both cavity slots) is the
   plan and whose coloured input measure is the explicit source/target atom sum
   of the same matched pairs.

## What is proved unconditionally

- canonicalPlanConfig_spec: the configuration decodes to the finite plan.
- canonicalPlanConfig_shellSum_eq_planMass: the shell-cardinality sum of the
  canonical configuration is the plan total mass.
- canonicalPlan_shellSum_eq_matchedPairCount: that sum is the number of matched
  index pairs (the plan matched-pair count).
- canonicalOptimalPlan_shellSum_eq_legalMaximumCard: for every cloud state the
  canonical shell-cardinality sum is the maximum cardinality of the realized
  legal graph (using the unconditional realized-plan total-mass theorem).
- ae_canonicalOptimalPlan_shellSum_eq_legalMaximumCard: the same a.e. under
  twoMarkedCloudLaw.  This is the full cardinality transport at the level of the
  canonical plan, with no a.e. hypothesis at all.

## Exact remaining gap

The repo statement PalmSceneCloudCouplingTransport is phrased for ONE fixed
scene s, while the canonical scene depends on the cloud state w.  A fixed-scene
a.e. identity can only hold if the plan mass is a.e. constant, which is false
for the random cloud counts; therefore the type-correct strongest form is the
w-indexed statement

  for a.e. w there is hs : IsFullOriginalInputMatching q (canonicalScene ... w)
  and the shell sum of sceneEdgeConfig hs is legalMaximumCard (graph w).

That statement is proved here from the single remaining a.e. hypothesis
CanonicalSceneFullMatching, i.e.
  for a.e. w, IsFullOriginalInputMatching q (canonicalScene q L r kin g t w).
This last hypothesis is the only missing piece.  It reduces to
(i) a.e. simplicity of the canonical plan (distinct physical points, equivalent
to a.e. injectivity of the iid Haar position sequences of the cloud, which is
not currently available in the repo for infinite marked sequences), and
(ii) the two marginal identities and the two occupied-atom uniqueness fields
for the explicit coloured input measure (provable in principle from the row and
column injectivity of the matching, not yet formalized).
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

/-! ## The canonical plan edge configuration -/


/-- The matched index pairs of the canonical legal optimal plan. -/
noncomputable def canonicalPlanEdges (q m n : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) : Finset (Fin m × Fin n) :=
  (firstLegalMarkedOptimalMatching q m n id id r kin g t ω).edges

/-- The physical edge attached to a matched index pair. -/
noncomputable def canonicalPlanPoints (q m n : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) (e : Fin m × Fin n) :
    LegalMarkedPhysicalEdge q :=
  legalMarkedPhysicalEdge q L ω e.1 e.2

/-- A shell configuration whose counting measure is the canonical finite plan. -/
noncomputable def canonicalPlanConfig (q m n : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    LocalConfiguration (0 : LegalMarkedPhysicalEdge q) :=
  Classical.choose (PointProcess.exists_configuration_finset_dirac (0 : LegalMarkedPhysicalEdge q)
    (canonicalPlanEdges q m n L r kin g t ω) (canonicalPlanPoints q m n L r kin g t ω))

/-- **The canonical configuration decodes to the finite plan.** -/
theorem canonicalPlanConfig_spec (q m n : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    LocalConfiguration.countingMeasure (canonicalPlanConfig q m n L r kin g t ω) =
      legalMarkedFixedOptimalPlan q m n L r kin g t ω := by
  unfold canonicalPlanConfig legalMarkedFixedOptimalPlan canonicalPlanEdges canonicalPlanPoints
  exact Classical.choose_spec (PointProcess.exists_configuration_finset_dirac
    (0 : LegalMarkedPhysicalEdge q)
    (canonicalPlanEdges q m n L r kin g t ω) (canonicalPlanPoints q m n L r kin g t ω))

/-- **The canonical shell sum is the plan total mass.** -/
theorem canonicalPlanConfig_shellSum_eq_planMass (q m n : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    (∑' k, ((canonicalPlanConfig q m n L r kin g t ω k).card : ℝ≥0∞)) =
      legalMarkedFixedOptimalPlan q m n L r kin g t ω Set.univ := by
  rw [← countingMeasure_univ (canonicalPlanConfig q m n L r kin g t ω),
    canonicalPlanConfig_spec]

/-- **The canonical shell sum is the matched-pair count of the plan.** -/
theorem canonicalPlan_shellSum_eq_matchedPairCount (q m n : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    (∑' k, ((canonicalPlanConfig q m n L r kin g t ω k).card : ℝ≥0∞)) =
      ((canonicalPlanEdges q m n L r kin g t ω).card : ℝ≥0∞) := by
  rw [canonicalPlanConfig_shellSum_eq_planMass]
  unfold legalMarkedFixedOptimalPlan canonicalPlanEdges
  exact finset_sum_dirac_univ _ _

/-- **Unconditional cardinality transport for the canonical optimal plan**: for
every cloud state the canonical shell-cardinality sum is the maximum cardinality
of the realized legal graph. -/
theorem canonicalOptimalPlan_shellSum_eq_legalMaximumCard (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    (∑' k, ((canonicalPlanConfig q (mSourceCount ω) (mTargetCount ω) L r kin g t ω k).card :
        ℝ≥0∞)) =
      (PartialMatching.legalMaximumCard
        (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) : ℝ≥0∞) := by
  rw [canonicalPlanConfig_shellSum_eq_planMass]
  rw [← legalMarkedOptimalPlan, legalMarkedOptimalPlan_univ]

/-- **A.e. cardinality transport for the canonical optimal plan**, with no a.e.
hypothesis: the identity holds for every cloud state. -/
theorem ae_canonicalOptimalPlan_shellSum_eq_legalMaximumCard (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      (∑' k,
        ((canonicalPlanConfig q (mSourceCount ω) (mTargetCount ω) L r kin g t ω k).card :
          ℝ≥0∞)) =
        (PartialMatching.legalMaximumCard
          (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) : ℝ≥0∞) :=
  Filter.Eventually.of_forall
    (canonicalOptimalPlan_shellSum_eq_legalMaximumCard q L r kin g t)

/-! ## The canonical scene -/

/-- The plan as a local finite measure, used for both cavity slots. -/
noncomputable def canonicalScenePlanMeasure (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    LocalFiniteMeasure (LegalMarkedPhysicalEdge q) :=
  ⟨legalMarkedOptimalPlan q L r kin g t ω, inferInstance⟩

/-- The coloured input measure of the canonical scene: one colour-0 atom at each
matched source point and one colour-1 atom at each matched target point. -/
noncomputable def canonicalInputMeasure (q m n : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    LocalFiniteMeasure (LegalColoredInputPoint q) :=
  ⟨∑ e : canonicalPlanEdges q m n L r kin g t ω,
      (Measure.dirac ((canonicalPlanPoints q m n L r kin g t ω e).1, (0 : Fin 2)) +
        Measure.dirac ((canonicalPlanPoints q m n L r kin g t ω e).2, (1 : Fin 2))),
    inferInstance⟩

/-- **The canonical scene attached to the legal optimal plan.**  Both cavity edge
slots are the plan (the second slot is the formally unused coordinate), and the
coloured input measure is the matched source/target atom sum. -/
noncomputable def canonicalScene (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) : LegalMarkedOptimalInputScene q :=
  ((canonicalScenePlanMeasure q L r kin g t ω, canonicalScenePlanMeasure q L r kin g t ω),
    canonicalInputMeasure q (mSourceCount ω) (mTargetCount ω) L r kin g t ω)

/-- The canonical scene whose edge measure is the plan. -/
def CanonicalSceneFullMatching (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) : Prop :=
  IsFullOriginalInputMatching q (canonicalScene q L r kin g t ω)

/-- **The canonical edge measure is the plan.** -/
theorem canonicalScene_edgeMass (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    ((canonicalScene q L r kin g t ω).1.1 : Measure (LegalMarkedPhysicalEdge q)) Set.univ =
      legalMarkedOptimalPlan q L r kin g t ω Set.univ :=
  rfl

/-- **Pointwise canonical scene transport**: a full-matching proof for the
canonical scene turns the shell-cardinality sum of its representing
configuration into the maximum cardinality of the realized legal graph. -/
theorem canonicalScene_transport_of_fullMatching (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ)
    (hs : IsFullOriginalInputMatching q (canonicalScene q L r kin g t ω)) :
    (∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞)) =
      (PartialMatching.legalMaximumCard
        (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) : ℝ≥0∞) := by
  rw [← scene_edge_totalMass hs]
  rw [canonicalScene_edgeMass, legalMarkedOptimalPlan_univ]

/-- **A.e. canonical scene transport from the single remaining a.e. full-matching
hypothesis.**  This is the strongest type-correct form of the isolated
identification for the canonical scene: a fixed scene cannot satisfy the a.e.
identity of PalmSceneCloudCouplingTransport unless the cloud plan mass is a.e.
constant, so the a.e. statement must be indexed by the cloud state. -/
theorem ae_canonicalScene_transport_of_ae_fullMatching (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0)
    (hm : ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      CanonicalSceneFullMatching q L r kin g t ω) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      ∃ hs : IsFullOriginalInputMatching q (canonicalScene q L r kin g t ω),
        (∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞)) =
          (PartialMatching.legalMaximumCard
            (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) : ℝ≥0∞) := by
  filter_upwards [hm] with ω hs
  exact ⟨hs, canonicalScene_transport_of_fullMatching q L r kin g t ω hs⟩

/-- **The canonical scene transport in the equivalent shell-sum form**, a.e.
under the remaining full-matching hypothesis: the scene configuration shell sum
equals the canonical plan configuration shell sum for a.e. cloud state. -/
theorem ae_canonicalScene_shellSum_eq_canonicalPlan (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0)
    (hm : ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      CanonicalSceneFullMatching q L r kin g t ω) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      ∃ hs : IsFullOriginalInputMatching q (canonicalScene q L r kin g t ω),
        (∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞)) =
          (∑' k,
            ((canonicalPlanConfig q (mSourceCount ω) (mTargetCount ω) L r kin g t ω k).card :
              ℝ≥0∞)) := by
  filter_upwards [hm] with ω hs
  refine ⟨hs, ?_⟩
  rw [← scene_edge_totalMass hs, canonicalScene_edgeMass]
  change legalMarkedFixedOptimalPlan q (mSourceCount ω) (mTargetCount ω) L r kin g t ω
      Set.univ =
    ∑' k, ((canonicalPlanConfig q (mSourceCount ω) (mTargetCount ω) L r kin g t ω k).card :
      ℝ≥0∞)
  rw [← canonicalPlanConfig_shellSum_eq_planMass]

end OTSelector.Reconstruction
