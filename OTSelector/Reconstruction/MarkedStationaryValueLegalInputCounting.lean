import OTSelector.PointProcess.FiniteConfiguration
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputJointStationarity
import OTSelector.PointProcess.LocalConfiguration.Polish
import OTSelector.PointProcess.LocalConfigurationTuple
import OTSelector.PointProcess.LocalConfiguration.Support

/-!
# Integer measures in the same original legal input scene

The canonical original legal optimum has unit edge atoms, and its colored
inputs have the original unit point atoms. Integer configurations form a
closed subspace of the vague measure carrier. Thus the same joint weak limit
retains integer edge and input measures; no fresh configuration law is coupled
after taking the limit.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
local instance markedStationaryValueLegalInputCountingColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)
local instance markedStationaryValueLegalInputCountingConfigurationTopology
    {X : Type*} [MetricSpace X] [ProperSpace X] (base : X) :
    TopologicalSpace (LocalConfiguration base) := LocalConfiguration.vagueTopology base

/-- This very measure, including every multiplicity, is an integer point measure. -/
def IsLegalCountingMeasure {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (base : X) (μ : LocalFiniteMeasure X) : Prop :=
  μ ∈ range (LocalConfiguration.toLocalFiniteMeasure (base := base))


/-- Integer counting measures are closed in the actual vague carrier. -/
theorem isClosed_isLegalCountingMeasure
    {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] (base : X) :
    IsClosed {μ : LocalFiniteMeasure X | IsLegalCountingMeasure base μ} :=
  LocalConfiguration.isClosedEmbedding_toLocalFiniteMeasure.isClosed_range

/-- The original rooted canonical legal edge plan has unit integer atoms. -/
theorem isLegalCountingMeasure_legalMarkedOptimalInputObservation_plan
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ)) :
    IsLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q)
      (legalMarkedOptimalInputObservation q hL kin g t p).1.1 := by
  classical
  let σ := firstLegalMarkedOptimalMatching q (mSourceCount p.1) (mTargetCount p.1)
    id id (L ^ q) kin g t p.1
  let f := fun e : Fin (mSourceCount p.1) × Fin (mTargetCount p.1) ↦
    physicalSceneEdgeReroot ((fun _ ↦ L / 2) + p.2)
      (legalMarkedPhysicalEdge q L p.1 e.1 e.2)
  obtain ⟨c, hc⟩ := PointProcess.exists_configuration_finset_dirac (0 : LegalMarkedPhysicalEdge q) σ.edges f
  refine ⟨c, ?_⟩
  apply Subtype.ext
  change LocalConfiguration.countingMeasure c =
    physicalSceneRootedPlan (legalMarkedNormalizedOptimalPlan q L kin g t p.1)
      (legalMarkedCenteredCoordinate q L) Prod.snd (L ^ q) p.2
  rw [physicalSceneRootedPlan_legalMarkedNormalizedOptimalPlan_centered q hL]
  rw [legalMarkedOptimalPlan, legalMarkedFixedOptimalPlan, Measure.map_finset_sum
    (physicalSceneEdgeReroot _).continuous.measurable.aemeasurable]
  simpa only [Measure.map_dirac] using hc

/-- Every original colored input atom also has its unchanged unit multiplicity. -/
theorem isLegalCountingMeasure_legalMarkedOptimalInputObservation_input
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ)) :
    IsLegalCountingMeasure (0 : LegalColoredInputPoint q)
      (legalMarkedOptimalInputObservation q hL kin g t p).2 := by
  classical
  let bs := mapBlockData (fun x ↦ (x, (0 : Fin 2)))
    (legalInputRootWindowPrefix q (Real.toNNReal L) univ (p.2, p.1.1))
  let bt := mapBlockData (fun x ↦ (x, (1 : Fin 2)))
    (legalInputRootWindowPrefix q (Real.toNNReal L) univ (p.2, p.1.2))
  let f : Fin bs.1 ⊕ Fin bt.1 → LegalColoredInputPoint q := Sum.elim bs.2 bt.2
  obtain ⟨c, hc⟩ := PointProcess.exists_configuration_sum_dirac (0 : LegalColoredInputPoint q) f
  refine ⟨c, ?_⟩
  apply Subtype.ext
  change LocalConfiguration.countingMeasure c = legalMarkedRootedColoredInputMeasure q L p
  rw [hc, Fintype.sum_sum_type]
  rfl

local instance markedStationaryValueLegalInputCountingPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalInputCountingInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace

/-- The same original joint weak limit retains integer matching atoms and
integer input atoms, with their original correlations. -/
theorem ae_isLegalCountingMeasure_of_legalMarkedInputSceneLaw_tendsto
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q)) :
    ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      IsLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q) s.1.1 ∧
        IsLegalCountingMeasure (0 : LegalColoredInputPoint q) s.2 := by
  let K : Set (LegalMarkedOptimalInputScene q) := {s |
    IsLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q) s.1.1 ∧
      IsLegalCountingMeasure (0 : LegalColoredInputPoint q) s.2}
  have hK : IsClosed K :=
    ((isClosed_isLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q)).preimage
      continuous_fst.fst).inter
        ((isClosed_isLegalCountingMeasure (0 : LegalColoredInputPoint q)).preimage continuous_snd)
  have hn (k : ℕ) : (legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k) : Measure (LegalMarkedOptimalInputScene q)) Kᶜ = 0 := by
    apply (ae_map_iff (measurable_legalMarkedOptimalInputObservation q (hL k) hk hg t).aemeasurable
      hK.measurableSet).mpr
    exact Eventually.of_forall fun p ↦
      ⟨isLegalCountingMeasure_legalMarkedOptimalInputObservation_plan q (hL k) kin g t p,
        isLegalCountingMeasure_legalMarkedOptimalInputObservation_input q (hL k) kin g t p⟩
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hK.isOpen_compl
  change (Q : Measure (LegalMarkedOptimalInputScene q)) Kᶜ ≤
    atTop.liminf (fun k ↦ (legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k) : Measure (LegalMarkedOptimalInputScene q)) Kᶜ) at hle
  simp only [hn, liminf_const] at hle
  exact le_antisymm hle bot_le

/-- Integer matching atoms have one countable original edge carrier. This is
obtained from the actual optimizer limit, not an added support assumption. -/
theorem ae_countable_edge_carrier_of_legalMarkedInputSceneLaw_tendsto
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q)) :
    ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      ∃ E : Set (LegalMarkedPhysicalEdge q), E.Countable ∧
        ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)), e ∈ E := by
  filter_upwards [ae_isLegalCountingMeasure_of_legalMarkedInputSceneLaw_tendsto
    q α β kin hk g hg t L hL hweak] with s hs
  obtain ⟨c, hc⟩ := hs.1
  refine ⟨Function.support (LocalConfiguration.multiplicity c),
    LocalConfiguration.countable_multiplicity_support c, ?_⟩
  have heq := congrArg Subtype.val hc
  change LocalConfiguration.countingMeasure c = (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) at heq
  rw [← heq]
  exact LocalConfiguration.ae_mem_multiplicity_support c

end OTSelector.Reconstruction
