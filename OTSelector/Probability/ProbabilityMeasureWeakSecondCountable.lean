import OTSelector.MeasureTheory.ProbabilityMeasureWeakBorel

/-!
# Countability of the actual weak probability topology

The probability slice of the existing compact-test carrier is homeomorphic
to the original weak probability space, so it inherits second countability.
-/
open MeasureTheory TopologicalSpace
noncomputable section
namespace OTSelector.Probability
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [PseudoMetrizableSpace X] [SigmaCompactSpace X] [SecondCountableTopology X]

/-- The two original presentations of a probability measure have the same
topology; neither changes the underlying measure. -/
def probabilityVagueHomeomorph : ProbabilityMeasure X ≃ₜ ProbabilityVagueCarrier X where
  toFun := probabilityToVagueCarrier
  invFun := vagueCarrierToProbability
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_probabilityToVagueCarrier
  continuous_invFun := continuous_vagueCarrierToProbability

/-- The actual weak probability topology is second countable. -/
theorem probabilityMeasure_weakSecondCountable :
    SecondCountableTopology (ProbabilityMeasure X) := by
  let _instLocalFiniteSecond :
      SecondCountableTopology (OTSelector.Probability.LocalFiniteMeasure X) :=
    (OTSelector.Probability.LocalFiniteMeasure.isClosedEmbedding_separatingTestCode
      (CompactExhaustion.choice X)).isEmbedding.secondCountableTopology
  let _instProbabilityVagueSecond : SecondCountableTopology (ProbabilityVagueCarrier X) :=
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding
      (Subtype.val : ProbabilityVagueCarrier X → OTSelector.Probability.LocalFiniteMeasure X))
      |>.secondCountableTopology
  exact probabilityVagueHomeomorph.isEmbedding.secondCountableTopology

/-- The same weak probability topology is separable, as needed for the
original paired-plan Prokhorov extraction. -/
theorem probabilityMeasure_weakSeparable : SeparableSpace (ProbabilityMeasure X) := by
  let _inst : SecondCountableTopology (ProbabilityMeasure X) := probabilityMeasure_weakSecondCountable
  infer_instance

end OTSelector.Probability
