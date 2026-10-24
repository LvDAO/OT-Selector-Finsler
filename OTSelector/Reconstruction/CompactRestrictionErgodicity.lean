import OTSelector.Probability.GeneratingLocalErgodicity
import OTSelector.Reconstruction.LocalMeasureRestrictionSigma

/-! # Ergodicity on the whole locally finite input from independent compact restrictions -/

open Set Function MeasureTheory ProbabilityTheory Topology TopologicalSpace

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [PseudoMetrizableSpace X]
  [SigmaCompactSpace X] [SecondCountableTopology X]

/-- Independence of the actual compact restriction from a translated copy proves ergodicity
for the complete random measure, including every measurable whole-input event. -/
theorem ergodic_of_compact_restriction_independence
    (P : Measure (LocalFiniteMeasure X)) [IsProbabilityMeasure P]
    (T : LocalFiniteMeasure X → LocalFiniteMeasure X) (hT : MeasurePreserving T P P)
    (hind : ∀ (U : Set X), IsCompact U →
      ∃ k : ℕ, IndepFun (legalInputRestrictionLocal U)
        (legalInputRestrictionLocal U ∘ T^[k]) P) : Ergodic T P := by
  let K := CompactExhaustion.choice X
  apply ergodic_of_generating_local_independence P T hT (localMeasureRestrictionSigma K)
    (monotone_localMeasureRestrictionSigma K) (iSup_localMeasureRestrictionSigma K)
  intro n B hBn
  rcases hBn with ⟨D, hD, rfl⟩
  obtain ⟨k, hk⟩ := hind (K n) (K.isCompact n)
  refine ⟨k, ?_⟩
  have hm := measurable_legalInputRestrictionLocal (K.isCompact n).measurableSet
  exact (indepFun_iff_indepSet_preimage hm (hm.comp (hT.iterate k).measurable)).mp hk
    D D hD hD

end OTSelector.Reconstruction
