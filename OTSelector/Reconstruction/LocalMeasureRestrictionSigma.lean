import OTSelector.Reconstruction.MarkedStationaryValueLegalInputWindowLocalLaw
import OTSelector.MeasureTheory.LocalFiniteMeasurePolish

/-!
# Compact restrictions generate the whole vague-measure Borel space

The sigma algebras of literal restrictions to an increasing compact exhaustion generate all
measurable events on the actual locally finite measure carrier.  Compact-test measurability,
already proved for this carrier, supplies the only determination step.
-/

open Set Function MeasureTheory Topology TopologicalSpace
open scoped CompactlySupported

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [PseudoMetrizableSpace X]
  [SigmaCompactSpace X] [SecondCountableTopology X]

/-- The information obtained by observing the entire input inside one compact window. -/
@[instance_reducible] def localMeasureRestrictionSigma (K : CompactExhaustion X) (n : ℕ) :
    MeasurableSpace (LocalFiniteMeasure X) :=
  (inferInstance : MeasurableSpace (LocalFiniteMeasure X)).comap
    (legalInputRestrictionLocal (K n))

/-- Restricting to a smaller window after a larger one gives the original smaller restriction. -/
theorem legalInputRestrictionLocal_comp_of_subset {U V : Set X}
    (hU : MeasurableSet U) (hUV : U ⊆ V) :
    legalInputRestrictionLocal U ∘ legalInputRestrictionLocal V =
      legalInputRestrictionLocal U := by
  funext μ
  apply Subtype.ext
  change ((μ : Measure X).restrict V).restrict U = (μ : Measure X).restrict U
  rw [Measure.restrict_restrict hU, inter_eq_left.mpr hUV]

theorem monotone_localMeasureRestrictionSigma (K : CompactExhaustion X) :
    Monotone (localMeasureRestrictionSigma K) := by
  intro n k hnk
  exact MeasurableSpace.comap_le_comap_of_eq_comp
    (legalInputRestrictionLocal (K n))
    (measurable_legalInputRestrictionLocal (K.isCompact n).measurableSet)
    (legalInputRestrictionLocal_comp_of_subset (K.isCompact n).measurableSet
      (K.subset hnk)).symm

/-- A compact test is unchanged by restriction to any window containing its support. -/
theorem testIntegral_legalInputRestrictionLocal {U : Set X} (hU : MeasurableSet U)
    (f : C_c(X, ℝ)) (hf : tsupport f ⊆ U) (μ : LocalFiniteMeasure X) :
    LocalFiniteMeasure.testIntegral (legalInputRestrictionLocal U μ) f =
      LocalFiniteMeasure.testIntegral μ f := by
  change (∫ x in U, f x ∂(μ : Measure X)) = ∫ x, f x ∂(μ : Measure X)
  rw [← integral_indicator hU]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ U
  · exact indicator_of_mem hx f
  · rw [indicator_of_notMem hx]
    exact (image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hf h))).symm

/-- Literal compact restrictions, over any compact exhaustion, generate the full Borel sigma
algebra of actual locally finite measures. -/
theorem iSup_localMeasureRestrictionSigma (K : CompactExhaustion X) :
    (⨆ n, localMeasureRestrictionSigma K n) =
      (inferInstance : MeasurableSpace (LocalFiniteMeasure X)) := by
  apply le_antisymm
  · refine iSup_le fun n ↦ ?_
    exact (measurable_legalInputRestrictionLocal (K.isCompact n).measurableSet).comap_le
  · suffices h : @Measurable (LocalFiniteMeasure X) (LocalFiniteMeasure X)
        (⨆ n, localMeasureRestrictionSigma K n) inferInstance id by
      simpa only [MeasurableSpace.comap_id] using h.comap_le
    refine @LocalFiniteMeasure.measurable_of_testIntegral X _ _ _ _ _ _ _ _
      (LocalFiniteMeasure X) (⨆ n, localMeasureRestrictionSigma K n) id ?_
    intro f
    obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact f.hasCompactSupport
    have hrestr : @Measurable (LocalFiniteMeasure X) (LocalFiniteMeasure X)
        (⨆ n, localMeasureRestrictionSigma K n) inferInstance
        (legalInputRestrictionLocal (K n)) :=
      Measurable.of_comap_le (le_iSup (localMeasureRestrictionSigma K) n)
    have ht := (LocalFiniteMeasure.continuous_testIntegral f).measurable.comp hrestr
    have heq : (fun μ : LocalFiniteMeasure X ↦ LocalFiniteMeasure.testIntegral
        (legalInputRestrictionLocal (K n) μ) f) =
        (fun μ ↦ LocalFiniteMeasure.testIntegral μ f) :=
      funext (fun μ ↦ testIntegral_legalInputRestrictionLocal
        (K.isCompact n).measurableSet f hn μ)
    change @Measurable _ _ (⨆ n, localMeasureRestrictionSigma K n) _
      (fun μ : LocalFiniteMeasure X ↦ LocalFiniteMeasure.testIntegral
        (legalInputRestrictionLocal (K n) μ) f) at ht
    rw [heq] at ht
    exact ht

end OTSelector.Reconstruction
