import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Semicontinuity.Basic

/-!
## Lemma skeleton

* **Conditions:** Locally compact Hausdorff Borel space; stated metrizability/exhaustion assumptions for extensionality.
* **Objects:** Measures finite on compacts with topology induced by actual compact-test integrals.
* **Proof detail:** Use Riesz representation, positivity/linearity closed conditions and compact products of readout intervals.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4*, Sections 436J–436K, Riesz representation on locally compact Hausdorff spaces.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=47
* Olav Kallenberg, *Random Measures, Theory and Applications (Springer 2017)*, Chapter 4 opening, pp. 109–110, and Section 4.1 “Weak and vague topologies”, pp. 111–117.
  https://link.springer.com/chapter/10.1007/978-3-319-41598-7_4

**Relationship to the sources:** This is a diffuse-measure carrier; no integer-valued or simple point-process restriction is imposed. Kallenberg uses bounded-support localization; here compact tests apply under the stated locally compact hypotheses.
-/

/-!
# Locally finite measures with their actual compact-test topology

This carrier permits diffuse transport plans. Compactly supported continuous
tests induce the topology; regularity and Riesz representation come from mathlib.
-/

open MeasureTheory Set Function Topology TopologicalSpace
open scoped CompactlySupported

noncomputable section
namespace OTSelector.Probability

variable (X : Type*) [TopologicalSpace X] [MeasurableSpace X]

/-- Measures finite on every compact set, including diffuse measures. -/
def LocalFiniteMeasure := {μ : Measure X // IsFiniteMeasureOnCompacts μ}

namespace LocalFiniteMeasure

variable {X}

instance : Coe (LocalFiniteMeasure X) (Measure X) := ⟨Subtype.val⟩

instance (μ : LocalFiniteMeasure X) : IsFiniteMeasureOnCompacts (μ : Measure X) := μ.property

variable [T2Space X] [LocallyCompactSpace X] [BorelSpace X]

/-- The actual compact-test integral, with its integrability already supplied. -/
def testIntegral (μ : LocalFiniteMeasure X) (f : C_c(X, ℝ)) : ℝ :=
  ∫ x, f x ∂(μ : Measure X)

/-- The vague topology is induced by all actual compact-test integrals. -/
instance : TopologicalSpace (LocalFiniteMeasure X) :=
  TopologicalSpace.induced (fun μ : LocalFiniteMeasure X ↦ testIntegral μ) inferInstance

omit [T2Space X] [LocallyCompactSpace X] [BorelSpace X] in
theorem continuous_testIntegral (f : C_c(X, ℝ)) :
    Continuous (fun μ : LocalFiniteMeasure X ↦ testIntegral μ f) := by
  have h : Continuous (fun μ : LocalFiniteMeasure X ↦ testIntegral μ) :=
    continuous_induced_dom
  exact (continuous_apply f).comp h

instance : MeasurableSpace (LocalFiniteMeasure X) := borel _

instance : BorelSpace (LocalFiniteMeasure X) := ⟨rfl⟩

variable [PseudoMetrizableSpace X] [SigmaCompactSpace X]

theorem testIntegral_injective :
    Injective (fun μ : LocalFiniteMeasure X ↦ testIntegral μ) := by
  intro μ ν h
  apply Subtype.ext
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  exact congrFun h f

theorem isEmbedding_testIntegral :
    IsEmbedding (fun μ : LocalFiniteMeasure X ↦ testIntegral μ) :=
  ⟨⟨rfl⟩, testIntegral_injective⟩

instance : T2Space (LocalFiniteMeasure X) := isEmbedding_testIntegral.t2Space

/-- Every positive compact-test functional is the readout of an actual measure. -/
def ofPositiveFunctional (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ) : LocalFiniteMeasure X :=
  ⟨RealRMK.rieszMeasure Λ, inferInstance⟩

omit [PseudoMetrizableSpace X] [SigmaCompactSpace X] in
@[simp]
theorem testIntegral_ofPositiveFunctional (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ)
    (f : C_c(X, ℝ)) : testIntegral (ofPositiveFunctional Λ) f = Λ f :=
  RealRMK.integral_rieszMeasure Λ f

/-- Linear and order relations characterize actual compact-test readouts. -/
def IsPositiveTestReadout (L : C_c(X, ℝ) → ℝ) : Prop :=
  (∀ f g, L (f + g) = L f + L g) ∧
  (∀ (c : ℝ) f, L (c • f) = c • L f) ∧ Monotone L

omit [PseudoMetrizableSpace X] [SigmaCompactSpace X] in
theorem range_testIntegral :
    range (fun μ : LocalFiniteMeasure X ↦ testIntegral μ) =
      {L | IsPositiveTestReadout L} := by
  ext L
  constructor
  · rintro ⟨μ, rfl⟩
    let Λ := CompactlySupportedContinuousMap.integralPositiveLinearMap (μ : Measure X)
    exact ⟨Λ.map_add, Λ.map_smul, Λ.monotone⟩
  · rintro ⟨hadd, hsmul, hmono⟩
    let Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
      { toFun := L, map_add' := hadd, map_smul' := hsmul, monotone' := hmono }
    exact ⟨ofPositiveFunctional Λ, funext (testIntegral_ofPositiveFunctional Λ)⟩

omit [PseudoMetrizableSpace X] [SigmaCompactSpace X] in
theorem isClosed_range_testIntegral :
    IsClosed (range (fun μ : LocalFiniteMeasure X ↦ testIntegral μ)) := by
  rw [range_testIntegral]
  simp only [IsPositiveTestReadout, Monotone, ofPred_and, ofPred_forall]
  refine (isClosed_iInter (fun f ↦ isClosed_iInter (fun g ↦ ?_))).inter
    ((isClosed_iInter (fun c ↦ isClosed_iInter (fun f ↦ ?_))).inter
      (isClosed_iInter (fun f ↦ isClosed_iInter (fun g ↦
        isClosed_iInter (fun _ ↦ ?_)))))
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · exact isClosed_le (continuous_apply _) (continuous_apply _)

theorem isClosedEmbedding_testIntegral :
    IsClosedEmbedding (fun μ : LocalFiniteMeasure X ↦ testIntegral μ) :=
  ⟨isEmbedding_testIntegral, isClosed_range_testIntegral⟩

/-- Bounds on all compact tests form a genuinely compact family of diffuse measures. -/
theorem isCompact_testIntegral_bounds (C : C_c(X, ℝ) → ℝ) :
    IsCompact {μ : LocalFiniteMeasure X | ∀ f, testIntegral μ f ∈ Icc (-C f) (C f)} := by
  have h := isClosedEmbedding_testIntegral.isCompact_preimage
    (isCompact_univ_pi (fun f : C_c(X, ℝ) ↦ isCompact_Icc (a := -C f) (b := C f)))
  simpa only [preimage, mem_pi, mem_univ, forall_true_left] using h

omit [T2Space X] in
/-- Open-window mass is the supremum of compact-test readouts supported there. -/
theorem open_measure_eq_iSup_testIntegral (μ : LocalFiniteMeasure X)
    {U : Set X} (hU : IsOpen U) :
    (μ : Measure X) U =
      ⨆ (f : C_c(X, ℝ)) (_ : EqOn f 0 Uᶜ) (_ : ∀ x, f x ∈ Icc 0 1),
        ENNReal.ofReal (testIntegral μ f) := by
  apply le_antisymm
  · apply le_of_forall_lt (fun r hr ↦ ?_)
    simp only [lt_iSup_iff, exists_prop]
    obtain ⟨K, hKU, hK, hrK⟩ := hU.exists_lt_isCompact hr
    obtain ⟨f, hfK, hfU, hfcomp, hfb⟩ := exists_continuous_one_zero_of_isCompact
      hK hU.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKU)
    let g : C_c(X, ℝ) := ⟨f, hfcomp⟩
    refine ⟨g, hfU, hfb, hrK.trans_le ?_⟩
    apply g.integrable.measure_le_integral
    · exact Filter.Eventually.of_forall (fun x ↦ (hfb x).1)
    · intro x hx
      exact (hfK hx).ge
  · simp only [iSup_le_iff]
    intro f hfU hfb
    exact integral_le_measure (fun x _ ↦ (hfb x).2) (fun x hx ↦ (hfU hx).le)

omit [T2Space X] in
/-- Open rectangle evaluation is lower semicontinuous for diffuse plan limits. -/
theorem lowerSemicontinuous_measure_open {U : Set X} (hU : IsOpen U) :
    LowerSemicontinuous (fun μ : LocalFiniteMeasure X ↦ (μ : Measure X) U) := by
  have heq := funext (fun μ : LocalFiniteMeasure X ↦ open_measure_eq_iSup_testIntegral μ hU)
  rw [heq]
  exact lowerSemicontinuous_iSup (fun f ↦ lowerSemicontinuous_iSup (fun _ ↦
    lowerSemicontinuous_iSup (fun _ ↦
      (ENNReal.continuous_ofReal.comp (continuous_testIntegral f)).lowerSemicontinuous)))

end LocalFiniteMeasure
end OTSelector.Probability
