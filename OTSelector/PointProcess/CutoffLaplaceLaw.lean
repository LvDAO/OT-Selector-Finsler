import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasureCountableTests
import OTSelector.MeasureTheory.LocalFiniteMeasureKernel
import OTSelector.PointProcess.CompactLaplaceDetermination
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.MarkedStationaryValueLegalInputCutoffLaw.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.MarkedStationaryValueLegalInputCutoffLaw`; the selected original proof blocks follow. -/
section

/-!
# PointProcess.CutoffLaplaceLaw

## Lemma skeleton

* **Conditions:** Finite laws on the vague locally finite measure carrier and a nonnegative continuous spatial cutoff; a measurable window is contained in its one-level region when the cutoff is removed.
* **Objects:** Continuous cutoff multiplication, whole localized law equality from original compact Laplace observations and equality of restricted-window laws.
* **Proof detail:** Multiply compact tests by the same cutoff to identify vague continuity and Laplace observations; use compact Laplace law determination, then the exact restriction identity where the cutoff equals one.

## Mathematical sources

- [Olav Kallenberg, Random Measures, Theory and Applications (Springer 2017)](https://link.springer.com/chapter/10.1007/978-3-319-41598-7_4): Chapter 4 opening, pp. 109–110, and Section 4.1 “Weak and vague topologies”, pp. 111–117.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap28.pdf#page=4): Section 281E, Stone–Weierstrass theorem for a point-separating unital algebra.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27): Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Section 235G, integration along an inverse-measure-preserving map.

Source relation (composition): Localization/determination composition. The cutoff constructor uses the formal nonnegative density encoding; positivity is explicit for continuity/test formulas.
-/

/-!
# Exact compact input laws from the original Laplace observations

Multiplying an actual input measure by a fixed nonnegative continuous cutoff
is a continuous operation on the vague carrier. Its Laplace observations are
the original observations multiplied by that same cutoff. This turns equality
of the prescribed observations into equality of whole localized input laws.
A cutoff equal to one on a chosen window can then be removed by restriction.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped CompactlySupported ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [PseudoMetrizableSpace X] [SigmaCompactSpace X] [SecondCountableTopology X]

/-- The same actual input with a continuous cutoff weight; no points are
resampled and every original spatial coordinate, clock and color is retained. -/
def legalInputCutoffLocal (η : C(X, ℝ)) (μ : LocalFiniteMeasure X) : LocalFiniteMeasure X := by
  letI := IsLocallyFiniteMeasure.withDensity_ofReal (μ := (μ : Measure X)) η.continuous
  exact ⟨(μ : Measure X).withDensity (fun x ↦ ENNReal.ofReal (η x)), inferInstance⟩

/-- Compact observations of the weighted original input remain original tests. -/
theorem testIntegral_legalInputCutoffLocal (η : C(X, ℝ)) (hη : ∀ x, 0 ≤ η x)
    (μ : LocalFiniteMeasure X) (F : C_c(X, ℝ)) :
    LocalFiniteMeasure.testIntegral (legalInputCutoffLocal η μ) F =
      LocalFiniteMeasure.testIntegral μ (LocalFiniteMeasure.weightedContinuousTest F η) := by
  change (∫ x, F x ∂(μ : Measure X).withDensity (fun x ↦ ENNReal.ofReal (η x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul η.continuous.measurable.ennreal_ofReal
    (by exact .of_forall fun x ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hη _), smul_eq_mul]
  apply integral_congr_ae
  exact .of_forall fun x ↦ mul_comm _ _

/-- Continuous localization preserves weak observations of the original input. -/
theorem continuous_legalInputCutoffLocal (η : C(X, ℝ)) (hη : ∀ x, 0 ≤ η x) :
    Continuous (legalInputCutoffLocal (X := X) η) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro F
  simpa only [Function.comp_def, testIntegral_legalInputCutoffLocal η hη] using
    LocalFiniteMeasure.continuous_testIntegral (LocalFiniteMeasure.weightedContinuousTest F η)

/-- Exact Laplace identities after multiplying original compact tests by one
fixed cutoff give the entire localized law. -/
theorem map_legalInputCutoffLocal_eq_of_compact_laplace
    (P P' : Measure (LocalFiniteMeasure X)) [IsFiniteMeasure P] [IsFiniteMeasure P']
    (η : C(X, ℝ)) (hη : ∀ x, 0 ≤ η x)
    (h : ∀ F : LegalNonnegativeInputTest X,
      (∫ μ, legalInputMeasureLaplace
        ⟨LocalFiniteMeasure.weightedContinuousTest F.1 η, fun x ↦ mul_nonneg (F.2 x) (hη x)⟩ μ ∂P) =
      ∫ μ, legalInputMeasureLaplace
        ⟨LocalFiniteMeasure.weightedContinuousTest F.1 η, fun x ↦ mul_nonneg (F.2 x) (hη x)⟩ μ ∂P') :
    P.map (legalInputCutoffLocal η) = P'.map (legalInputCutoffLocal η) := by
  have hm := (continuous_legalInputCutoffLocal η hη).measurable
  apply measure_eq_of_legalInput_compact_laplace
  intro F
  rw [integral_map hm.aemeasurable (legalInputMeasureLaplace F).continuous.aestronglyMeasurable,
    integral_map hm.aemeasurable (legalInputMeasureLaplace F).continuous.aestronglyMeasurable]
  change (∫ μ, Real.exp (-LocalFiniteMeasure.testIntegral (legalInputCutoffLocal η μ) F.1) ∂P) =
    ∫ μ, Real.exp (-LocalFiniteMeasure.testIntegral (legalInputCutoffLocal η μ) F.1) ∂P'
  simp_rw [testIntegral_legalInputCutoffLocal η hη]
  exact h F

/-- A cutoff equal to one on the requested original window disappears after
restriction, pointwise for each original input measure. -/
theorem restrict_legalInputCutoffLocal_eq (η : C(X, ℝ))
    {U : Set X} (hU : MeasurableSet U) (hηU : EqOn η 1 U) (μ : LocalFiniteMeasure X) :
    (legalInputCutoffLocal η μ : Measure X).restrict U = (μ : Measure X).restrict U := by
  change ((μ : Measure X).withDensity (fun x ↦ ENNReal.ofReal (η x))).restrict U = _
  rw [restrict_withDensity hU]
  calc
    _ = ((μ : Measure X).restrict U).withDensity (fun _ ↦ 1) := by
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem hU] with x hx
      rw [hηU hx]
      norm_num
    _ = _ := by simp

/-- Weighted Laplace equality on a cutoff which is one on a measurable window
identifies the literal restricted input law, with all original correlations. -/
theorem map_legalInput_restrict_eq_of_cutoff_laplace
    (P P' : Measure (LocalFiniteMeasure X)) [IsFiniteMeasure P] [IsFiniteMeasure P']
    (η : C(X, ℝ)) (hη : ∀ x, 0 ≤ η x)
    {U : Set X} (hU : MeasurableSet U) (hηU : EqOn η 1 U)
    (h : ∀ F : LegalNonnegativeInputTest X,
      (∫ μ, legalInputMeasureLaplace
        ⟨LocalFiniteMeasure.weightedContinuousTest F.1 η, fun x ↦ mul_nonneg (F.2 x) (hη x)⟩ μ ∂P) =
      ∫ μ, legalInputMeasureLaplace
        ⟨LocalFiniteMeasure.weightedContinuousTest F.1 η, fun x ↦ mul_nonneg (F.2 x) (hη x)⟩ μ ∂P') :
    P.map (fun μ : LocalFiniteMeasure X ↦ (μ : Measure X).restrict U) =
      P'.map (fun μ : LocalFiniteMeasure X ↦ (μ : Measure X).restrict U) := by
  have hm : Measurable (fun μ : LocalFiniteMeasure X ↦ (μ : Measure X).restrict U) := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    simpa only [Measure.restrict_apply hS, Function.comp_def] using
      (Measure.measurable_coe (hS.inter hU)).comp measurable_localFiniteMeasure_coe
  have hcut := map_legalInputCutoffLocal_eq_of_compact_laplace P P' η hη h
  have hmap (R : Measure (LocalFiniteMeasure X)) :
      (R.map (legalInputCutoffLocal η)).map (fun μ : LocalFiniteMeasure X ↦ (μ : Measure X).restrict U) =
        R.map (fun μ : LocalFiniteMeasure X ↦ (μ : Measure X).restrict U) := by
    rw [Measure.map_map hm (continuous_legalInputCutoffLocal η hη).measurable]
    congr 1
    funext μ
    exact restrict_legalInputCutoffLocal_eq η hU hηU μ
  rw [← hmap P, ← hmap P', hcut]

end OTSelector.Reconstruction

end
end
