import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasureKernel
import OTSelector.MeasureTheory.LocalFiniteMeasurePolish
import OTSelector.MeasureTheory.PairWeakCycleSupport
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.MeasurableMeasureEqualsLocal.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.MeasurableMeasureEqualsLocal`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.MeasurableLocalMeasureEquality

Conditions: A measurable arbitrary measure field, a measurable locally finite field and the explicit locally compact/countable Borel carrier assumptions.
Objects: The measurable event that the two original random measures are equal, without assuming local finiteness of the arbitrary field.
Proof detail: Restrict both fields to a compact exhaustion, replace only infinite compact restrictions by zero for measurable finite coding, and detect whole equality by countably many finite restrictions.

## Mathematical sources

- D. H. Fremlin, *Measure Theory, Volume 4*: Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces. https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106
- D. H. Fremlin, *Measure Theory, Volume 4*: Section 411N(a)–(d), p. 6: self-supporting sets and the unique full-measure closed support. https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=6
- Olav Kallenberg, *Random Measures, Theory and Applications (Springer 2017)*: Chapter 4 opening, pp. 109–110, and Section 4.1 “Weak and vague topologies”, pp. 111–117. https://link.springer.com/chapter/10.1007/978-3-319-41598-7_4

Source relation: A locally derived measurable-equality adapter using compact exhaustion and a Polish locally finite carrier. It does not assume a usable diagonal on the whole unrestricted measure space.
-/

/-! # Measurable equality of an arbitrary random measure to a local measure -/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {Ω X : Type*} [MeasurableSpace Ω]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [PseudoMetrizableSpace X]
  [SigmaCompactSpace X] [SecondCountableTopology X]
local instance measurableMeasureEqualsLocalPolish : PolishSpace (LocalFiniteMeasure X) :=
  LocalFiniteMeasure.instPolishSpace

/-- Equality to an actual locally finite random measure is a measurable
event even when the other random measure is not known locally finite.
Compact restrictions supply the finite versions and detect whole equality. -/
theorem measurableSet_measure_eq_localFiniteMeasure
    (ν : Ω → Measure X) (hν : Measurable ν)
    (μ : Ω → LocalFiniteMeasure X) (hμ : Measurable μ) :
    MeasurableSet {ω | ν ω = (μ ω : Measure X)} := by
  let K := CompactExhaustion.choice X
  let rv (n : ℕ) (ω : Ω) := (ν ω).restrict (K n)
  let rm (n : ℕ) (ω : Ω) := (μ ω : Measure X).restrict (K n)
  have hrv (n : ℕ) : Measurable (rv n) := by
    apply Measure.measurable_of_measurable_coe
    intro V hV
    simpa only [rv, Measure.restrict_apply hV, Function.comp_def] using
      (Measure.measurable_coe (hV.inter (K.isCompact n).measurableSet)).comp hν
  have hrm (n : ℕ) : Measurable (rm n) := by
    apply Measure.measurable_of_measurable_coe
    intro V hV
    simpa only [rm, Measure.restrict_apply hV, Function.comp_def] using
      (Measure.measurable_coe (hV.inter (K.isCompact n).measurableSet)).comp
        (OTSelector.Reconstruction.measurable_localFiniteMeasure_coe.comp hμ)
  let fv (n : ℕ) := finitePlanLocalVersion (rv n)
  let fm (n : ℕ) := finitePlanLocalVersion (rm n)
  have hfv (n : ℕ) : Measurable (fv n) := measurable_finitePlanLocalVersion _ (hrv n)
  have hfm (n : ℕ) : Measurable (fm n) := measurable_finitePlanLocalVersion _ (hrm n)
  have hmfin (n : ℕ) (ω : Ω) : rm n ω univ < ∞ := by
    simpa only [rm, Measure.restrict_apply_univ] using
      (K.isCompact n).measure_lt_top (μ := (μ ω : Measure X))
  have he : {ω | ν ω = (μ ω : Measure X)} =
      {ω | ∀ n : ℕ, rv n ω univ < ∞ ∧ fv n ω = fm n ω} := by
    ext ω
    constructor
    · intro h
      intro n
      have hr : rv n ω = rm n ω := by dsimp only [rv, rm]; rw [h]
      exact ⟨by rw [hr]; exact hmfin n ω, by apply Subtype.ext; simp only [fv, fm, coe_finitePlanLocalVersion, hr]⟩
    · intro h
      apply Measure.ext_of_iUnion_eq_univ K.iUnion_eq
      intro n
      have hc := congrArg (fun p : LocalFiniteMeasure X ↦ (p : Measure X)) (h n).2
      simpa only [fv, fm, coe_finitePlanLocalVersion, ite_eq_left (h n).1, ite_eq_left (hmfin n ω)] using hc
  rw [he]
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro n
  exact (measurableSet_lt ((Measure.measurable_coe MeasurableSet.univ).comp (hrv n))
    measurable_const).inter (measurableSet_eq_fun (hfv n) (hfm n))

end OTSelector.Probability

end
end
