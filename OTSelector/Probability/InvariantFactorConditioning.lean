import Mathlib.Dynamics.Ergodic.Extreme

/-!
# Invariant Factor Conditioning

Conditions: A probability-preserving extension T, an ergodic factor S, a measurable equivariant input with the stated factor law, and a positive-mass a.e. T-invariant event.

Objects: The same original input law after normalized conditioning on that invariant event.

Proof detail: Push the restricted extension measure to the factor, use invariant RN-density rigidity to identify it as the event mass times the original law, then normalize.

Relation to primary sources: A locally derived invariant-event factor-conditioning theorem. The factor need only have the exact single-transformation ergodicity supplied in its type.

References:
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 6.1, Example 6.1.4 and invariant-event/ergodicity definitions, pp. 331–332; Exercises 6.1.1–6.1.2, p. 334. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=340
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Appendix A.4, Theorem A.4.8 and Exercises A.4.6–A.4.9, p. 470. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=478
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 4.1, definition and uniqueness, pp. 205–207; Example 4.1.5, p. 208; Theorem 4.1.9, pp. 210–211. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=213
-/
/-! Invariant-event conditioning retains an ergodic original input factor. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
noncomputable section
namespace OTSelector.Probability

/-- Conditioning a stationary scene on an invariant event leaves its
ergodic original input law unchanged. This uses absolute continuity of the
conditioned input and needs no ergodic decomposition of the scene law. -/
theorem map_cond_eq_of_ergodic_factor_of_ae_invariant
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (P : Measure X) [IsProbabilityMeasure P]
    (T : Ω → Ω) (S : X → X) (input : Ω → X)
    (hT : MeasurePreserving T Q Q) (hinput : Measurable input)
    (hmap : Q.map input = P) (hcomm : Semiconj input T S) (hP : Ergodic S P)
    (A : Set Ω) (hA : MeasurableSet A) (hinv : T ⁻¹' A =ᵐ[Q] A) (hpos : Q A ≠ 0) :
    (Q[|A]).map input = P := by
  let _ : IsProbabilityMeasure Q[|A] := cond_isProbabilityMeasure hpos
  let R : Measure X := (Q[|A]).map input
  let _ : IsProbabilityMeasure R := Measure.isProbabilityMeasure_map hinput.aemeasurable
  have hrestricted : MeasurePreserving T (Q.restrict A) (Q.restrict A) := by
    simpa only [Measure.restrict_congr_set hinv] using hT.restrict_preimage hA
  have hconditioned : MeasurePreserving T Q[|A] Q[|A] :=
    hrestricted.smul_measure (Q A)⁻¹
  have hfactor : MeasurePreserving input Q[|A] R := ⟨hinput, rfl⟩
  have hR : MeasurePreserving S R R :=
    hfactor.of_semiconj hconditioned hcomm hP.toMeasurePreserving.measurable
  have habs : R ≪ P := by
    rw [← hmap]
    exact (cond_absolutelyContinuous (μ := Q) (s := A)).map hinput
  exact hP.eq_of_absolutelyContinuous hR habs

end OTSelector.Probability
