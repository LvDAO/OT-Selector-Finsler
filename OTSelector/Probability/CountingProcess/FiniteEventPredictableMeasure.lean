import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Encodable
import Mathlib.Data.NNReal.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.OrderClosed
import OTSelector.Probability.CountingProcess.Core
import OTSelector.Probability.CountingProcess.PredictableMeasureExtension

/-!
# Probability.CountingProcess.FiniteEventPredictableMeasure

**Conditions:** A finite base measure, finitely many stopping-time event labels and a deterministic finite horizon; equality on predictable generators and total mass is an explicit hypothesis.

**Objects:** Expected finite-event jump measure and the predictable-trim intensity measure.

**Proof detail:** Sum actual event-time pushforwards restricted to attained labels, trim time×sample measure to the predictable sigma algebra and weight it by the nonnegative-part rate; finite-measure generator uniqueness identifies the measures.

**Sources:** [Richard D. Gill, Censoring and Stochastic Integrals, Mathematical Centre Tracts 124 (1980)](https://ir.cwi.nl/pub/11499/11499D.pdf#page=13), Section 2.1, pp. 8–9 (PDF pages 13–14), stochastic basis, stopping-time sigma-field, predictable processes and counting paths; [Richard D. Gill, Censoring and Stochastic Integrals, Mathematical Centre Tracts 124 (1980)](https://ir.cwi.nl/pub/11499/11499D.pdf#page=16), Section 2.2, pp. 10–11, especially equation (2.2.1), p. 11 (PDF page 16); Section 2.3, equation (2.3.1), p. 12; [Günter Last; Mathew Penrose, Lectures on the Poisson Process (author version, 21 August 2017)](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=254), Appendix A.1, Theorem A.5, p. 242; [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf), Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.

Source relation (composition): The cited primary sections give the mathematical principles used here. The exact source statement, endpoint convention, measure generality and finite encoding are local corollaries or Lean adapters rather than a claim that the book states the Lean theorem verbatim.
-/


/-!
# Predictable measures of finitely many event times

For a finite family of stopping times, the expected jump measure is a
finite sum of pushforwards of the sample law.  The candidate compensator
measure is the predictable trim of time x sample measure, restricted to a
finite horizon and weighted by the nonnegative rate.

The definitions here make the later monotone-class argument an equality
of honest measures on the predictable sigma algebra.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace OTSelector.CountingProcess

set_option linter.style.haveILetI false

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The time x sample measure, restricted to the predictable sigma
algebra. -/
noncomputable def predictableTimeSampleMeasure
    (mu : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega)) :
    @Measure (NNReal × Omega) F.predictable :=
  (timeMeasure.prod mu).trim (predictable_le_prod F)

set_option linter.unusedVariables false in
/-- Expected event measure up to a deterministic horizon.  Top-valued
fallback labels are excluded by the restriction `xi_i <= T`. -/
noncomputable def finiteEventJumpMeasure {m : Nat}
    (mu : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (xi : Fin m → Omega → WithTop NNReal)
    (hxi : ∀ i, IsStoppingTime F (xi i)) (T : NNReal) :
    @Measure (NNReal × Omega) F.predictable :=
  ∑ i : Fin m,
    @Measure.map Omega (NNReal × Omega)
      (inferInstance : MeasurableSpace Omega) F.predictable
      (fun omega => (WithTop.untopD 0 (xi i omega), omega))
      (mu.restrict {omega | xi i omega ≤ (T : WithTop NNReal)})

noncomputable instance finiteEventJumpMeasure_isFinite {m : Nat}
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (xi : Fin m → Omega → WithTop NNReal)
    (hxi : ∀ i, IsStoppingTime F (xi i)) (T : NNReal) :
    IsFiniteMeasure (finiteEventJumpMeasure mu F xi hxi T) := by
  let nu : Fin m → @Measure (NNReal × Omega) F.predictable := fun i =>
    @Measure.map Omega (NNReal × Omega)
      (inferInstance : MeasurableSpace Omega) F.predictable
      (fun omega => (WithTop.untopD 0 (xi i omega), omega))
      (mu.restrict {omega | xi i omega ≤ (T : WithTop NNReal)})
  letI (i : Fin m) : IsFiniteMeasure (nu i) := by
    letI : IsFiniteMeasure
        (mu.restrict {omega | xi i omega ≤ (T : WithTop NNReal)}) :=
      isFiniteMeasure_restrict.mpr (measure_lt_top mu _).ne
    dsimp [nu]
    exact Measure.isFiniteMeasure_map
      (β := NNReal × Omega) (mβ := F.predictable)
      (mu.restrict {omega | xi i omega ≤ (T : WithTop NNReal)})
      (fun omega => (WithTop.untopD 0 (xi i omega), omega))
  change IsFiniteMeasure (∑ i : Fin m, nu i)
  infer_instance

/-- The finite-horizon predictable measure with density `Lambda`.  The
caller proves predictability and nonnegativity of `Lambda`; `ofReal`
makes this definition an ordinary measure before those facts are used. -/
noncomputable def finiteHorizonIntensityMeasure
    (mu : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (Lambda : NNReal → Omega → Real) (T : NNReal) :
    @Measure (NNReal × Omega) F.predictable :=
  ((predictableTimeSampleMeasure mu F).restrict
      (Ioc (0 : NNReal) T ×ˢ (univ : Set Omega))).withDensity
    (fun z => ENNReal.ofReal (Lambda z.1 z.2))

/-- Equality on the defining predictable rectangles extends to the two
finite-horizon measures.  Finiteness is required only for the jump
measure; equality of total masses then supplies finiteness of the
candidate compensator measure inside the standard extension theorem. -/
theorem finiteEventJumpMeasure_eq_intensityMeasure_of_generator {m : Nat}
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (xi : Fin m → Omega → WithTop NNReal)
    (hxi : ∀ i, IsStoppingTime F (xi i))
    (Lambda : NNReal → Omega → Real) (T : NNReal)
    (hrect : ∀ s, s ∈ predictableGenerator F →
      finiteEventJumpMeasure mu F xi hxi T s =
        finiteHorizonIntensityMeasure mu F Lambda T s)
    (huniv : finiteEventJumpMeasure mu F xi hxi T univ =
      finiteHorizonIntensityMeasure mu F Lambda T univ) :
    finiteEventJumpMeasure mu F xi hxi T =
      finiteHorizonIntensityMeasure mu F Lambda T := by
  exact measure_eq_on_predictable_of_eq_generator F hrect huniv

end OTSelector.CountingProcess
