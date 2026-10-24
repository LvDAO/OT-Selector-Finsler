import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import OTSelector.Probability.EmpiricalMeasure
import OTSelector.Transport.Coupling.CostEquivalence
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Limit.EmpiricalPressureSelector.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Limit.EmpiricalPressureSelector`; the selected original proof blocks follow. -/
section

/-!
Conditions: Two actual finite point lists and the indicated cost/coupling conventions.

Objects: The set of probability couplings optimal for their empirical laws.

Proof detail: Unpack the empirical laws and define the whole optimal coupling face using the actual cost optimum.

Sources: Gabriel Peyré, Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20 (https://optimaltransport.github.io/pdf/ComputationalOT.pdf).
Relation: Only the empiricalOptimalFace definition is extracted. Pressure and asymptotic selector assertions from the same file are excluded.
-/

/-!
# Actual empirical distance selectors from probe pressures

The face consists of every optimal coupling of the original empirical probability marginals,
including samples with repeated points. The pressure is the attained finite assignment value
for scaled distance slack plus an actual paired bounded continuous probe, divided by sample size.
Finite optimality supplies nonemptiness and every affine comparison used in reconstruction.
The compact space may be the union of supports with the restricted ambient distance; neither
compactness of the ambient manifold nor intrinsic path distance on that union is required.

Differentiability and the stated stochastic or filter pressure limits remain analytic premises.
This interface does not prove the geometric pressure theorem for a Finsler model.
-/

open Filter MeasureTheory Set
open scoped Topology BoundedContinuousFunction ENNReal

namespace OTSelector.Pressure

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-- All probability couplings minimizing distance for the original empirical marginals. -/
def empiricalOptimalFace {n : ℕ} (X Y : Fin n → M) : Set (ProbabilityMeasure (M × M)) :=
  {γ | IsOptimalCoupling edist (empiricalMeasure X) (empiricalMeasure Y)
    (γ : Measure (M × M))}








end OTSelector.Pressure

end
