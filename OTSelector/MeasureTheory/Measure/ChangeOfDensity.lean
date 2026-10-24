import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Unique
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.JacobiComplianceReflection.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.JacobiComplianceReflection`; the selected original proof blocks follow. -/
section

/-!
Conditions: A measurable equivalence, an arbitrary measure and an extended nonnegative density.

Objects: The exact pushforward-withDensity identity using the inverse equivalence.

Proof detail: Test equality on measurable sets and change variables through the equivalence, retaining the actual density.

Sources: D. H. Fremlin, Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf); D. H. Fremlin, Section 235G, integration along an inverse-measure-preserving map (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf).
Relation: Change-of-measure adapter, requiring no smoothness or Jacobi equation.
-/

/-!
# Changing the inward coordinate of an actual Jacobi conditional law

Reflection reverses the momentum and the signed compliance primitive while preserving
the Hamiltonian equations and the positive velocity coefficient. The same pushforward
of the original conditional measure retains its exact density formula. Translation
provides the analogous left-end coordinate change. All identities concern the actual
interval integral and original measure; no new population is introduced.
-/

open Set MeasureTheory Matrix
open scoped Topology Matrix.Norms.Operator ENNReal

set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Geometry

variable {n : Type*} [Fintype n] [DecidableEq n]







/-- An invertible measurable coordinate change transports its density exactly. -/
theorem map_withDensity_measurableEquiv
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (μ : Measure X) (d : X → ℝ≥0∞) :
    (μ.withDensity d).map e = (μ.map e).withDensity (fun y ↦ d (e.symm y)) := by
  ext S hS
  rw [Measure.map_apply e.measurable hS, withDensity_apply _ (e.measurable hS),
    withDensity_apply _ hS, e.measurableEmbedding.restrict_map,
    e.measurableEmbedding.lintegral_map]
  simp only [e.symm_apply_apply]











end OTSelector.Geometry

end
