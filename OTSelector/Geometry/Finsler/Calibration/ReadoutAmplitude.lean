import LeanLevy.RandomMeasure.PoissonRandomMeasure
import LeanPool.FormalLearningTheory.Bridge
import LeanPool.FormalLearningTheory.PureMath.FiniteVCApprox
import LeanPool.QuasiBorelSpaces.MeasureTheory.Option
import LeanPool.ZhangYeungInequality.PFR.Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Radon
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Data.NNRat.Encodable
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Set.Finite.List
import Mathlib.Dynamics.Ergodic.Action.Basic
import Mathlib.Dynamics.Ergodic.Extreme
import Mathlib.InformationTheory.Hamming
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.SubFinite
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.LocallyFinsupp
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.UniformSpace.Ascoli
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerOriginalNodePositionReadoutBridge.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerOriginalNodePositionReadoutBridge`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.ReadoutAmplitude

* **Conditions:** Two parameter points lie in the same actual calibrated window ball.
* **Objects:** The original window readout distance bounded by its local Lipschitz constant times the maximum clock/label displacement.
* **Proof detail:** Apply the seed-provided local readout Lipschitz bound and the product max-norm distance identity.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): A generic metric readout estimate. No momentum-node normalization or model-versus-actual claim is part of the selected command.
-/

/-!
# Node-position to window-readout amplitude bridge

This file closes the remaining gaps (a) and (b) of
FinslerOriginalReadoutLipschitzFromAtlas.lean.

Gap (a): the node-position to readout estimate.  The normalized node position is
the matrix normalization of the literal original node position in the label
chart: normalizedMomentumNodePosition = T * v originalMomentumNodePosition.
Hence a bound on the normalized node-position amplitude (the pressure-lane
amplitude event) demultiplies with the inverse-frame constant to the literal
label-chart amplitude of the node position.  On the window side the readout is
Lipschitz on the coordinate ball (seed local data), so the readout amplitude is
bounded by the explicit constant times the maximum of the clock and label
coordinate amplitudes.

Gap (b): the single reference point and the half-radius shrink.  The retained
window points are compared with the single window centre; if the constant times
the coordinate amplitude is strictly below half the constructed chart radius,
then the two readout-deviation hypotheses of the atlas ball containment hold and
the retained pair lies in one manifold ball of explicit radius K * Drad.

Contents:

1. norm_le_of_normalized_amplitude: inverse-frame demultiplication.
2. originalMomentumNodePosition_norm_le_of_normalized: the concrete node-position
   amplitude bridge.
3. readout_amplitude_le_coordinate: window readout amplitude bounded by the
   coordinate amplitude through the seed local Lipschitz constant.
4. readout_deviation_le_of_coordinate_deviation: the same estimate relative to
   the single window centre.
5. calibratedWindow_ballContainment_of_coordinateAmplitude: the half-radius
   shrink of the atlas ball containment, with the reference point and the
   readout amplitude passed through explicitly.
6. calibratedWindow_ballContainment_of_labelBall: the same with the amplitude
   instantiated at the coordinate amplitude bound.
-/
open Set Function Filter MeasureTheory Matrix Module Manifold Metric
open OTSelector.Geometry ContinuousFinslerNorm
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical Topology BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## Gap (a): normalized node amplitude to literal label-chart amplitude -/





/-! ## Gap (a): window readout amplitude from coordinate amplitudes -/

/-- **Window readout amplitude from coordinate amplitude.**  On the retained
coordinate ball the window readout is Lipschitz with the seed local constant, so
the readout amplitude between two retained parameters is bounded by the constant
times the maximum of their clock and label coordinate differences. -/
theorem readout_amplitude_le_coordinate (P : CalibratedSeedWindow F u)
    {z zc : ℝ × P.seed.covector.ker}
    (hz : z ∈ ball P.center (P.seed.radius P.center))
    (hzc : zc ∈ ball P.center (P.seed.radius P.center)) :
    ‖P.readout z - P.readout zc‖ ≤
      (P.seed.constant P.center : ℝ) * max |z.1 - zc.1| ‖z.2 - zc.2‖ := by
  have h := P.lipschitzOn_readout.dist_le_mul z hz zc hzc
  rw [dist_eq_norm] at h
  have hprod : dist z zc = max |z.1 - zc.1| ‖z.2 - zc.2‖ := by
    rw [Prod.dist_eq, Real.dist_eq, dist_eq_norm]
  rwa [hprod] at h



/-! ## Gap (b): the half-radius shrink through the retained window data -/





end OTSelector.Reconstruction

end
end
