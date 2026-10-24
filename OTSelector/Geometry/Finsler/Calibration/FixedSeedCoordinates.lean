import LeanPool.QuasiBorelSpaces.MeasureTheory.Option
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.SubFinite
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.LocallyFinsupp
import Mathlib.Topology.MetricSpace.HausdorffDimension
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Geometry.Finsler.Calibration.RootLabelValue
import OTSelector.Geometry.Finsler.Calibration.SeedRootPartition
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.HopfRinow
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneFixedSeed.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneFixedSeed`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.FixedSeedCoordinates

* **Conditions:** A fixed original calibrated window atlas, population label map and its existing selected root pieces.
* **Objects:** The fixed physical source piece and its original basis-coordinate seed observation, with measurable source membership.
* **Proof detail:** Take the label preimage of the existing Borel piece and express its zero-extended inverse label in the finite seed basis.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (adapter): Only the two definitions and source-set measurability are selected; auxiliary accuracies, near-edge events and pressure statements are excluded.
-/

/-!
# One fixed original seed scene across auxiliary accuracies

The physical source piece and scaled seed basis observation are defined directly
from the original atlas. They do not depend on an auxiliary finite core. Every
auxiliary near edge stays in one original seed piece, and its same-seed position
agrees exactly with the fixed observation. Crossings of a fixed source piece are
therefore part of the full original non-near complement at every core accuracy.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] {μ ν : Measure M}
  [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞} [∀ j, SigmaFinite (κ j)]

/-- A fixed original seed piece in physical space. It is independent of all
auxiliary finite cores, scalar windows and accuracy parameters. -/
def physicalSceneOriginalSeedSource (j : ℕ) : Set M :=
  a ⁻¹' populationSeedRootPiece P a κ lambda j

/-- The actual fixed original seed basis observation, before spatial scaling. -/
def physicalSceneOriginalSeedBasisPosition (j : ℕ) (x : M) :
    Fin (finrank ℝ (P j).seed.covector.ker) → ℝ :=
  (Module.finBasis ℝ (P j).seed.covector.ker).equivFun
    (populationSeedRootLabelValue (P j).seed a (a x))





variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
include hF hcomplete hu ha hinj

/-- The same original physical seed piece is a measurable source restriction. -/
theorem measurableSet_physicalSceneOriginalSeedSource (j : ℕ) :
    MeasurableSet (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := lambda) j) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  exact (measurableSet_populationSeedRootPiece P a κ lambda hF hcomplete hu ha hinj j).preimage ha



end OTSelector.Reconstruction

end
end
