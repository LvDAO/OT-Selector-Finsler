import LeanPool.Vlasov.OT.Coupling
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import OTSelector.Transport.Coupling.FiniteClockMixture

/-!
Conditions: A finite original law and measurable data/recovery maps with measurable equality in their target; separate pair lemmas use only dominated endpoint marginals or a stated s-finite same-label kernel.

Objects: A.e. conditional recovery of two equal original readouts, transfer to both endpoints under dominated marginals, and exact measurable same-label pair pushforward identities.

Proof detail: Disintegrate the original a.e. equality, transfer null endpoint sets through dominated marginals and compose the actual measurable endpoint maps under the same kernel product.

References: D. H. Fremlin: 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary; D. H. Fremlin: 452B(b), p. 18: integrating a measurable family on a product; 452E–452F, pp. 20–21: disintegration and its integral formula.
Relation: The selected statements are generic conditional-law/measure-transport lemmas. They do not replace the original joint law by a separately selected coupling or assert the original file’s geometric recovery conclusions.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawActualSeedRecovery.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawActualSeedRecovery`; the selected original proof blocks follow. -/
section

/-!
The given original physical inverse agrees almost everywhere with the actual
seed map on original conditional clocks. Deterministic retained pair kernels
inherit both endpoint identities through their dominated original marginals,
so original physical and seed-coordinate pair laws agree exactly.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Manifold
open scoped Topology ContDiff ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Original almost-everywhere recovery equalities pass to the literal original
conditional clock laws before any retained class or sample is chosen. -/
theorem ae_condDistrib_recovery_eq
    {X Z Y : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace Y]
    [MeasurableEq Y] (μ : Measure X) [IsFiniteMeasure μ]
    (a : X → Z) (u : X → ℝ) (ha : Measurable a) (hu : Measurable u)
    (b c : Z × ℝ → Y) (hb : Measurable b) (hc : Measurable c)
    (heq : ∀ᵐ x ∂μ, b (a x, u x) = c (a x, u x)) :
    ∀ᵐ z ∂μ.map a, ∀ᵐ t ∂condDistrib u a μ z, b (z, t) = c (z, t) := by
  let _instMapFinite : IsFiniteMeasure (μ.map a) := Measure.isFiniteMeasure_map μ a
  apply Measure.ae_ae_of_ae_compProd (p := fun p : Z × ℝ ↦ b p = c p)
  rw [compProd_map_condDistrib hu.aemeasurable]
  exact (ae_map_iff (ha.prodMk hu).aemeasurable (measurableSet_eq_fun hb hc)).mpr heq

/-- A retained clock-pair subpopulation inherits original endpoint identities
from its dominated original conditional marginals. -/
theorem ae_pair_endpoints_of_dominated_original_marginals
    {X : Type*} (γ : Measure (ℝ × ℝ)) (μ ν : Measure ℝ)
    (hleft : γ.map Prod.fst ≤ μ) (hright : γ.map Prod.snd ≤ ν)
    (b c : ℝ → X)
    (hμ : ∀ᵐ s ∂μ, b s = c s) (hν : ∀ᵐ t ∂ν, b t = c t) :
    ∀ᵐ p ∂γ, b p.1 = c p.1 ∧ b p.2 = c p.2 := by
  have hs := ae_of_ae_map measurable_fst.aemeasurable ((ae_mono hleft) hμ)
  have ht := ae_of_ae_map measurable_snd.aemeasurable ((ae_mono hright) hν)
  exact hs.and ht



/-- Read the two actual physical endpoints of one labeled clock pair. -/
def labelClockPairPhysicalMap {Z Y : Type*} (b : Z × ℝ → Y) (p : Z × (ℝ × ℝ)) : Y × Y :=
  (b (p.1, p.2.1), b (p.1, p.2.2))

theorem measurable_labelClockPairPhysicalMap
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    {b : Z × ℝ → Y} (hb : Measurable b) : Measurable (labelClockPairPhysicalMap b) :=
  (hb.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
    (hb.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))



/-- Physical endpoints read after the shared-label map are the same literal
pair endpoint map used in the original cell construction. -/
theorem sameLabelPair_physical_map_eq
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    (r : Measure Z) (K : Kernel Z (ℝ × ℝ)) [IsSFiniteKernel K]
    (b : Z × ℝ → Y) (hb : Measurable b) :
    ((r ⊗ₘ K).map sameLabelPopulationPair).map (Prod.map b b) =
      (r ⊗ₘ K).map (labelClockPairPhysicalMap b) := by
  rw [Measure.map_map (hb.prodMap hb) measurable_sameLabelPopulationPair]
  rfl


end OTSelector.Reconstruction

end
end
