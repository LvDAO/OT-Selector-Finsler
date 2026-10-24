import LeanPool.QuasiBorelSpaces.MeasureTheory.Option
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
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.SubFinite
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.LocallyFinsupp
import Mathlib.Topology.MetricSpace.HausdorffDimension
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneLimitProjectedCoreAccuracy.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneLimitProjectedCoreAccuracy`; the selected original proof blocks follow. -/
section

/-!
Conditions: All projected auxiliary laws have the same actual output law, the retained defect is zero and lost-defect tails obey a vanishing accuracy bound.

Objects: The actual output defect vanishes almost everywhere.

Proof detail: Transfer each output level event through the common pushforward law, dominate by the lost tail and let accuracy vanish; a countable level union forces zero.

Sources: D. H. Fremlin, Section 235G, integration along an inverse-measure-preserving map (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf); Rick Durrett, Section 1.6.1, Theorem 1.6.4 and equation (1.6.1), pp. 29–30 (https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37); Sheldon Axler, Section 2B, Theorems 2.59–2.60, p. 44 (increasing and decreasing sets) (https://measure.axler.net/MIRA.pdf#page=59).
Relation: Pushforward and tail-squeeze consequence, independent of the geometric names of the original application.
-/

/-!
# Core accuracy varies only the auxiliary extension of one fixed original law

Different auxiliary cores may use different retained/lost extensions. Their
projection is the SAME fixed original law. Zero retained witnesses and vanishing
discarded-mass bounds therefore identify one common original readout without
selecting a third weak-limit law or a tilt/sample diagonal.
-/

open Set Function Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Auxiliary retained/lost laws may change with core accuracy while their
original projection stays fixed. Accuracy is taken only after those original
sample and tilt limits, and forces the fixed full readout to vanish. -/
theorem ae_eq_zero_of_projected_retained_zero_and_lost_accuracy
    (R : ProbabilityMeasure Y) (Raux : ℕ → ProbabilityMeasure X)
    (f : X → Y) (hf : Measurable f)
    (hmap : ∀ m, (Raux m).map hf.aemeasurable = R)
    (W : Y → ℝ≥0∞) (hW : Measurable W)
    (retained lost : ℕ → X → ℝ≥0∞)
    (hdom : ∀ m, ∀ᵐ s ∂(Raux m : Measure X), W (f s) ≤ retained m s + lost m s)
    (hretained : ∀ m, ∀ᵐ s ∂(Raux m : Measure X), retained m s = 0)
    (accuracy : ℕ → ℝ≥0∞) (haccuracy : Tendsto accuracy atTop (𝓝 0))
    (hlost : ∀ (m : ℕ) (level : ℝ≥0∞), 0 < level → level ≠ ⊤ →
      (Raux m : Measure X) {s | level < lost m s} ≤ accuracy m / level) :
    ∀ᵐ y ∂(R : Measure Y), W y = 0 := by
  have hopen (level : ℝ≥0∞) (hl0 : 0 < level) (hlt : level ≠ ⊤) :
      (R : Measure Y) {y | level < W y} = 0 := by
    have hb (m : ℕ) : (R : Measure Y) {y | level < W y} ≤ accuracy m / level := by
      have hm : (Raux m : Measure X).map f = (R : Measure Y) :=
        congrArg (fun p : ProbabilityMeasure Y ↦ (p : Measure Y)) (hmap m)
      rw [← hm, Measure.map_apply hf (measurableSet_lt measurable_const hW)]
      apply (measure_mono_ae ?_).trans (hlost m level hl0 hlt)
      filter_upwards [hdom m, hretained m] with s hs hr hlevel
      have hd : W (f s) ≤ lost m s := by simpa only [hr, zero_add] using hs
      exact hlevel.trans_le hd
    have hlim : Tendsto (fun m ↦ accuracy m / level) atTop (𝓝 0) := by
      simpa only [ENNReal.zero_div] using
        ENNReal.Tendsto.div_const haccuracy (Or.inr hl0.ne')
    apply le_antisymm _ bot_le
    calc
      _ = atTop.liminf (fun _ : ℕ ↦ (R : Measure Y) {y | level < W y}) := (liminf_const _).symm
      _ ≤ atTop.liminf (fun m ↦ accuracy m / level) := liminf_le_liminf (Eventually.of_forall hb)
      _ = 0 := hlim.liminf_eq
  have hz : ∀ᵐ y ∂(R : Measure Y), W y ≤ 0 := by
    apply (ae_le_const_iff_forall_gt_measure_zero W 0).mpr
    intro b hb
    obtain ⟨q, _, hq0, hqb⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hb
    have hs : {y | b ≤ W y} ⊆ {y | ((q : ℝ).toNNReal : ℝ≥0∞) < W y} :=
      fun _ hy ↦ hqb.trans_le hy
    exact measure_mono_null hs (hopen _ hq0 ENNReal.coe_ne_top)
  exact hz.mono fun _ hy ↦ le_antisymm hy bot_le

end OTSelector.Reconstruction

end
end
