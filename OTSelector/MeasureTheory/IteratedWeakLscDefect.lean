import LeanPool.QuasiBorelSpaces.MeasureTheory.Option
import LeanPool.Vlasov.OT.Coupling
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
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
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
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

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneLimitIteratedLscDefect.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneLimitIteratedLscDefect`; the selected original proof blocks follow. -/
section

/-!
Conditions: Two levels of actual weak probability convergence, a nonnegative lower-semicontinuous defect and the stated eventual integral loss/tilt/sample bound.

Objects: A limiting defect-tail bound loss divided by any positive finite level.

Proof detail: Pass to the lower-semicontinuous integral inequality at each weak limit, let both error scales vanish and apply Markov to the limit.

Sources: D. H. Fremlin, Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation (https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61); Rick Durrett, Section 1.6.1, Theorem 1.6.4 and equation (1.6.1), pp. 29–30 (https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37).
Relation: Iterated Portmanteau/Markov consequence; no exchange of the two limits or uniform-integrability premise is inserted.
-/

/-!
# Separate sample and tilt errors in the same limiting scene

A fixed original core's population loss remains explicit. The original energy
error vanishes first with the sample size at each fixed tilt. The tilt error
vanishes only in the subsequent outer limit. No diagonal law is introduced.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
  [OpensMeasurableSpace S] [HasOuterApproxClosed S]

/-- An original lower semicontinuous witness keeps only its fixed-core loss
in every positive-level event after the sample and tilt weak limits. -/
theorem measure_lsc_gt_le_of_iterated_weak_sample_tilt_defect_bounds
    (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ k, Tendsto (φ k) atTop atTop)
    (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop)
    (hinner : ∀ k, Tendsto (fun N ↦ Pn k (φ k N)) atTop (𝓝 (Q k)))
    (houter : Tendsto (fun k ↦ Q (ψ k)) atTop (𝓝 R))
    (W : S → ℝ≥0∞) (hW : LowerSemicontinuous W)
    (loss : ℝ≥0∞) (tilt : ℕ → ℝ≥0∞) (sample : ℕ → ℝ≥0∞)
    (htilt : Tendsto tilt atTop (𝓝 0)) (hsample : Tendsto sample atTop (𝓝 0))
    (hbound : ∀ᶠ k in atTop, ∀ᶠ N in atTop,
      (∫⁻ s, W s ∂(Pn k N : Measure S)) ≤ tilt k + loss + sample N)
    (r : ℝ≥0∞) (hr : 0 < r) (hrt : r ≠ ⊤) :
    (R : Measure S) {s | r < W s} ≤ loss / r := by
  have hQ : ∀ᶠ k in atTop, (Q k : Measure S) {s | r < W s} ≤ (tilt k + loss) / r := by
    filter_upwards [hbound] with k hk
    have hb : ∀ᶠ N in atTop,
        (Pn k (φ k N) : Measure S) {s | r < W s} ≤
          (tilt k + loss + sample (φ k N)) / r := by
      filter_upwards [(hφ k).eventually hk] with N hN
      exact ((measure_mono (show {s | r < W s} ⊆ {s | r ≤ W s} from
        fun s hs ↦ le_of_lt (show r < W s from hs))).trans
        (meas_ge_le_lintegral_div hW.measurable.aemeasurable (ne_of_gt hr) hrt)).trans
        (ENNReal.div_le_div_right hN r)
    have hlim : Tendsto (fun N ↦ (tilt k + loss + sample (φ k N)) / r) atTop
        (𝓝 ((tilt k + loss) / r)) := by
      simpa only [add_zero, Function.comp_def] using ENNReal.Tendsto.div_const
        (tendsto_const_nhds.add (hsample.comp (hφ k))) (Or.inr (ne_of_gt hr))
    exact (ProbabilityMeasure.le_liminf_measure_open_of_tendsto (hinner k)
      (hW.isOpen_preimage r)).trans ((liminf_le_liminf hb).trans_eq hlim.liminf_eq)
  have hlim : Tendsto (fun k ↦ (tilt (ψ k) + loss) / r) atTop (𝓝 (loss / r)) := by
    simpa only [zero_add, Function.comp_def] using ENNReal.Tendsto.div_const
      ((htilt.comp hψ).add tendsto_const_nhds) (Or.inr (ne_of_gt hr))
  have hQsub : ∀ᶠ k in atTop,
      (Q (ψ k) : Measure S) {s | r < W s} ≤ (tilt (ψ k) + loss) / r := hψ.eventually hQ
  exact (ProbabilityMeasure.le_liminf_measure_open_of_tendsto houter
    (hW.isOpen_preimage r)).trans ((liminf_le_liminf hQsub).trans_eq hlim.liminf_eq)





end OTSelector.Reconstruction

end
end
