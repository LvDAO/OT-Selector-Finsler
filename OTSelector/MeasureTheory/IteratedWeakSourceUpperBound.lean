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
import OTSelector.MeasureTheory.LocalFiniteMeasure
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneRootedSourceKernelUpperWeak.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneRootedSourceKernelUpperWeak`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.IteratedWeakSourceUpperBound

## Lemma skeleton

* **Conditions:** Weakly converging probability scenes, a lower-semicontinuous nonnegative readout, a continuous nonnegative upper reference and sample/tilt errors tending to zero in their separate limits.
* **Objects:** Almost-everywhere upper bounds surviving one or two limits, including full nonproper source-window masses.
* **Proof detail:** The positive-excess event over reference+epsilon is open. Portmanteau sends its eventually zero probabilities to zero; take countably many epsilons, then apply the same step at the outer limit. Open rectangle evaluation supplies the source-window readout.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61): Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=59): Section 2B, Theorems 2.59–2.60, p. 44 (increasing and decreasing sets).

Source relation (composition): Pathwise upper-limit transfer; no target cutoff, proper projection or projected local finiteness is needed.
-/

/-!
# Continuous reference upper bounds through the same weak scene limits

Open positive-excess events transfer pathwise upper bounds with vanishing
errors. The sample limit is taken at each fixed tilt before the outer tilt
limit. The source-window readout uses ALL targets, through an open nonproper
projection preimage, and requires no target cutoff or source-marginal finiteness.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
  [OpensMeasurableSpace S] [HasOuterApproxClosed S]

/-- An LSC readout stays below a continuous reference in the original weak
limit when its finite-stage pathwise excess is bounded by a vanishing error.
Only open positive-excess events are passed through Portmanteau. -/
theorem ae_lsc_le_continuous_of_weak_vanishing_error
    (R : ProbabilityMeasure S) (Pn : ℕ → ProbabilityMeasure S)
    (hweak : Tendsto Pn atTop (𝓝 R))
    (W : S → ℝ≥0∞) (hW : LowerSemicontinuous W)
    (f : S → ℝ≥0∞) (hf : Continuous f)
    (error : ℕ → ℝ≥0∞) (herror : Tendsto error atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, ∀ᵐ s ∂(Pn n : Measure S), W s ≤ f s + error n) :
    ∀ᵐ s ∂(R : Measure S), W s ≤ f s := by
  have hδ (δ : ℝ≥0∞) (hδ : 0 < δ) : ∀ᵐ s ∂(R : Measure S), W s ≤ f s + δ := by
    let U : Set S := {s | f s + δ < W s}
    have hclosed : IsClosed {s : S | W s ≤ f s + δ} :=
      hW.isClosed_epigraph.preimage (continuous_id.prodMk (hf.add continuous_const))
    have hU : IsOpen U := by
      simpa only [Set.compl_ofPred, not_le] using hclosed.isOpen_compl
    have hsmall : ∀ᶠ n in atTop, error n < δ :=
      herror.eventually (Iio_mem_nhds hδ)
    have hn : ∀ᶠ n in atTop, (Pn n : Measure S) U = 0 := by
      filter_upwards [hbound, hsmall] with n hn herr
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hn] with s hs hbad
      exact (not_lt_of_ge (hs.trans (add_le_add le_rfl herr.le))) hbad
    have hlim : atTop.liminf (fun n ↦ (Pn n : Measure S) U) = 0 :=
      (liminf_congr hn).trans (liminf_const 0)
    have hzero : (R : Measure S) U = 0 := le_antisymm
      ((ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hU).trans_eq hlim) bot_le
    exact (measure_eq_zero_iff_ae_notMem.mp hzero).mono fun _ hs ↦ not_lt.mp hs
  have hall : ∀ᵐ s ∂(R : Measure S), ∀ k : ℕ,
      W s ≤ f s + (((k + 1 : ℕ) : ℝ≥0∞))⁻¹ :=
    ae_all_iff.mpr fun k ↦ hδ _ (by simp)
  have htol : Tendsto (fun k : ℕ ↦ (((k + 1 : ℕ) : ℝ≥0∞))⁻¹) atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  filter_upwards [hall] with s hs
  have hlim : Tendsto (fun k : ℕ ↦ f s + (((k + 1 : ℕ) : ℝ≥0∞))⁻¹)
      atTop (𝓝 (f s)) := by
    simpa only [add_zero] using tendsto_const_nhds.add htol
  exact ge_of_tendsto hlim (Eventually.of_forall hs)

/-- A sample-size pathwise error vanishes separately at every fixed tilt,
then the SAME exact reference bound survives the prescribed outer weak limit. -/
theorem ae_lsc_le_continuous_of_iterated_weak_sample_error
    (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ ℓ, Tendsto (φ ℓ) atTop atTop)
    (ψ : ℕ → ℕ)
    (hinner : ∀ ℓ, Tendsto (fun n ↦ Pn ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
    (W : S → ℝ≥0∞) (hW : LowerSemicontinuous W)
    (f : S → ℝ≥0∞) (hf : Continuous f)
    (sample : ℕ → ℝ≥0∞) (hsample : Tendsto sample atTop (𝓝 0))
    (hbound : ∀ ℓ, ∀ᶠ n in atTop,
      ∀ᵐ s ∂(Pn ℓ n : Measure S), W s ≤ f s + sample n) :
    ∀ᵐ s ∂(R : Measure S), W s ≤ f s := by
  have hQ (ℓ : ℕ) : ∀ᵐ s ∂(Q ℓ : Measure S), W s ≤ f s :=
    ae_lsc_le_continuous_of_weak_vanishing_error (Q ℓ) (fun n ↦ Pn ℓ (φ ℓ n))
      (hinner ℓ) W hW f hf (fun n ↦ sample (φ ℓ n)) (hsample.comp (hφ ℓ))
      ((hφ ℓ).eventually (hbound ℓ))
  apply ae_lsc_le_continuous_of_weak_vanishing_error R (fun ℓ ↦ Q (ψ ℓ)) houter
    W hW f hf (fun _ ↦ 0) tendsto_const_nhds
  exact Eventually.of_forall fun ℓ ↦ by simpa only [add_zero] using hQ (ψ ℓ)

/-- Distinct sample and tilt pathwise errors vanish in their original order;
no diagonal scene or extra integrability hypothesis is introduced. -/
theorem ae_lsc_le_continuous_of_iterated_weak_tilt_sample_errors
    (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ ℓ, Tendsto (φ ℓ) atTop atTop)
    (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop)
    (hinner : ∀ ℓ, Tendsto (fun n ↦ Pn ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
    (W : S → ℝ≥0∞) (hW : LowerSemicontinuous W)
    (f : S → ℝ≥0∞) (hf : Continuous f)
    (tilt sample : ℕ → ℝ≥0∞)
    (htilt : Tendsto tilt atTop (𝓝 0)) (hsample : Tendsto sample atTop (𝓝 0))
    (hbound : ∀ ℓ, ∀ᶠ n in atTop,
      ∀ᵐ s ∂(Pn ℓ n : Measure S), W s ≤ f s + tilt ℓ + sample n) :
    ∀ᵐ s ∂(R : Measure S), W s ≤ f s := by
  have hQ (ℓ : ℕ) : ∀ᵐ s ∂(Q ℓ : Measure S), W s ≤ f s + tilt ℓ :=
    ae_lsc_le_continuous_of_weak_vanishing_error (Q ℓ) (fun n ↦ Pn ℓ (φ ℓ n))
      (hinner ℓ) W hW (fun s ↦ f s + tilt ℓ) (hf.add continuous_const)
      (fun n ↦ sample (φ ℓ n)) (hsample.comp (hφ ℓ)) ((hφ ℓ).eventually (hbound ℓ))
  exact ae_lsc_le_continuous_of_weak_vanishing_error R (fun ℓ ↦ Q (ψ ℓ)) houter
    W hW f hf (fun ℓ ↦ tilt (ψ ℓ)) (htilt.comp hψ) (Eventually.of_forall fun ℓ ↦ hQ (ψ ℓ))

section SourceWindow
variable {X Y : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [PseudoMetrizableSpace X]
  [SigmaCompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [T2Space Y] [LocallyCompactSpace Y] [PseudoMetrizableSpace Y]
  [SigmaCompactSpace Y] [SecondCountableTopology Y]

/-- The ALL-target source-window mass of a continuous actual vague-plan
readout is LSC, even though the source projection is nonproper. -/
theorem lowerSemicontinuous_nonproper_source_window_mass
    (plan : S → LocalFiniteMeasure (X × Y)) (hplan : Continuous plan)
    (O : Set X) (hO : IsOpen O) :
    LowerSemicontinuous (fun s ↦ (plan s : Measure (X × Y)) (O ×ˢ univ)) :=
  (LocalFiniteMeasure.lowerSemicontinuous_measure_open (hO.prod isOpen_univ)).comp hplan

/-- Original finite-stage pathwise source-window bounds against a continuous
reference survive one actual weak limit with a vanishing sample error. -/
theorem ae_nonproper_source_window_mass_le_continuous_of_weak_vanishing_error
    (R : ProbabilityMeasure S) (Pn : ℕ → ProbabilityMeasure S)
    (hweak : Tendsto Pn atTop (𝓝 R))
    (plan : S → LocalFiniteMeasure (X × Y)) (hplan : Continuous plan)
    (O : Set X) (hO : IsOpen O)
    (f : S → ℝ≥0∞) (hf : Continuous f)
    (error : ℕ → ℝ≥0∞) (herror : Tendsto error atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, ∀ᵐ s ∂(Pn n : Measure S),
      (plan s : Measure (X × Y)) (O ×ˢ univ) ≤ f s + error n) :
    ∀ᵐ s ∂(R : Measure S), (plan s : Measure (X × Y)) (O ×ˢ univ) ≤ f s :=
  ae_lsc_le_continuous_of_weak_vanishing_error R Pn hweak _
    (lowerSemicontinuous_nonproper_source_window_mass plan hplan O hO)
    f hf error herror hbound

/-- The SAME actual plan source-window estimate survives the fixed-tilt sample
limit and the subsequent outer limit. No target-window restriction is required. -/
theorem ae_nonproper_source_window_mass_le_continuous_of_iterated_weak_sample_error
    (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ ℓ, Tendsto (φ ℓ) atTop atTop)
    (ψ : ℕ → ℕ)
    (hinner : ∀ ℓ, Tendsto (fun n ↦ Pn ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
    (plan : S → LocalFiniteMeasure (X × Y)) (hplan : Continuous plan)
    (O : Set X) (hO : IsOpen O)
    (f : S → ℝ≥0∞) (hf : Continuous f)
    (sample : ℕ → ℝ≥0∞) (hsample : Tendsto sample atTop (𝓝 0))
    (hbound : ∀ ℓ, ∀ᶠ n in atTop, ∀ᵐ s ∂(Pn ℓ n : Measure S),
      (plan s : Measure (X × Y)) (O ×ˢ univ) ≤ f s + sample n) :
    ∀ᵐ s ∂(R : Measure S), (plan s : Measure (X × Y)) (O ×ˢ univ) ≤ f s :=
  ae_lsc_le_continuous_of_iterated_weak_sample_error Pn Q R φ hφ ψ hinner houter _
    (lowerSemicontinuous_nonproper_source_window_mass plan hplan O hO)
    f hf sample hsample hbound

/-- Separate sample and tilt errors also pass for the original ALL-target
nonproper source-window readout, with its unchanged continuous reference. -/
theorem ae_nonproper_source_window_mass_le_continuous_of_iterated_weak_tilt_sample_errors
    (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ ℓ, Tendsto (φ ℓ) atTop atTop)
    (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop)
    (hinner : ∀ ℓ, Tendsto (fun n ↦ Pn ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
    (plan : S → LocalFiniteMeasure (X × Y)) (hplan : Continuous plan)
    (O : Set X) (hO : IsOpen O)
    (f : S → ℝ≥0∞) (hf : Continuous f)
    (tilt sample : ℕ → ℝ≥0∞)
    (htilt : Tendsto tilt atTop (𝓝 0)) (hsample : Tendsto sample atTop (𝓝 0))
    (hbound : ∀ ℓ, ∀ᶠ n in atTop, ∀ᵐ s ∂(Pn ℓ n : Measure S),
      (plan s : Measure (X × Y)) (O ×ˢ univ) ≤ f s + tilt ℓ + sample n) :
    ∀ᵐ s ∂(R : Measure S), (plan s : Measure (X × Y)) (O ×ˢ univ) ≤ f s :=
  ae_lsc_le_continuous_of_iterated_weak_tilt_sample_errors Pn Q R φ hφ ψ hψ hinner houter _
    (lowerSemicontinuous_nonproper_source_window_mass plan hplan O hO)
    f hf tilt sample htilt hsample hbound

end SourceWindow
end OTSelector.Reconstruction

end
end
