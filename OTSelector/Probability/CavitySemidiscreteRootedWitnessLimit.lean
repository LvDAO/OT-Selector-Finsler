import OTSelector.Probability.CavitySemidiscreteRootedWitness
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Vanishing expected rooted witnesses

The phase-averaged bound is integrated on the same environment and independent
root probability spaces. It allows sample-size-dependent probability spaces and
passes directly to the weak-law cycle-support consumer.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section
namespace OTSelector.Probability

/-- The exact original environment-times-root expectation inherits the actual fiber
bound. Neither the root domain nor the environment is replaced by a new sample. -/
theorem lintegral_prod_witness_le_of_fiber_bound
    {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Z) [SFinite Q]
    (W : Ω × Z → ℝ≥0∞) (hW : Measurable W)
    (ε B : ℝ≥0∞) (hε0 : ε ≠ 0) (hεtop : ε ≠ ⊤)
    (hfiber : ∀ᵐ ω ∂P, (∫⁻ z, ε * W (ω, z) ∂Q) ≤ B) :
    (∫⁻ z, W z ∂P.prod Q) ≤ B / ε := by
  apply (ENNReal.le_div_iff_mul_le (Or.inl hε0) (Or.inl hεtop)).mpr
  rw [mul_comm, ← lintegral_const_mul' _ _ hεtop,
    lintegral_prod (fun z ↦ ε * W z) (measurable_const.mul hW).aemeasurable]
  calc
    _ ≤ ∫⁻ _, B ∂P := lintegral_mono_ae hfiber
    _ = B := by simp

/-- The quantitative grid bound forces expected cycle witnesses to vanish even when
sample size changes both probability spaces. -/
theorem tendsto_lintegral_rooted_witness_zero_of_fiber_bound
    {Ω Z : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Z n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : ∀ n, Measure (Z n)) [∀ n, SFinite (Q n)]
    (W : ∀ n, Ω n × Z n → ℝ≥0∞) (hW : ∀ n, Measurable (W n))
    (ε C : ℝ≥0∞) (hε0 : ε ≠ 0) (hεtop : ε ≠ ⊤) (hC : C ≠ ⊤)
    (t : ℕ → ℝ≥0∞) (ht : Tendsto t atTop (𝓝 0))
    (hfiber : ∀ n, ∀ᵐ ω ∂P n, (∫⁻ z, ε * W n (ω, z) ∂Q n) ≤ C * t n) :
    Tendsto (fun n ↦ ∫⁻ z, W n z ∂(P n).prod (Q n)) atTop (𝓝 0) := by
  have hbound (n : ℕ) := lintegral_prod_witness_le_of_fiber_bound
    (P n) (Q n) (W n) (hW n) ε (C * t n) hε0 hεtop (hfiber n)
  have hlim : Tendsto (fun n ↦ C * t n / ε) atTop (𝓝 (0 : ℝ≥0∞)) := by
    have hm := ENNReal.Tendsto.const_mul ht (Or.inr hC)
    simpa only [mul_zero, ENNReal.zero_div] using
      ENNReal.Tendsto.div_const hm (Or.inr hε0)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ zero_le) hbound

end OTSelector.Probability
