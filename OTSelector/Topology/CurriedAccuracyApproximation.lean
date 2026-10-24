import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.Filter.Curry

/-!
# Topology.CurriedAccuracyApproximation

Conditions: An array has the stated rowwise limits and outer zero limit, or accuracy-dependent curried approximants with rowwise vanishing sample error.

Objects: Curried convergence, preserving the order of outer and inner eventual quantifiers, including nonnegative integral readouts.

Proof detail: Split each error into outer, inner and accuracy parts. Choose the outer threshold first; choose each inner threshold after fixing its row. Use eventual Bochner/lintegral equality when integrability holds.

## Mathematical sources

- [Terence Tao, An Epsilon of Room, I](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=86): Section 1.6.2, Definition 1.6.15 and Exercise 1.6.8, pp. 77–78.
- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean): Section 6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17 (zero test).
- [Rick Durrett, Probability](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=38): Section 1.6.2, Theorems 1.6.5–1.6.7 (Fatou, monotone convergence, dominated convergence), p. 30.

Source relation: Locally proved ordered-limit/encoding corollaries. Curried convergence is not a claim about a product-filter diagonal or about uniform row thresholds.
-/

/-!
# Readouts retain the sample-before-tilt order

Separate inner readout limits and the outer zero limit give convergence on the
curried filter. Inner sample thresholds may depend on the fixed outer index.
-/
open Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- The curried filter preserves the two successive limits without a diagonal. -/
theorem tendsto_curry_zero_of_inner_outer_readout_limits
    (A : ℕ → ℕ → ℝ) (B : ℕ → ℝ) (ψ : ℕ → ℕ)
    (hinner : ∀ ℓ, Tendsto (A ℓ) atTop (𝓝 (B ℓ)))
    (houter : Tendsto (fun ℓ ↦ B (ψ ℓ)) atTop (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ ↦ A (ψ p.1) p.2)
      ((atTop : Filter ℕ).curry atTop) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  apply eventually_curry_iff.mpr
  filter_upwards [(Metric.tendsto_nhds.mp houter) (ε / 2) (by positivity)] with ℓ hℓ
  filter_upwards [(Metric.tendsto_nhds.mp (hinner (ψ ℓ))) (ε / 2) (by positivity)] with n hn
  exact (dist_triangle (A (ψ ℓ) n) (B (ψ ℓ)) 0).trans_lt (by linarith)

/-- Actual nonnegative readout expectations inherit curried convergence from
inner integrability and the two original expectation limits. -/
theorem tendsto_lintegral_ofReal_curry_zero_of_iterated_readout_limits
    {S : Type*} [MeasurableSpace S]
    (Pn : ℕ → ℕ → Measure S) (Q : ℕ → Measure S)
    (φ : ℕ → ℕ → ℕ) (ψ : ℕ → ℕ)
    (H : S → ℝ) (hH : ∀ s, 0 ≤ H s)
    (hinner : ∀ ℓ,
      (∀ᶠ n in atTop, Integrable H (Pn ℓ (φ ℓ n))) ∧
      Tendsto (fun n ↦ ∫ s, H s ∂Pn ℓ (φ ℓ n)) atTop
        (𝓝 (∫ s, H s ∂Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ ∫ s, H s ∂Q (ψ ℓ)) atTop (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ ↦ ∫⁻ s, ENNReal.ofReal (H s)
      ∂Pn (ψ p.1) (φ (ψ p.1) p.2))
      ((atTop : Filter ℕ).curry atTop) (𝓝 0) := by
  have hreal := tendsto_curry_zero_of_inner_outer_readout_limits
    (fun ℓ n ↦ ∫ s, H s ∂Pn ℓ (φ ℓ n))
    (fun ℓ ↦ ∫ s, H s ∂Q ℓ) ψ (fun ℓ ↦ (hinner ℓ).2) houter
  have hlim : Tendsto (fun p : ℕ × ℕ ↦ ENNReal.ofReal
      (∫ s, H s ∂Pn (ψ p.1) (φ (ψ p.1) p.2)))
      ((atTop : Filter ℕ).curry atTop) (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  have heq : (fun p : ℕ × ℕ ↦ ENNReal.ofReal
      (∫ s, H s ∂Pn (ψ p.1) (φ (ψ p.1) p.2))) =ᶠ[
        (atTop : Filter ℕ).curry atTop]
      (fun p : ℕ × ℕ ↦ ∫⁻ s, ENNReal.ofReal (H s)
        ∂Pn (ψ p.1) (φ (ψ p.1) p.2)) := by
    apply eventually_curry_iff.mpr
    apply Eventually.of_forall
    intro ℓ
    filter_upwards [(hinner (ψ ℓ)).1] with n hn
    exact ofReal_integral_eq_lintegral_ofReal hn (Eventually.of_forall hH)
  exact hlim.congr' heq

/-- Every accuracy uses one fixed approximating readout. Sample thresholds
may depend on the fixed tilt index, preserving the original iterated order. -/
theorem tendsto_curry_zero_of_vanishing_accuracy_approximants
    (A : ℕ → ℕ → ℝ≥0∞)
    (happrox : ∀ accuracy : ℝ, 0 < accuracy →
      ∃ B : ℕ → ℕ → ℝ≥0∞,
        Tendsto (fun p : ℕ × ℕ ↦ B p.1 p.2)
          ((atTop : Filter ℕ).curry atTop) (𝓝 0) ∧
      ∃ sample : ℕ → ℕ → ℝ≥0∞,
        (∀ ℓ, Tendsto (sample ℓ) atTop (𝓝 0)) ∧
        ∀ ℓ, ∀ᶠ n in atTop, A ℓ n ≤ B ℓ n + ENNReal.ofReal accuracy + sample ℓ n) :
    Tendsto (fun p : ℕ × ℕ ↦ A p.1 p.2)
      ((atTop : Filter ℕ).curry atTop) (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hε
  simp only [zero_add] at hδε
  let α : ℝ := (δ : ℝ) / 3
  have hα : 0 < α := div_pos (by exact_mod_cast hδ) (by norm_num)
  have hαe : 0 < ENNReal.ofReal α := ENNReal.ofReal_pos.mpr hα
  obtain ⟨B, hB, sample, hsample, hbound⟩ := happrox α hα
  have hs : Tendsto (fun p : ℕ × ℕ ↦ sample p.1 p.2)
      ((atTop : Filter ℕ).curry atTop) (𝓝 0) :=
    Filter.Tendsto.curry (Eventually.of_forall hsample)
  have hbounds : ∀ᶠ p : ℕ × ℕ in (atTop : Filter ℕ).curry atTop,
      A p.1 p.2 ≤ B p.1 p.2 + ENNReal.ofReal α + sample p.1 p.2 :=
    eventually_curry_iff.mpr (Eventually.of_forall hbound)
  filter_upwards [hbounds, ENNReal.tendsto_nhds_zero.mp hB _ hαe,
    ENNReal.tendsto_nhds_zero.mp hs _ hαe] with p hp hBp hsp
  have heq : ENNReal.ofReal α + ENNReal.ofReal α + ENNReal.ofReal α = (δ : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_add hα.le hα.le,
      ← ENNReal.ofReal_add (add_nonneg hα.le hα.le) hα.le]
    have hr : α + α + α = (δ : ℝ) := by dsimp only [α]; ring
    rw [hr, ENNReal.ofReal_coe_nnreal]
  calc
    A p.1 p.2 ≤ B p.1 p.2 + ENNReal.ofReal α + sample p.1 p.2 := hp
    _ ≤ ENNReal.ofReal α + ENNReal.ofReal α + ENNReal.ofReal α :=
      add_le_add (add_le_add hBp le_rfl) hsp
    _ = (δ : ℝ≥0∞) := heq
    _ ≤ ε := hδε.le

end OTSelector.Reconstruction
