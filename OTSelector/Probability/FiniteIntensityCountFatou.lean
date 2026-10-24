import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Finite Intensity Count Fatou

Conditions: An a.e. nonnegative limit of integrable approximants with uniformly bounded integrals; the ENNReal exhaustion variant supplies finite limiting expectation and convergent approximants, with any real exponential tilt.

Objects: Integrability and expectation upper bounds of the limit, a.e. finiteness of the ENNReal observable and a passed exponential-moment estimate.

Proof detail: Apply Fatou to nonnegative approximants. Finite lower expectation excludes an infinite limit before continuity of toReal identifies its real exponential limit.

Relation to primary sources: A local exhaustion/Fatou consequence with arbitrary real exponential parameter; finiteness is proved before totalized toReal is used and no uniform-integrability premise is needed.

References:
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 1.6.2, Theorems 1.6.5–1.6.7, p. 30. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=38
-/
/-! Exponential count estimates under finite-intensity exhaustion, by Fatou. -/
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Probability

/-- A uniform nonnegative integral bound survives an almost sure limit.
This uses Fatou, with no uniform integrability assumption. -/
theorem integrable_and_integral_le_of_nonneg_ae_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {C : ℝ}
    (hf : ∀ n, Integrable (f n) P) (hf₀ : ∀ n, 0 ≤ᵐ[P] f n)
    (hg : AEStronglyMeasurable g P) (hg₀ : 0 ≤ᵐ[P] g) (hC : 0 ≤ C)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ f n ω) atTop (𝓝 (g ω)))
    (hbound : ∀ n, (∫ ω, f n ω ∂P) ≤ C) :
    Integrable g P ∧ (∫ ω, g ω ∂P) ≤ C := by
  have hfatou : (∫⁻ ω, ENNReal.ofReal (g ω) ∂P) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ ω, liminf (fun n ↦ ENNReal.ofReal (f n ω)) atTop ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with ω hω
        exact (ENNReal.tendsto_ofReal hω).liminf_eq.symm
      _ ≤ liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (f n ω) ∂P) atTop :=
        lintegral_liminf_le' (fun n ↦ (hf n).aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal C := by
        apply liminf_le_of_frequently_le'
        apply Frequently.of_forall
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hf n) (hf₀ n)]
        exact ENNReal.ofReal_le_ofReal (hbound n)
  have hgi : Integrable g P :=
    (lintegral_ofReal_ne_top_iff_integrable hg hg₀).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfatou)
  refine ⟨hgi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hgi hg₀] at hfatou
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hfatou

/-- Finite mean intensity and compact-count exponential bounds give the
exponential bound for the full count. Infinity is removed before taking `toReal`. -/
theorem finite_count_and_exp_moment_of_exhaustion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ≥0∞} {Xn : ℕ → Ω → ℝ≥0∞} {C t : ℝ}
    (hX : AEMeasurable X P) (hmean : (∫⁻ ω, X ω ∂P) ≠ ∞)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ Xn n ω) atTop (𝓝 (X ω)))
    (hint : ∀ n, Integrable (fun ω ↦ Real.exp (t * (Xn n ω).toReal)) P)
    (hC : 0 ≤ C)
    (hbound : ∀ n, (∫ ω, Real.exp (t * (Xn n ω).toReal) ∂P) ≤ C) :
    (∀ᵐ ω ∂P, X ω < ∞) ∧
      Integrable (fun ω ↦ Real.exp (t * (X ω).toReal)) P ∧
      (∫ ω, Real.exp (t * (X ω).toReal) ∂P) ≤ C := by
  have hfinite := ae_lt_top' hX hmean
  refine ⟨hfinite, integrable_and_integral_le_of_nonneg_ae_limit hint
    (fun _ ↦ .of_forall (fun _ ↦ (Real.exp_pos _).le))
    (hX.ennreal_toReal.const_mul t).exp.aestronglyMeasurable
    (.of_forall (fun _ ↦ (Real.exp_pos _).le)) hC ?_ hbound⟩
  filter_upwards [hfinite, hlim] with ω hω hlimω
  exact Real.continuous_exp.continuousAt.tendsto.comp
    (((ENNReal.tendsto_toReal hω.ne).comp hlimω).const_mul t)

end OTSelector.Probability
