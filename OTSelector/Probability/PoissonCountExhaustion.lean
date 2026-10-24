import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Moments.Basic
import OTSelector.Probability.FiniteIntensityCountFatou
import OTSelector.Probability.PoissonExponentialMoment

/-!
Conditions: Actual Poisson laws for ENNReal approximant counts, uniformly bounded rates, a.e. convergence to an a.e.-measurable finite-mean limit, and nonnegative tilt for the exhaustion upper bound.

Objects: Exact transformed count MGFs and finite limit count with its genuine exponential upper bound, including measure counts under monotone set exhaustion.

Proof detail: Transport the ordinary Poisson transform through natural/ENNReal casts. Finite mean first excludes infinite limiting count; Fatou passes the bounded-rate exponential estimate to its identified real limit.

References: Gunter Last; Mathew Penrose: Section 1.1, equations (1.8)–(1.10), p. 2; Rick Durrett: Section 1.6.2, Theorems 1.6.5–1.6.7, p. 30.
Relation: A finite-intensity exhaustion adapter. Its general transformed-law identity accepts any real tilt, while the rate-monotone upper-bound corollary explicitly requires nonnegative tilt.
-/


/-! Original Poisson count bounds on arbitrary finite-intensity sets. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Probability

/-- Exact exponential moment for a genuine Poisson count viewed in `ℝ≥0∞`. -/
theorem integrable_and_integral_exp_mul_of_hasLaw_poisson_ennreal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → ℝ≥0∞} {r : ℝ≥0}
    (hN : HasLaw N ((poissonMeasure r).map (Nat.cast : ℕ → ℝ≥0∞)) P) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * (N ω).toReal)) P ∧
      (∫ ω, Real.exp (t * (N ω).toReal) ∂P) =
        Real.exp ((r : ℝ) * (Real.exp t - 1)) := by
  let f : ℝ≥0∞ → ℝ := fun x ↦ Real.exp (t * x.toReal)
  have hf : Measurable f := (measurable_id.ennreal_toReal.const_mul t).exp
  have hi : Integrable f ((poissonMeasure r).map (Nat.cast : ℕ → ℝ≥0∞)) := by
    apply (integrable_map_measure hf.aestronglyMeasurable
      measurable_from_nat.aemeasurable).mpr
    simpa only [f, Function.comp_def, ENNReal.toReal_natCast] using
      integrable_exp_mul_poissonMeasure r t
  have hi' : Integrable f (P.map N) := hN.map_eq.symm ▸ hi
  refine ⟨(integrable_map_measure hf.aestronglyMeasurable hN.aemeasurable).mp hi', ?_⟩
  calc
    _ = ∫ x, f x ∂(poissonMeasure r).map (Nat.cast : ℕ → ℝ≥0∞) :=
      hN.integral_comp hf.aestronglyMeasurable
    _ = ∫ n : ℕ, Real.exp (t * (n : ℝ)) ∂poissonMeasure r := by
      rw [integral_map measurable_from_nat.aemeasurable hf.aestronglyMeasurable]
      simp only [f, ENNReal.toReal_natCast]
    _ = _ := integral_exp_mul_poissonMeasure r t

/-- Compact-exhaustion Poisson laws yield a full finite-intensity exponential
bound. No independence of the exhaustion counts is required. -/
theorem finite_count_and_exp_moment_of_poisson_exhaustion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ≥0∞} {Xn : ℕ → Ω → ℝ≥0∞} {r : ℝ≥0} {rn : ℕ → ℝ≥0}
    (hX : AEMeasurable X P) (hmean : (∫⁻ ω, X ω ∂P) ≠ ∞)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ Xn n ω) atTop (𝓝 (X ω)))
    (hlaw : ∀ n, HasLaw (Xn n) ((poissonMeasure (rn n)).map
      (Nat.cast : ℕ → ℝ≥0∞)) P)
    (hr : ∀ n, rn n ≤ r) {t : ℝ} (ht : 0 ≤ t) :
    (∀ᵐ ω ∂P, X ω < ∞) ∧
      Integrable (fun ω ↦ Real.exp (t * (X ω).toReal)) P ∧
      (∫ ω, Real.exp (t * (X ω).toReal) ∂P) ≤
        Real.exp ((r : ℝ) * (Real.exp t - 1)) := by
  have hm := fun n ↦ integrable_and_integral_exp_mul_of_hasLaw_poisson_ennreal (hlaw n) t
  apply finite_count_and_exp_moment_of_exhaustion hX hmean hlim
    (fun n ↦ (hm n).1) (Real.exp_pos _).le
  intro n
  rw [(hm n).2]
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hr n)
    (sub_nonneg.mpr (by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr ht))

/-- The limit in the preceding theorem is automatic for an increasing
exhaustion of the actual set in any original random measure. -/
theorem finite_count_and_exp_moment_of_poisson_measure_exhaustion
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] {P : Measure Ω}
    (N : Ω → Measure S) {B : Set S} {Bn : ℕ → Set S}
    (hBn : Monotone Bn) (hunion : (⋃ n, Bn n) = B)
    (hN : AEMeasurable (fun ω ↦ N ω B) P)
    (hmean : (∫⁻ ω, N ω B ∂P) ≠ ∞)
    {r : ℝ≥0} {rn : ℕ → ℝ≥0}
    (hlaw : ∀ n, HasLaw (fun ω ↦ N ω (Bn n))
      ((poissonMeasure (rn n)).map (Nat.cast : ℕ → ℝ≥0∞)) P)
    (hr : ∀ n, rn n ≤ r) {t : ℝ} (ht : 0 ≤ t) :
    (∀ᵐ ω ∂P, N ω B < ∞) ∧
      Integrable (fun ω ↦ Real.exp (t * (N ω B).toReal)) P ∧
      (∫ ω, Real.exp (t * (N ω B).toReal) ∂P) ≤
        Real.exp ((r : ℝ) * (Real.exp t - 1)) := by
  apply finite_count_and_exp_moment_of_poisson_exhaustion hN hmean ?_ hlaw hr ht
  apply Eventually.of_forall
  intro ω
  simpa only [hunion, Function.comp_def] using
    (tendsto_measure_iUnion_atTop (μ := N ω) hBn)

end OTSelector.Probability
