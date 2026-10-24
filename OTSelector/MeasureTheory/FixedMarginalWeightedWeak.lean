import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
## Lemma skeleton

* **Conditions:** Joint weak convergence with one fixed first marginal and an integrable measurable macro weight.
* **Objects:** Convergence of a bounded-continuous joint test times the macro weight.
* **Proof detail:** Approximate the weight in L1 by continuous functions; the fixed marginal bounds the approximation error uniformly.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4*, Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini).
  https://measure.axler.net/MIRA.pdf
* D. H. Fremlin, *Measure Theory, Volume 4*, Section 418J (second-countable target Lusin theorem), with compact inner regularity in Section 416.
  https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=110

**Relationship to the sources:** This is a useful fixed-marginal refinement of weak convergence, proved locally; arbitrary measurable weights require the fixed-marginal hypothesis.
-/

/-! A fixed first marginal lets arbitrary integrable macro weights pass through
joint weak convergence. In particular measurable core indicators need no
boundary condition, and the original joint measures are never normalized again. -/
open Set Function Filter MeasureTheory Topology TopologicalSpace
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OTSelector.Probability
set_option linter.unusedSectionVars false

variable {W S : Type*} [TopologicalSpace W] [PolishSpace W]
  [MeasurableSpace W] [BorelSpace W]
  [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]

/-- An integrable first-coordinate weight remains integrable against a bounded
continuous joint observation under every joint law with that first marginal. -/
theorem integrable_weighted_of_fixed_first_marginal
    (η : ProbabilityMeasure W) (R : ProbabilityMeasure (W × S))
    (hmarg : R.map measurable_fst.aemeasurable = η)
    (h : W → ℝ) (hh : Integrable h (η : Measure W)) (Φ : (W × S) →ᵇ ℝ) :
    Integrable (fun p ↦ h p.1 * Φ p) (R : Measure (W × S)) := by
  have hmap : (R : Measure (W × S)).map Prod.fst = (η : Measure W) :=
    congrArg (fun μ : ProbabilityMeasure W ↦ (μ : Measure W)) hmarg
  have hi : Integrable h ((R : Measure (W × S)).map Prod.fst) := by
    rw [hmap]
    exact hh
  exact (hi.comp_measurable measurable_fst).mul_bdd
    Φ.continuous.aestronglyMeasurable (ae_of_all _ Φ.norm_coe_le_norm)

/-- First-marginal L1 error controls the weighted integral uniformly over all
joint laws with that marginal, independently of their conditional laws. -/
theorem abs_integral_weighted_sub_le_of_fixed_first_marginal
    (η : ProbabilityMeasure W) (R : ProbabilityMeasure (W × S))
    (hmarg : R.map measurable_fst.aemeasurable = η)
    (h k : W → ℝ) (hh : Integrable h (η : Measure W))
    (hk : Integrable k (η : Measure W)) (Φ : (W × S) →ᵇ ℝ) :
    |(∫ p, h p.1 * Φ p ∂(R : Measure (W × S))) -
      ∫ p, k p.1 * Φ p ∂(R : Measure (W × S))| ≤
        ‖Φ‖ * ∫ w, ‖h w - k w‖ ∂(η : Measure W) := by
  have hmap : (R : Measure (W × S)).map Prod.fst = (η : Measure W) :=
    congrArg (fun μ : ProbabilityMeasure W ↦ (μ : Measure W)) hmarg
  have hdiff : Integrable (fun w ↦ h w - k w)
      ((R : Measure (W × S)).map Prod.fst) := by
    rw [hmap]
    exact hh.sub hk
  have hcomp := hdiff.comp_measurable measurable_fst
  have hprod := integrable_weighted_of_fixed_first_marginal η R hmarg
    (fun w ↦ h w - k w) (hh.sub hk) Φ
  rw [← integral_sub
    (integrable_weighted_of_fixed_first_marginal η R hmarg h hh Φ)
    (integrable_weighted_of_fixed_first_marginal η R hmarg k hk Φ)]
  simp_rw [← sub_mul]
  calc
    _ ≤ ∫ p, |(h p.1 - k p.1) * Φ p| ∂(R : Measure (W × S)) :=
      abs_integral_le_integral_abs
    _ ≤ ∫ p, ‖Φ‖ * ‖h p.1 - k p.1‖ ∂(R : Measure (W × S)) := by
      apply integral_mono_ae hprod.abs (hcomp.norm.const_mul ‖Φ‖)
      apply ae_of_all
      intro p
      change |(h p.1 - k p.1) * Φ p| ≤ ‖Φ‖ * ‖h p.1 - k p.1‖
      rw [abs_mul, ← Real.norm_eq_abs (Φ p), ← Real.norm_eq_abs (h p.1 - k p.1)]
      exact (mul_le_mul_of_nonneg_left (Φ.norm_coe_le_norm p)
        (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = ‖Φ‖ * ∫ w, ‖h w - k w‖ ∂(η : Measure W) := by
      rw [integral_const_mul]
      congr 1
      have heq := integral_map measurable_fst.aemeasurable hdiff.norm.aestronglyMeasurable
      rw [hmap] at heq
      exact heq.symm

/-- Joint weak convergence preserves its fixed first marginal and every
integrable measurable first-coordinate weight against bounded continuous tests. -/
theorem fixed_first_marginal_weighted_integral_tendsto_of_weak
    (η : ProbabilityMeasure W)
    (Rn : ℕ → ProbabilityMeasure (W × S)) (R : ProbabilityMeasure (W × S))
    (hweak : Tendsto Rn atTop (𝓝 R))
    (hmarg : ∀ n, (Rn n).map measurable_fst.aemeasurable = η)
    (h : W → ℝ) (hh : Integrable h (η : Measure W)) (Φ : (W × S) →ᵇ ℝ) :
    R.map measurable_fst.aemeasurable = η ∧
      Tendsto (fun n ↦ ∫ p, h p.1 * Φ p ∂(Rn n : Measure (W × S))) atTop
        (𝓝 (∫ p, h p.1 * Φ p ∂(R : Measure (W × S)))) := by
  have hmapped := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    Rn R hweak (continuous_fst : Continuous (Prod.fst : W × S → W))
  simp_rw [hmarg] at hmapped
  have hR : R.map measurable_fst.aemeasurable = η :=
    tendsto_nhds_unique hmapped tendsto_const_nhds
  refine ⟨hR, Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  let δ := ε / (3 * (‖Φ‖ + 1))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨k, hk, hkI⟩ := hh.exists_boundedContinuous_integral_sub_le hδ
  let Ψ : (W × S) →ᵇ ℝ := (k.compContinuous ⟨Prod.fst, continuous_fst⟩) * Φ
  have hΨ := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak Ψ
  have hbudget : ‖Φ‖ * δ ≤ ε / 3 := by
    have hle : ‖Φ‖ * δ ≤ (‖Φ‖ + 1) * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδ.le
    have heq : (‖Φ‖ + 1) * δ = ε / 3 := by
      dsimp only [δ]
      field_simp
    exact hle.trans_eq heq
  let I : ProbabilityMeasure (W × S) → ℝ := fun T ↦
    ∫ p, h p.1 * Φ p ∂(T : Measure (W × S))
  let J : ProbabilityMeasure (W × S) → ℝ := fun T ↦
    ∫ p, k p.1 * Φ p ∂(T : Measure (W × S))
  have hgap (T : ProbabilityMeasure (W × S))
      (hT : T.map measurable_fst.aemeasurable = η) : |I T - J T| ≤ ε / 3 :=
    (abs_integral_weighted_sub_le_of_fixed_first_marginal η T hT h k hh hkI Φ).trans
      ((mul_le_mul_of_nonneg_left hk (norm_nonneg Φ)).trans hbudget)
  have hnear := Metric.tendsto_nhds.mp hΨ (ε / 3) (by positivity)
  filter_upwards [hnear] with n hn
  change dist (I (Rn n)) (I R) < ε
  change dist (J (Rn n)) (J R) < ε / 3 at hn
  rw [Real.dist_eq] at hn ⊢
  calc
    |I (Rn n) - I R| =
        |(I (Rn n) - J (Rn n)) + (J (Rn n) - J R) + (J R - I R)| := by
      congr 1
      ring
    _ ≤ |I (Rn n) - J (Rn n)| + |J (Rn n) - J R| + |J R - I R| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ < ε := by
      rw [abs_sub_comm (J R) (I R)]
      linarith [hgap (Rn n) (hmarg n), hgap R hR]

end OTSelector.Probability
