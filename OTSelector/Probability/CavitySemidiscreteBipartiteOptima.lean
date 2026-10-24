import OTSelector.Probability.CavitySemidiscretePressureComparison
import OTSelector.Probability.CavitySemidiscreteOptimizer

/-!
# Common actual opposite-tilt optimizers for the original iid target law

Original pair-difference atomlessness and iid target distinctness produce deterministic
positive tilts tending to zero. On a single full-measure target-and-weight event, all
three diffuse optima exist and their averaged base-cost excess tends to zero at the
explicit rate `t * G`. No optimal-plan or pressure identity is an input.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S T : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [MeasurableSpace T] [MeasurableEq T]

/-- Actual random target clouds share a deterministic sequence of opposite tilts and the
corresponding diffuse optimizers, with an explicit near-optimal average on the same masses. -/
theorem exists_bipartite_opposite_semidiscrete_optima_sequence
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (c g : S → T → ℝ) (hc : Measurable (Function.uncurry c))
    (hci : Integrable (Function.uncurry c) (μ.prod ν))
    (hg : Measurable (Function.uncurry g))
    (hatom : ∀ y z, y ≠ z → NullSingletonClass (μ.map (fun x ↦ c x y - c x z)))
    (G : ℝ≥0) (hbound : ∀ x y, |g x y| ≤ G) :
    ∃ t : ℕ → ℝ, StrictAnti t ∧ (∀ n, 0 < t n) ∧ Tendsto t atTop (nhds 0) ∧
      ∀ᵐ y ∂Measure.pi (fun _ : Fin (m + 1) ↦ ν), ∀ᵐ p ∂dirichletOne m, ∀ n,
      ∃ a₀ aplus aminus : S → Fin (m + 1) → ℝ,
        IsOptimalSemidiscreteAllocation μ p (fun s j ↦ c s (y j)) a₀ ∧
        IsOptimalSemidiscreteAllocation μ p (fun s j ↦ c s (y j) + t n * g s (y j)) aplus ∧
        IsOptimalSemidiscreteAllocation μ p (fun s j ↦ c s (y j) + (-t n) * g s (y j)) aminus ∧
        0 ≤ semidiscreteAllocationCost μ (fun s j ↦ c s (y j))
          (fun s j ↦ (aplus s j + aminus s j) / 2) -
            semidiscreteAllocationCost μ (fun s j ↦ c s (y j)) a₀ ∧
        semidiscreteAllocationCost μ (fun s j ↦ c s (y j))
          (fun s j ↦ (aplus s j + aminus s j) / 2) -
            semidiscreteAllocationCost μ (fun s j ↦ c s (y j)) a₀ ≤ t n * G := by
  have hi : ∀ᵐ y ∂Measure.pi (fun _ : Fin (m + 1) ↦ ν),
      ∀ j, Integrable (fun x ↦ c x (y j)) μ := by
    apply ae_all_iff.mpr
    intro j
    have hj := (measurePreserving_eval (fun _ : Fin (m + 1) ↦ ν) j).quasiMeasurePreserving
    exact hj.tendsto_ae.eventually hci.prod_left_ae
  have hat : ∀ᵐ y ∂Measure.pi (fun _ : Fin (m + 1) ↦ ν), ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ c s (y j) - c s (y l))) := by
    filter_upwards [ae_injective_pi_of_nullSingletonClass (ι := Fin (m + 1)) ν] with y hy
    exact fun j l hjl ↦ hatom (y j) (y l) (hy.ne hjl)
  obtain ⟨t, ht, hpos, hlim, hopt⟩ := exists_opposite_semidiscrete_optima_sequence
    μ (Measure.pi (fun _ : Fin (m + 1) ↦ ν))
    (fun j y s ↦ c s (y j)) (fun j y s ↦ g s (y j))
    (fun j ↦ hc.comp (measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst))) hi
    (fun j ↦ hg.comp (measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst))) hat
    G (fun y s j ↦ hbound s (y j))
  refine ⟨t, ht, hpos, hlim, ?_⟩
  filter_upwards [hi, hopt] with y hiy hy
  have hgi j : Integrable (fun s ↦ g s (y j)) μ :=
    (integrable_const (G : ℝ)).mono'
      (hg.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Eventually.of_forall fun s ↦ by simpa only [Real.norm_eq_abs] using hbound s (y j))
  filter_upwards [hy] with p hp
  intro n
  obtain ⟨a₀, aplus, aminus, h₀, hplus, hminus⟩ := hp n
  have hcmp := semidiscrete_opposite_tilt_excess μ p
    (fun s j ↦ c s (y j)) (fun s j ↦ g s (y j)) a₀ aplus aminus
    h₀.1 hplus.1 hminus.1 hiy hgi G (Eventually.of_forall fun s j ↦ hbound s (y j))
    (t n) (hpos n).le h₀.2 hplus.2 hminus.2
  exact ⟨a₀, aplus, aminus, h₀, hplus, hminus, hcmp.1, hcmp.2.1.trans hcmp.2.2.1⟩

end OTSelector.Probability
