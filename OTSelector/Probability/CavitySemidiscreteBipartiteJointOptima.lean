import OTSelector.Probability.CavitySemidiscreteJointOptima
import OTSelector.Probability.CavitySemidiscreteBipartiteOptima

/-!
# Measurable optimal plans for the actual iid target cloud

The target cloud has its original product law. A common deterministic sequence of
tilt parameters yields jointly measurable zero and opposite-tilt allocations on the
same target cloud, Dirichlet weights, and original source space.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S T : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [MeasurableSpace T] [StandardBorelSpace T]

/-- Actual iid targets and masses support all three jointly measurable optimal plans,
with the common positive tilt sequence and the quantitative base-cost comparison. -/
theorem exists_jointlyMeasurable_bipartite_opposite_semidiscrete_optima_sequence
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (c g : S → T → ℝ) (hc : Measurable (Function.uncurry c))
    (hci : Integrable (Function.uncurry c) (μ.prod ν))
    (hg : Measurable (Function.uncurry g))
    (hatom : ∀ y z, y ≠ z → NullSingletonClass (μ.map (fun x ↦ c x y - c x z)))
    (G : ℝ≥0) (hbound : ∀ x y, |g x y| ≤ G) :
    ∃ t : ℕ → ℝ, ∃ A₀ : (((Fin (m + 1) → T) × (Fin (m + 1) → ℝ)) × S) → Fin (m + 1) → ℝ,
    ∃ Aplus Amin : ℕ → (((Fin (m + 1) → T) × (Fin (m + 1) → ℝ)) × S) → Fin (m + 1) → ℝ,
      StrictAnti t ∧ (∀ n, 0 < t n) ∧ Tendsto t atTop (nhds 0) ∧
      (∀ j, Measurable (fun z ↦ A₀ z j)) ∧
      (∀ n j, Measurable (fun z ↦ Aplus n z j)) ∧
      (∀ n j, Measurable (fun z ↦ Amin n z j)) ∧
      ∀ᵐ z ∂(Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod (dirichletOne m),
        IsOptimalSemidiscreteAllocation μ z.2 (fun s j ↦ c s (z.1 j))
          (fun s ↦ A₀ (z, s)) ∧ ∀ n,
        IsOptimalSemidiscreteAllocation μ z.2
          (fun s j ↦ c s (z.1 j) + t n * g s (z.1 j)) (fun s ↦ Aplus n (z, s)) ∧
        IsOptimalSemidiscreteAllocation μ z.2
          (fun s j ↦ c s (z.1 j) + (-t n) * g s (z.1 j)) (fun s ↦ Amin n (z, s)) ∧
        0 ≤ semidiscreteAllocationCost μ (fun s j ↦ c s (z.1 j))
          (fun s j ↦ (Aplus n (z, s) j + Amin n (z, s) j) / 2) -
            semidiscreteAllocationCost μ (fun s j ↦ c s (z.1 j)) (fun s ↦ A₀ (z, s)) ∧
        semidiscreteAllocationCost μ (fun s j ↦ c s (z.1 j))
          (fun s j ↦ (Aplus n (z, s) j + Amin n (z, s) j) / 2) -
            semidiscreteAllocationCost μ (fun s j ↦ c s (z.1 j)) (fun s ↦ A₀ (z, s)) ≤ t n * G := by
  have hi : ∀ᵐ y ∂Measure.pi (fun _ : Fin (m + 1) ↦ ν),
      ∀ j, Integrable (fun x ↦ c x (y j)) μ := by
    apply ae_all_iff.mpr
    intro j
    exact (measurePreserving_eval (fun _ : Fin (m + 1) ↦ ν) j).quasiMeasurePreserving.ae
      hci.prod_left_ae
  have hat : ∀ᵐ y ∂Measure.pi (fun _ : Fin (m + 1) ↦ ν), ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ c s (y j) - c s (y l))) := by
    filter_upwards [ae_injective_pi_of_nullSingletonClass (ι := Fin (m + 1)) ν] with y hy
    exact fun j l hjl ↦ hatom (y j) (y l) (hy.ne hjl)
  exact exists_jointlyMeasurable_opposite_semidiscrete_optima_sequence
    μ (Measure.pi (fun _ : Fin (m + 1) ↦ ν))
    (fun y j s ↦ c s (y j)) (fun y j s ↦ g s (y j))
    (fun j ↦ hc.comp (measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst))) hi
    (fun j ↦ hg.comp (measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst))) hat
    G (fun y s j ↦ hbound s (y j))

end OTSelector.Probability
