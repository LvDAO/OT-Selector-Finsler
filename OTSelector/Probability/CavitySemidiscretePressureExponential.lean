import OTSelector.Probability.CavitySemidiscretePressureBipartite
import OTSelector.Probability.DirichletExponentialLaw

/-!
# Actual finite pressure with normalized independent exponential target weights

The reference-weight integral in the proved iid pressure formula is exactly the
integral obtained by dividing independent mean-one exponentials by their total.
This uses the proved law of those variables, including at exceptional tilt parameters.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]

/-- The actual semidiscrete value is integrable under normalized independent exponentials,
and its expectation is the original finite iid assignment pressure. -/
theorem integral_iid_pressure_eq_normalizedExp_semidiscreteValue
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c g : Fin (m + 1) → S → ℝ)
    (hc : ∀ j, Measurable (c j)) (hci : ∀ j, Integrable (c j) μ)
    (hg : ∀ j, Measurable (g j))
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c j s - c l s)))
    (G : ℝ≥0) (hbound : ∀ s j, |g j s| ≤ G) (t : ℝ) :
    Integrable (fun e : Fin (m + 1) → ℝ ↦
      semidiscreteValue μ (fun s j ↦ c j s + t * g j s) (normalizedMass m e))
      (Measure.pi (fun _ ↦ expMeasure 1)) ∧
    (∫ x : Fin (m + 1) → S,
      perturbedAssignmentValue (fun i j ↦ c j (x i)) (fun i j ↦ g j (x i)) t /
        (m + 1 : ℕ) ∂Measure.pi (fun _ ↦ μ)) =
      ∫ e : Fin (m + 1) → ℝ,
        semidiscreteValue μ (fun s j ↦ c j s + t * g j s) (normalizedMass m e)
          ∂Measure.pi (fun _ ↦ expMeasure 1) := by
  have h := integral_iid_perturbedAssignmentValue_eq_dirichlet_semidiscreteValue
    μ c g hc hci hg hatom G hbound t
  have hpres : MeasurePreserving (normalizedMass m)
      (Measure.pi (fun _ : Fin (m + 1) ↦ expMeasure 1)) (dirichletOne m) :=
    ⟨measurable_normalizedMass m, map_normalizedMass_pi_exp m⟩
  refine ⟨hpres.integrable_comp_of_integrable h.1, ?_⟩
  rw [h.2.2, ← hpres.map_eq, integral_map hpres.measurable.aemeasurable]
  rw [hpres.map_eq]
  exact h.1.aestronglyMeasurable

/-- The random-target pressure admits the actual independent exponential weight representation. -/
theorem integral_bipartite_pressure_eq_normalizedExp_semidiscreteValue
    {T : Type*} [MeasurableSpace T] [MeasurableEq T]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (c g : S → T → ℝ) (hc : Measurable (Function.uncurry c))
    (hci : Integrable (Function.uncurry c) (μ.prod ν))
    (hg : Measurable (Function.uncurry g))
    (hatom : ∀ y z, y ≠ z → NullSingletonClass (μ.map (fun x ↦ c x y - c x z)))
    (G : ℝ≥0) (hbound : ∀ x y, |g x y| ≤ G) (t : ℝ) :
    Integrable (fun y : Fin (m + 1) → T ↦ ∫ e : Fin (m + 1) → ℝ,
      semidiscreteValue μ (fun x j ↦ c x (y j) + t * g x (y j)) (normalizedMass m e)
        ∂Measure.pi (fun _ ↦ expMeasure 1)) (Measure.pi (fun _ ↦ ν)) ∧
    (∫ q : (Fin (m + 1) → T) × (Fin (m + 1) → S),
      perturbedAssignmentValue (fun i j ↦ c (q.2 i) (q.1 j))
        (fun i j ↦ g (q.2 i) (q.1 j)) t / (m + 1 : ℕ)
        ∂(Measure.pi (fun _ ↦ ν)).prod (Measure.pi (fun _ ↦ μ))) =
      ∫ y : Fin (m + 1) → T, ∫ e : Fin (m + 1) → ℝ,
        semidiscreteValue μ (fun x j ↦ c x (y j) + t * g x (y j)) (normalizedMass m e)
          ∂Measure.pi (fun _ ↦ expMeasure 1) ∂Measure.pi (fun _ ↦ ν) := by
  have h := integral_bipartite_pressure_eq_dirichlet_semidiscreteValue (m := m)
    μ ν c g hc hci hg hatom G hbound t
  have heq : (fun y : Fin (m + 1) → T ↦
      ∫ p, semidiscreteValue μ (fun x j ↦ c x (y j) + t * g x (y j)) p
        ∂dirichletOne m) =ᵐ[Measure.pi (fun _ ↦ ν)]
      fun y ↦ ∫ e : Fin (m + 1) → ℝ,
        semidiscreteValue μ (fun x j ↦ c x (y j) + t * g x (y j)) (normalizedMass m e)
          ∂Measure.pi (fun _ ↦ expMeasure 1) := by
    filter_upwards [ae_integral_iid_pressure_eq_dirichlet_semidiscreteValue (m := m)
      μ ν c g hc hci hg hatom G hbound] with y hy
    rw [← map_normalizedMass_pi_exp m, integral_map
      (measurable_normalizedMass m).aemeasurable]
    rw [map_normalizedMass_pi_exp m]
    exact (hy t).1.aestronglyMeasurable
  exact ⟨h.1.congr heq, h.2.trans (integral_congr_ae heq)⟩

end OTSelector.Probability
