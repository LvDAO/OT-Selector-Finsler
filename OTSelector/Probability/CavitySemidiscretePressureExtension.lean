import OTSelector.Probability.CavitySemidiscretePressureRegularity
import OTSelector.Probability.CavityTiltAtomlessness

/-!
# The actual iid pressure identity at every perturbation

Good tilts form a dense set by the proved countable-exception result. Pointwise
Lipschitz bounds give integrability and continuity of both actual pressure means;
their exact equality on good tilts therefore extends to every real parameter.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace OTSelector.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Dense integrability and one common almost-everywhere Lipschitz bound supply
integrability of the original family at every parameter. -/
theorem integrable_of_dense_integrable_of_ae_lipschitz
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℝ → Ω → ℝ) (G : ℝ≥0)
    (hlip : ∀ᵐ ω ∂P, LipschitzWith G (fun t ↦ F t ω))
    (D : Set ℝ) (hD : Dense D) (hint : ∀ t ∈ D, Integrable (F t) P)
    (t : ℝ) : Integrable (F t) P := by
  obtain ⟨u, hu, hut⟩ := mem_closure_iff_seq_limit.mp (hD t)
  have hm : AEStronglyMeasurable (F t) P :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n ↦ (hint (u n) (hu n)).aestronglyMeasurable)
      (hlip.mono fun ω hω ↦ hω.continuous.continuousAt.tendsto.comp hut)
  apply ((hint (u 0) (hu 0)).norm.add
    (integrable_const ((G : ℝ) * |t - u 0|))).mono' hm
  filter_upwards [hlip] with ω hω
  have hb : ‖F t ω - F (u 0) ω‖ ≤ (G : ℝ) * |t - u 0| := by
    simpa only [Real.dist_eq, Real.norm_eq_abs] using hω.dist_le_mul t (u 0)
  calc
    ‖F t ω‖ ≤ ‖F (u 0) ω‖ + ‖F t ω - F (u 0) ω‖ := by
      simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub (F (u 0) ω) (F t ω)
    _ ≤ _ := add_le_add le_rfl hb

/-- Averaging a common almost-everywhere Lipschitz bound preserves its constant. -/
theorem lipschitzWith_integral_of_ae_lipschitz
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℝ → Ω → ℝ) (G : ℝ≥0)
    (hlip : ∀ᵐ ω ∂P, LipschitzWith G (fun t ↦ F t ω))
    (hint : ∀ t, Integrable (F t) P) :
    LipschitzWith G (fun t ↦ ∫ ω, F t ω ∂P) := by
  apply LipschitzWith.of_dist_le_mul
  intro t u
  rw [Real.dist_eq, ← integral_sub (hint t) (hint u), ← Real.norm_eq_abs]
  have hb : ∀ᵐ ω ∂P, ‖F t ω - F u ω‖ ≤ (G : ℝ) * dist t u :=
    hlip.mono fun ω hω ↦ by simpa only [dist_eq_norm] using hω.dist_le_mul t u
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
    norm_integral_le_of_norm_le_const hb

variable {m : ℕ} {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]

/-- Every real bounded paired perturbation satisfies the original iid finite-pressure
identity, including parameters where score differences acquire atoms. -/
theorem integral_iid_perturbedAssignmentValue_eq_dirichlet_semidiscreteValue
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c g : Fin (m + 1) → S → ℝ)
    (hc : ∀ j, Measurable (c j)) (hci : ∀ j, Integrable (c j) μ)
    (hg : ∀ j, Measurable (g j))
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c j s - c l s)))
    (G : ℝ≥0) (hbound : ∀ s j, |g j s| ≤ G) (t : ℝ) :
    Integrable (semidiscreteValue μ (fun s j ↦ c j s + t * g j s)) (dirichletOne m) ∧
    Integrable (fun x : Fin (m + 1) → S ↦
      perturbedAssignmentValue (fun i j ↦ c j (x i)) (fun i j ↦ g j (x i)) t / (m + 1 : ℕ))
      (Measure.pi (fun _ : Fin (m + 1) ↦ μ)) ∧
    (∫ x : Fin (m + 1) → S,
      perturbedAssignmentValue (fun i j ↦ c j (x i)) (fun i j ↦ g j (x i)) t / (m + 1 : ℕ)
        ∂Measure.pi (fun _ : Fin (m + 1) ↦ μ)) =
      ∫ p, semidiscreteValue μ (fun s j ↦ c j s + t * g j s) p ∂dirichletOne m := by
  let P := Measure.pi (fun _ : Fin (m + 1) ↦ μ)
  let F : ℝ → (Fin (m + 1) → S) → ℝ := fun t x ↦
    perturbedAssignmentValue (fun i j ↦ c j (x i)) (fun i j ↦ g j (x i)) t / (m + 1 : ℕ)
  let H : ℝ → (Fin (m + 1) → ℝ) → ℝ := fun t p ↦
    semidiscreteValue μ (fun s j ↦ c j s + t * g j s) p
  let D : Set ℝ := {t | ∀ j l, j ≠ l → NullSingletonClass
    (μ.map (fun s ↦ (c j s + t * g j s) - (c l s + t * g l s)))}
  have hD : Dense D := dense_good_cavity_tilts μ c g hc hg hatom
  have hgi (j : Fin (m + 1)) : Integrable (g j) μ := by
    apply (integrable_const (G : ℝ)).mono' (hg j).aestronglyMeasurable
    exact Eventually.of_forall fun s ↦ by simpa only [Real.norm_eq_abs] using hbound s j
  have hFl : ∀ᵐ x ∂P, LipschitzWith G (fun u ↦ F u x) := by
    apply Eventually.of_forall
    intro x
    exact lipschitzWith_perturbedAssignmentValue_div (Nat.succ_pos m)
      (fun i j ↦ c j (x i)) (fun i j ↦ g j (x i)) G (fun i j ↦ hbound (x i) j)
  have hHl : ∀ᵐ p ∂dirichletOne m, LipschitzWith G (fun u ↦ H u p) :=
    (ae_mem_stdSimplex_dirichletOne m).mono fun p hp ↦
      lipschitzWith_semidiscreteValue_tilt μ (fun s j ↦ c j s) (fun s j ↦ g j s)
        hci hgi G (Eventually.of_forall hbound) p hp
  have hgood (u : ℝ) (hu : u ∈ D) :
      Integrable (H u) (dirichletOne m) ∧ Integrable (F u) P ∧
        (∫ x, F u x ∂P) = ∫ p, H u p ∂dirichletOne m := by
    have h := integral_iid_assignmentValue_eq_dirichlet_semidiscreteValue μ
      (fun j s ↦ c j s + u * g j s) (fun j ↦ (hc j).add ((hg j).const_mul u))
      (fun j ↦ (hci j).add ((hgi j).const_mul u)) hu
    have heq (x : Fin (m + 1) → S) :
        perturbedAssignmentValue (fun i j ↦ c j (x i) + u * g j (x i)) 0 0 /
          (m + 1 : ℕ) = F u x := by
      let C : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := fun i j ↦ c j (x i)
      let Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := fun i j ↦ g j (x i)
      change perturbedAssignmentValue (perturbedEdgeCost C Q u) 0 0 / (m + 1 : ℕ) =
        perturbedAssignmentValue C Q u / (m + 1 : ℕ)
      simp only [perturbedAssignmentValue, perturbedEdgeCost_zero]
    simpa only [heq] using h
  have hFi := integrable_of_dense_integrable_of_ae_lipschitz P F G hFl D hD
    (fun u hu ↦ (hgood u hu).2.1)
  have hHi := integrable_of_dense_integrable_of_ae_lipschitz (dirichletOne m) H G hHl D hD
    (fun u hu ↦ (hgood u hu).1)
  have hFcont := (lipschitzWith_integral_of_ae_lipschitz P F G hFl hFi).continuous
  have hHcont := (lipschitzWith_integral_of_ae_lipschitz (dirichletOne m) H G hHl hHi).continuous
  have heq := Continuous.ext_on hD hFcont hHcont (fun u hu ↦ (hgood u hu).2.2)
  exact ⟨hHi t, hFi t, congrFun heq t⟩

end OTSelector.Probability
