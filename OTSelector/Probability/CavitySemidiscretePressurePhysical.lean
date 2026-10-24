import OTSelector.Probability.CavitySemidiscretePrimal
import OTSelector.Probability.CavitySemidiscretePressureExponential

/-!
# The iid pressure identity for the full physical coupling primal

The allocation representation is eliminated from the public value formula: the diffuse
value is the infimum over all couplings to the actual weighted target atoms. Both the
Dirichlet and normalized exponential representations use the original sampled targets.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S T Ω : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [MeasurableSpace T] [MeasurableSingletonClass T] [MeasurableSpace Ω]

omit [StandardBorelSpace S] in
/-- The full physical value and allocation value agree almost everywhere in the weight law. -/
theorem ae_fullSemidiscreteValue_eq_semidiscreteValue
    (μ : Measure S) [IsProbabilityMeasure μ]
    (Y : Fin (m + 1) → T) (hY : Function.Injective Y)
    (c g : S → T → ℝ) (hc : Measurable (Function.uncurry c))
    (hci : ∀ j, Integrable (fun s ↦ c s (Y j)) μ)
    (hg : Measurable (Function.uncurry g))
    (G : ℝ≥0) (hbound : ∀ x y, |g x y| ≤ G) (t : ℝ) :
    fullSemidiscreteValue μ Y (fun x y ↦ c x y + t * g x y) =ᵐ[dirichletOne m]
      semidiscreteValue μ (fun x j ↦ c x (Y j) + t * g x (Y j)) := by
  have hgi j : Integrable (fun s ↦ g s (Y j)) μ :=
    (integrable_const (G : ℝ)).mono'
      (hg.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Eventually.of_forall fun s ↦ by simpa only [Real.norm_eq_abs] using hbound s (Y j))
  filter_upwards [ae_mem_stdSimplex_dirichletOne m] with p hp
  exact fullSemidiscreteValue_eq_semidiscreteValue μ Y hY (fun x y ↦ c x y + t * g x y)
    (hc.add (hg.const_mul t)) (fun j ↦ (hci j).add ((hgi j).const_mul t)) p hp.1

/-- Fixed actual targets: the original empirical minimum equals the full semidiscrete primal
in expectation, with no selected diffuse optimizer in the statement. -/
theorem integral_iid_pressure_eq_fullSemidiscreteValue
    (μ : Measure S) [IsProbabilityMeasure μ]
    (Y : Fin (m + 1) → T) (hY : Function.Injective Y)
    (c g : S → T → ℝ) (hc : Measurable (Function.uncurry c))
    (hci : ∀ j, Integrable (fun s ↦ c s (Y j)) μ)
    (hg : Measurable (Function.uncurry g))
    (hatom : ∀ y z, y ≠ z → NullSingletonClass (μ.map (fun x ↦ c x y - c x z)))
    (G : ℝ≥0) (hbound : ∀ x y, |g x y| ≤ G) (t : ℝ) :
    Integrable (fullSemidiscreteValue μ Y (fun x y ↦ c x y + t * g x y))
      (dirichletOne m) ∧
    (∫ x : Fin (m + 1) → S,
      perturbedAssignmentValue (fun i j ↦ c (x i) (Y j))
        (fun i j ↦ g (x i) (Y j)) t / (m + 1 : ℕ) ∂Measure.pi (fun _ ↦ μ)) =
      ∫ p, fullSemidiscreteValue μ Y (fun x y ↦ c x y + t * g x y) p
        ∂dirichletOne m := by
  have h := integral_iid_perturbedAssignmentValue_eq_dirichlet_semidiscreteValue μ
    (fun j x ↦ c x (Y j)) (fun j x ↦ g x (Y j))
    (fun _ ↦ hc.comp (measurable_id.prodMk measurable_const)) hci
    (fun _ ↦ hg.comp (measurable_id.prodMk measurable_const))
    (fun j l hjl ↦ hatom (Y j) (Y l) (hY.ne hjl)) G (fun x j ↦ hbound x (Y j)) t
  have heq := ae_fullSemidiscreteValue_eq_semidiscreteValue μ Y hY c g hc hci hg G hbound t
  exact ⟨h.1.congr heq.symm, h.2.2.trans (integral_congr_ae heq.symm)⟩

/-- Fixed actual targets: the complete coupling primal has the actual normalized Exp(1) value law. -/
theorem integral_iid_pressure_eq_normalizedExp_fullSemidiscreteValue
    (μ : Measure S) [IsProbabilityMeasure μ]
    (Y : Fin (m + 1) → T) (hY : Function.Injective Y)
    (c g : S → T → ℝ) (hc : Measurable (Function.uncurry c))
    (hci : ∀ j, Integrable (fun s ↦ c s (Y j)) μ)
    (hg : Measurable (Function.uncurry g))
    (hatom : ∀ y z, y ≠ z → NullSingletonClass (μ.map (fun x ↦ c x y - c x z)))
    (G : ℝ≥0) (hbound : ∀ x y, |g x y| ≤ G) (t : ℝ) :
    Integrable (fun e : Fin (m + 1) → ℝ ↦
      fullSemidiscreteValue μ Y (fun x y ↦ c x y + t * g x y) (normalizedMass m e))
      (Measure.pi (fun _ ↦ expMeasure 1)) ∧
    (∫ x : Fin (m + 1) → S,
      perturbedAssignmentValue (fun i j ↦ c (x i) (Y j))
        (fun i j ↦ g (x i) (Y j)) t / (m + 1 : ℕ) ∂Measure.pi (fun _ ↦ μ)) =
      ∫ e : Fin (m + 1) → ℝ,
        fullSemidiscreteValue μ Y (fun x y ↦ c x y + t * g x y) (normalizedMass m e)
          ∂Measure.pi (fun _ ↦ expMeasure 1) := by
  have h := integral_iid_pressure_eq_fullSemidiscreteValue μ Y hY c g hc hci hg hatom G hbound t
  have hpres : MeasurePreserving (normalizedMass m)
      (Measure.pi (fun _ : Fin (m + 1) ↦ expMeasure 1)) (dirichletOne m) :=
    ⟨measurable_normalizedMass m, map_normalizedMass_pi_exp m⟩
  refine ⟨hpres.integrable_comp_of_integrable h.1, ?_⟩
  rw [h.2, ← hpres.map_eq, integral_map hpres.measurable.aemeasurable]
  rw [hpres.map_eq]
  exact h.1.aestronglyMeasurable

variable [MeasurableEq T]

/-- The original two-color iid value equals the actual full semidiscrete coupling value,
averaged over the same target law and independent Dirichlet weights. -/
theorem integral_original_bipartite_pressure_eq_fullSemidiscreteValue
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (X : Fin (m + 1) → Ω → S) (Y : Fin (m + 1) → Ω → T)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXi : iIndepFun X P) (hYi : iIndepFun Y P)
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ j, P.map (Y j) = ν)
    (hXY : IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P)
    (c g : S → T → ℝ) (hc : Measurable (Function.uncurry c))
    (hci : Integrable (Function.uncurry c) (μ.prod ν))
    (hg : Measurable (Function.uncurry g))
    (hatom : ∀ y z, y ≠ z → NullSingletonClass (μ.map (fun x ↦ c x y - c x z)))
    (G : ℝ≥0) (hbound : ∀ x y, |g x y| ≤ G) (t : ℝ) :
    Integrable (fun y : Fin (m + 1) → T ↦
      ∫ p, fullSemidiscreteValue μ y (fun x y ↦ c x y + t * g x y) p ∂dirichletOne m)
      (Measure.pi (fun _ ↦ ν)) ∧
    (∫ ω, perturbedAssignmentValue (fun i j ↦ c (X i ω) (Y j ω))
      (fun i j ↦ g (X i ω) (Y j ω)) t / (m + 1 : ℕ) ∂P) =
      ∫ y : Fin (m + 1) → T, ∫ p,
        fullSemidiscreteValue μ y (fun x y ↦ c x y + t * g x y) p
          ∂dirichletOne m ∂Measure.pi (fun _ ↦ ν) := by
  have h := integral_original_bipartite_pressure_eq_dirichlet_semidiscreteValue
    P μ ν X Y hX hY hXi hYi hXlaw hYlaw hXY c g hc hci hg hatom G hbound t
  have hi : ∀ᵐ y ∂Measure.pi (fun _ : Fin (m + 1) ↦ ν),
      ∀ j, Integrable (fun x ↦ c x (y j)) μ := by
    apply ae_all_iff.mpr
    intro j
    have hj := (measurePreserving_eval (fun _ : Fin (m + 1) ↦ ν) j).quasiMeasurePreserving
    exact hj.tendsto_ae.eventually hci.prod_left_ae
  have heq : (fun y : Fin (m + 1) → T ↦
      ∫ p, semidiscreteValue μ (fun x j ↦ c x (y j) + t * g x (y j)) p ∂dirichletOne m) =ᵐ[
      Measure.pi (fun _ ↦ ν)] fun y ↦
      ∫ p, fullSemidiscreteValue μ y (fun x y ↦ c x y + t * g x y) p ∂dirichletOne m := by
    filter_upwards [ae_injective_pi_of_nullSingletonClass (ι := Fin (m + 1)) ν, hi]
      with y hy hiy
    exact integral_congr_ae
      (ae_fullSemidiscreteValue_eq_semidiscreteValue μ y hy c g hc hiy hg G hbound t).symm
  exact ⟨h.2.1.congr heq, h.2.2.trans (integral_congr_ae heq)⟩

end OTSelector.Probability
