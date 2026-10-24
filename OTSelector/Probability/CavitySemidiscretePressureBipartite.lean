import OTSelector.Probability.CavitySemidiscretePressureSampling

/-!
# Original two-color iid pressure and random semidiscrete target weights

The conditional value identity holds on one full-measure target-cloud event for every
real perturbation parameter. Actual edge integrability gives the unconditional identity
by Fubini and the exact joint law of the two original iid arrays.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S T Ω : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [MeasurableSpace T] [MeasurableEq T] [MeasurableSpace Ω]

/-- One full-measure event of target clouds supports the conditional identity at every tilt. -/
theorem ae_integral_iid_pressure_eq_dirichlet_semidiscreteValue
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (c g : S → T → ℝ) (hc : Measurable (Function.uncurry c))
    (hci : Integrable (Function.uncurry c) (μ.prod ν))
    (hg : Measurable (Function.uncurry g))
    (hatom : ∀ y z, y ≠ z → NullSingletonClass (μ.map (fun x ↦ c x y - c x z)))
    (G : ℝ≥0) (hbound : ∀ x y, |g x y| ≤ G) :
    ∀ᵐ y ∂Measure.pi (fun _ : Fin (m + 1) ↦ ν), ∀ t : ℝ,
      Integrable (semidiscreteValue μ (fun x j ↦ c x (y j) + t * g x (y j)))
        (dirichletOne m) ∧
      Integrable (fun x : Fin (m + 1) → S ↦
        perturbedAssignmentValue (fun i j ↦ c (x i) (y j))
          (fun i j ↦ g (x i) (y j)) t / (m + 1 : ℕ))
        (Measure.pi (fun _ ↦ μ)) ∧
      (∫ x : Fin (m + 1) → S,
        perturbedAssignmentValue (fun i j ↦ c (x i) (y j))
          (fun i j ↦ g (x i) (y j)) t / (m + 1 : ℕ)
          ∂Measure.pi (fun _ ↦ μ)) =
        ∫ p, semidiscreteValue μ (fun x j ↦ c x (y j) + t * g x (y j)) p
          ∂dirichletOne m := by
  have hi : ∀ᵐ y ∂Measure.pi (fun _ : Fin (m + 1) ↦ ν),
      ∀ j, Integrable (fun x ↦ c x (y j)) μ := by
    apply ae_all_iff.mpr
    intro j
    have hj := (measurePreserving_eval (fun _ : Fin (m + 1) ↦ ν) j).quasiMeasurePreserving
    exact hj.tendsto_ae.eventually hci.prod_left_ae
  filter_upwards [ae_injective_pi_of_nullSingletonClass (ι := Fin (m + 1)) ν, hi]
    with y hy hiy
  intro t
  exact integral_iid_perturbedAssignmentValue_eq_dirichlet_semidiscreteValue μ
    (fun j x ↦ c x (y j)) (fun j x ↦ g x (y j))
    (fun _ ↦ hc.comp (measurable_id.prodMk measurable_const)) hiy
    (fun _ ↦ hg.comp (measurable_id.prodMk measurable_const))
    (fun j l hjl ↦ hatom (y j) (y l) (hy.ne hjl)) G
    (fun x j ↦ hbound x (y j)) t

omit [StandardBorelSpace S] [MeasurableEq T] in
/-- Product integrability of the genuine finite minimum follows from the original edge law. -/
theorem integrable_bipartite_perturbedAssignmentValue
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν]
    (c g : S → T → ℝ) (hc : Measurable (Function.uncurry c))
    (hci : Integrable (Function.uncurry c) (μ.prod ν))
    (hg : Measurable (Function.uncurry g))
    (G : ℝ≥0) (hbound : ∀ x y, |g x y| ≤ G) (t : ℝ) :
    Integrable (fun q : (Fin (m + 1) → T) × (Fin (m + 1) → S) ↦
      perturbedAssignmentValue (fun i j ↦ c (q.2 i) (q.1 j))
        (fun i j ↦ g (q.2 i) (q.1 j)) t / (m + 1 : ℕ))
      ((Measure.pi (fun _ ↦ ν)).prod (Measure.pi (fun _ ↦ μ))) := by
  have hgi : Integrable (Function.uncurry g) (μ.prod ν) :=
    (integrable_const (G : ℝ)).mono' hg.aestronglyMeasurable
      (Eventually.of_forall fun q ↦ by simpa only [Real.norm_eq_abs, Function.uncurry] using hbound q.1 q.2)
  have hij (i j : Fin (m + 1)) :
      MeasurePreserving (fun q : (Fin (m + 1) → T) × (Fin (m + 1) → S) ↦
        (q.2 i, q.1 j))
        ((Measure.pi (fun _ ↦ ν)).prod (Measure.pi (fun _ ↦ μ))) (μ.prod ν) :=
    Measure.measurePreserving_swap.comp
      ((measurePreserving_eval (fun _ : Fin (m + 1) ↦ ν) j).prod
        (measurePreserving_eval (fun _ : Fin (m + 1) ↦ μ) i))
  let C : ((Fin (m + 1) → T) × (Fin (m + 1) → S)) →
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    fun q i j ↦ c (q.2 i) (q.1 j) + t * g (q.2 i) (q.1 j)
  have hC := integrable_assignmentValue
    ((Measure.pi (fun _ ↦ ν)).prod (Measure.pi (fun _ ↦ μ))) C
    (fun i j ↦ (hc.comp (hij i j).measurable).add
      ((hg.comp (hij i j).measurable).const_mul t))
    (fun i j ↦ (hij i j).integrable_comp_of_integrable (hci.add (hgi.const_mul t)))
  have heq (q : (Fin (m + 1) → T) × (Fin (m + 1) → S)) :
      perturbedAssignmentValue (C q) 0 0 =
        perturbedAssignmentValue (fun i j ↦ c (q.2 i) (q.1 j))
          (fun i j ↦ g (q.2 i) (q.1 j)) t := by
    simp only [perturbedAssignmentValue, perturbedEdgeCost_zero]
    rfl
  exact (hC.div_const (m + 1 : ℕ)).congr (Eventually.of_forall fun q ↦ congrArg (fun v : ℝ ↦ v / (m + 1 : ℕ)) (heq q))

/-- Integrating the conditional identity gives the genuine two-color product pressure. -/
theorem integral_bipartite_pressure_eq_dirichlet_semidiscreteValue
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (c g : S → T → ℝ) (hc : Measurable (Function.uncurry c))
    (hci : Integrable (Function.uncurry c) (μ.prod ν))
    (hg : Measurable (Function.uncurry g))
    (hatom : ∀ y z, y ≠ z → NullSingletonClass (μ.map (fun x ↦ c x y - c x z)))
    (G : ℝ≥0) (hbound : ∀ x y, |g x y| ≤ G) (t : ℝ) :
    Integrable (fun y : Fin (m + 1) → T ↦
      ∫ p, semidiscreteValue μ (fun x j ↦ c x (y j) + t * g x (y j)) p
        ∂dirichletOne m) (Measure.pi (fun _ ↦ ν)) ∧
    (∫ q : (Fin (m + 1) → T) × (Fin (m + 1) → S),
      perturbedAssignmentValue (fun i j ↦ c (q.2 i) (q.1 j))
        (fun i j ↦ g (q.2 i) (q.1 j)) t / (m + 1 : ℕ)
        ∂(Measure.pi (fun _ ↦ ν)).prod (Measure.pi (fun _ ↦ μ))) =
      ∫ y : Fin (m + 1) → T, ∫ p,
        semidiscreteValue μ (fun x j ↦ c x (y j) + t * g x (y j)) p
          ∂dirichletOne m ∂Measure.pi (fun _ ↦ ν) := by
  have hF := integrable_bipartite_perturbedAssignmentValue (m := m)
    μ ν c g hc hci hg G hbound t
  have heq := (ae_integral_iid_pressure_eq_dirichlet_semidiscreteValue (m := m)
    μ ν c g hc hci hg hatom G hbound).mono fun _ h ↦ (h t).2.2
  refine ⟨hF.integral_prod_left.congr heq, ?_⟩
  exact (integral_prod _ hF).trans (integral_congr_ae heq)

/-- The pressure identity on the original probability space of the two independent iid colors. -/
theorem integral_original_bipartite_pressure_eq_dirichlet_semidiscreteValue
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
    Integrable (fun ω ↦
      perturbedAssignmentValue (fun i j ↦ c (X i ω) (Y j ω))
        (fun i j ↦ g (X i ω) (Y j ω)) t / (m + 1 : ℕ)) P ∧
    Integrable (fun y : Fin (m + 1) → T ↦
      ∫ p, semidiscreteValue μ (fun x j ↦ c x (y j) + t * g x (y j)) p
        ∂dirichletOne m) (Measure.pi (fun _ ↦ ν)) ∧
    (∫ ω, perturbedAssignmentValue (fun i j ↦ c (X i ω) (Y j ω))
      (fun i j ↦ g (X i ω) (Y j ω)) t / (m + 1 : ℕ) ∂P) =
      ∫ y : Fin (m + 1) → T, ∫ p,
        semidiscreteValue μ (fun x j ↦ c x (y j) + t * g x (y j)) p
          ∂dirichletOne m ∂Measure.pi (fun _ ↦ ν) := by
  have hmX : Measurable (fun ω i ↦ X i ω) := measurable_pi_lambda _ hX
  have hmY : Measurable (fun ω j ↦ Y j ω) := measurable_pi_lambda _ hY
  have hlX : P.map (fun ω i ↦ X i ω) = Measure.pi (fun _ : Fin (m + 1) ↦ μ) := by
    rw [iIndepFun.map_fun_eq_pi_map (fun i ↦ (hX i).aemeasurable) hXi]
    simp_rw [hXlaw]
  have hlY : P.map (fun ω j ↦ Y j ω) = Measure.pi (fun _ : Fin (m + 1) ↦ ν) := by
    rw [iIndepFun.map_fun_eq_pi_map (fun j ↦ (hY j).aemeasurable) hYi]
    simp_rw [hYlaw]
  have hpair := hXY.symm.map_prod_eq_prod_map_map hmY.aemeasurable hmX.aemeasurable
  rw [hlY, hlX] at hpair
  have hpres : MeasurePreserving (fun ω ↦ ((fun j ↦ Y j ω), (fun i ↦ X i ω))) P
      ((Measure.pi (fun _ ↦ ν)).prod (Measure.pi (fun _ ↦ μ))) :=
    ⟨hmY.prodMk hmX, hpair⟩
  have hF := integrable_bipartite_perturbedAssignmentValue (m := m)
    μ ν c g hc hci hg G hbound t
  have hval := integral_bipartite_pressure_eq_dirichlet_semidiscreteValue (m := m)
    μ ν c g hc hci hg hatom G hbound t
  refine ⟨hpres.integrable_comp_of_integrable hF, hval.1, ?_⟩
  rw [← hval.2, ← hpair, integral_map (hmY.prodMk hmX).aemeasurable]
  rw [hpair]
  exact hF.aestronglyMeasurable

end OTSelector.Probability
