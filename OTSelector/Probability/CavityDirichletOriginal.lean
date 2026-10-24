import OTSelector.Probability.Dirichlet.CavityLaw
import OTSelector.Probability.IIDBipartiteAssignment

/-!
# Dirichlet cavity masses on the original probability space

The fixed-target law transfers along the exact iid array law. With random target data,
the actual cell mass vector has the product of the target law and the Dirichlet law.
Thus independence of these masses from the target cloud is a conclusion.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S B Ω : Type*}
  [MeasurableSpace S] [MeasurableSpace B] [MeasurableSpace Ω]

/-- The actual retained source array may live on any original iid probability space. -/
theorem map_iidCavityMassVector_of_iid
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (X : Fin m → Ω → S) (hX : ∀ k, Measurable (X k))
    (hi : iIndepFun X P) (hlaw : ∀ k, P.map (X k) = μ)
    (c : Fin (m + 1) → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c j s - c l s))) :
    P.map (fun ω ↦ iidCavityMassVector μ c (fun k ↦ X k ω)) = dirichletOne m := by
  have harray : Measurable (fun ω k ↦ X k ω) := measurable_pi_lambda _ hX
  have harraylaw : P.map (fun ω k ↦ X k ω) = Measure.pi (fun _ : Fin m ↦ μ) := by
    rw [iIndepFun.map_fun_eq_pi_map (fun k ↦ (hX k).aemeasurable) hi]
    simp_rw [hlaw]
  change P.map (iidCavityMassVector μ c ∘ (fun ω k ↦ X k ω)) = _
  rw [← Measure.map_map (measurable_iidCavityMassVector μ c hc) harray,
    harraylaw, map_iidCavityMassVector_eq_dirichletOne μ c hc hatom]

/-- Cell mass vectors are jointly measurable with arbitrary measurable target parameters. -/
theorem measurable_parameterizedIidCavityMassVector
    (μ : Measure S) [IsFiniteMeasure μ]
    (c : B → Fin (m + 1) → S → ℝ)
    (hc : ∀ j, Measurable (fun z : B × S ↦ c z.1 j z.2)) :
    Measurable (fun q : B × (Fin m → S) ↦ iidCavityMassVector μ (c q.1) q.2) := by
  let retained : B × (Fin m → S) → Fin (m + 1) → Fin (m + 1) → ℝ :=
    fun q ↦ iidCapacityInputCost (c q.1) (fun k w ↦ w k) q.2
  let row : (B × (Fin m → S)) × S → Fin (m + 1) → ℝ :=
    fun z j ↦ c z.1.1 j z.2
  have hret (k j : Fin (m + 1)) : Measurable (fun q ↦ retained q k j) := by
    refine Fin.succAboveCases 0 ?_ (fun l ↦ ?_) k
    · simp only [retained, iidCapacityInputCost, Fin.insertNth_apply_same]
      exact measurable_const
    · simpa only [retained, iidCapacityInputCost_retained, Function.comp_def] using
        (hc j).comp (measurable_fst.prodMk ((measurable_pi_apply l).comp measurable_snd))
  have hrow (j : Fin (m + 1)) : Measurable (fun z ↦ row z j) :=
    (hc j).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  apply measurable_pi_iff.mpr
  intro j
  exact (measurable_cavityCellMass μ retained row hret hrow 0 j).ennreal_toReal

/-- Conditional atomlessness yields the exact joint law of the parameter and its actual
cavity mass vector under the original product sampling law. -/
theorem measurePreserving_parameterizedIidCavityMassVector
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure B) [SFinite ν]
    (c : B → Fin (m + 1) → S → ℝ)
    (hc : ∀ j, Measurable (fun z : B × S ↦ c z.1 j z.2))
    (hatom : ∀ᵐ b ∂ν, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ c b j s - c b l s))) :
    MeasurePreserving (fun q : B × (Fin m → S) ↦
      (q.1, iidCavityMassVector μ (c q.1) q.2))
      (ν.prod (Measure.pi (fun _ : Fin m ↦ μ))) (ν.prod (dirichletOne m)) := by
  refine (MeasurePreserving.id ν).skew_product
    (g := fun b w ↦ iidCavityMassVector μ (c b) w)
    (μc := Measure.pi (fun _ : Fin m ↦ μ)) (μd := dirichletOne m)
    (measurable_parameterizedIidCavityMassVector μ c hc) ?_
  filter_upwards [hatom] with b hb
  exact map_iidCavityMassVector_eq_dirichletOne μ (c b)
    (fun j ↦ (hc j).comp measurable_prodMk_left) hb

/-- The target-parameter and cell-mass product law holds on the original probability
space, using the original array independence and actual marginal laws. -/
theorem map_parameterizedIidCavityMassVector_of_indep_iid
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure B) [IsProbabilityMeasure ν]
    (X : Fin m → Ω → S) (Y : Ω → B)
    (hX : ∀ k, Measurable (X k)) (hY : Measurable Y)
    (hi : iIndepFun X P) (hXlaw : ∀ k, P.map (X k) = μ) (hYlaw : P.map Y = ν)
    (hXY : IndepFun Y (fun ω k ↦ X k ω) P)
    (c : B → Fin (m + 1) → S → ℝ)
    (hc : ∀ j, Measurable (fun z : B × S ↦ c z.1 j z.2))
    (hatom : ∀ᵐ b ∂ν, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ c b j s - c b l s))) :
    P.map (fun ω ↦ (Y ω, iidCavityMassVector μ (c (Y ω)) (fun k ↦ X k ω))) =
      ν.prod (dirichletOne m) := by
  have hmX : Measurable (fun ω k ↦ X k ω) := measurable_pi_lambda _ hX
  have hlX : P.map (fun ω k ↦ X k ω) = Measure.pi (fun _ : Fin m ↦ μ) := by
    rw [iIndepFun.map_fun_eq_pi_map (fun k ↦ (hX k).aemeasurable) hi]
    simp_rw [hXlaw]
  have hpair := hXY.map_prod_eq_prod_map_map hY.aemeasurable hmX.aemeasurable
  rw [hYlaw, hlX] at hpair
  have hpres := measurePreserving_parameterizedIidCavityMassVector μ ν c hc hatom
  have hcomp := (hpres.comp ⟨hY.prodMk hmX, hpair⟩).map_eq
  exact hcomp

variable {T : Type*} [MeasurableSpace T] [MeasurableEq T]

/-- For the two original iid colors, the actual mass vector is Dirichlet and independent
of the entire target cloud. Target collisions are removed by their proven null event. -/
theorem map_bipartiteIidCavityMassVector_eq_prod
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (X : Fin m → Ω → S) (Y : Fin (m + 1) → Ω → T)
    (hX : ∀ k, Measurable (X k)) (hY : ∀ j, Measurable (Y j))
    (hXi : iIndepFun X P) (hYi : iIndepFun Y P)
    (hXlaw : ∀ k, P.map (X k) = μ) (hYlaw : ∀ j, P.map (Y j) = ν)
    (hXY : IndepFun (fun ω k ↦ X k ω) (fun ω j ↦ Y j ω) P)
    (c : S → T → ℝ) (hc : Measurable (Function.uncurry c))
    (hatom : ∀ y z, y ≠ z → NullSingletonClass (μ.map (fun s ↦ c s y - c s z))) :
    P.map (fun ω ↦ ((fun j ↦ Y j ω),
      iidCavityMassVector μ (fun j s ↦ c s (Y j ω)) (fun k ↦ X k ω))) =
      (Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod (dirichletOne m) := by
  have hmY : Measurable (fun ω j ↦ Y j ω) := measurable_pi_lambda _ hY
  have hlY : P.map (fun ω j ↦ Y j ω) = Measure.pi (fun _ : Fin (m + 1) ↦ ν) := by
    rw [iIndepFun.map_fun_eq_pi_map (fun j ↦ (hY j).aemeasurable) hYi]
    simp_rw [hYlaw]
  apply map_parameterizedIidCavityMassVector_of_indep_iid P μ _ X _ hX hmY hXi
    hXlaw hlY hXY.symm (fun y j s ↦ c s (y j))
  · intro j
    exact hc.comp (measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst))
  · filter_upwards [ae_injective_pi_of_nullSingletonClass (ι := Fin (m + 1)) ν] with y hy
    intro j l hjl
    exact hatom (y j) (y l) (hy.ne hjl)

end OTSelector.Probability
