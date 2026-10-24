import OTSelector.Probability.CavitySemidiscreteJointReadout
import OTSelector.Probability.CavitySemidiscretePressureBipartite
import OTSelector.Probability.DirichletExponentialLaw

/-!
# Joint random-target pressure under actual Dirichlet and exponential laws

Actual measurable cavity optimizers give joint integrability at good tilts. The
common Lipschitz bound extends this to every real tilt. Fubini then identifies the
original iid pressure with one genuine target-and-weight product integral.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S V : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [MeasurableSpace V] [StandardBorelSpace V]

/-- Joint integrability of the actual primal at every tilt, including atom-creating tilts. -/
theorem integrable_parameterized_dirichlet_semidiscreteValue_tilt
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ρ : Measure V) [IsProbabilityMeasure ρ]
    (c g : V → Fin (m + 1) → S → ℝ)
    (hc : ∀ j, Measurable (fun z : V × S ↦ c z.1 j z.2))
    (hci : ∀ j, Integrable (fun z : V × S ↦ c z.1 j z.2) (ρ.prod μ))
    (hg : ∀ j, Measurable (fun z : V × S ↦ g z.1 j z.2))
    (hatom : ∀ᵐ v ∂ρ, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ c v j s - c v l s)))
    (G : ℝ≥0) (hbound : ∀ v s j, |g v j s| ≤ G) (t : ℝ) :
    Integrable (fun z : V × (Fin (m + 1) → ℝ) ↦
      semidiscreteValue μ (fun s j ↦ c z.1 j s + t * g z.1 j s) z.2)
      (ρ.prod (dirichletOne m)) := by
  let H : ℝ → V × (Fin (m + 1) → ℝ) → ℝ := fun u z ↦
    semidiscreteValue μ (fun s j ↦ c z.1 j s + u * g z.1 j s) z.2
  let B : Set ℝ := {u | ¬∀ᵐ v ∂ρ, ∀ j l, j ≠ l → NullSingletonClass
    (μ.map (fun s ↦ (c v j s + u * g v j s) - (c v l s + u * g v l s)))}
  have hB : B.Countable := countable_bad_parameterized_cavity_tilts μ ρ
    (fun j v s ↦ c v j s) (fun j v s ↦ g v j s) hc hg hatom
  have hgi j : Integrable (fun z : V × S ↦ g z.1 j z.2) (ρ.prod μ) :=
    (integrable_const (G : ℝ)).mono' (hg j).aestronglyMeasurable
      (Eventually.of_forall fun z ↦ by simpa only [Real.norm_eq_abs] using hbound z.1 z.2 j)
  have hgs (v : V) (j : Fin (m + 1)) : Integrable (g v j) μ :=
    (integrable_const (G : ℝ)).mono'
      ((hg j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun s ↦ by simpa only [Real.norm_eq_abs] using hbound v s j)
  have hic : ∀ᵐ z ∂ρ.prod (dirichletOne m), ∀ j, Integrable (c z.1 j) μ :=
    measurePreserving_fst.quasiMeasurePreserving.ae
      (ae_all_iff.mpr (fun j ↦ (hci j).prod_right_ae))
  have hs : ∀ᵐ z ∂ρ.prod (dirichletOne m), z.2 ∈ stdSimplex ℝ (Fin (m + 1)) :=
    measurePreserving_snd.quasiMeasurePreserving.ae (ae_mem_stdSimplex_dirichletOne m)
  have hlip : ∀ᵐ z ∂ρ.prod (dirichletOne m), LipschitzWith G (fun u ↦ H u z) := by
    filter_upwards [hic, hs] with z hz hzp
    exact lipschitzWith_semidiscreteValue_tilt μ (fun s j ↦ c z.1 j s)
      (fun s j ↦ g z.1 j s) hz (hgs z.1) G
      (Eventually.of_forall fun s j ↦ hbound z.1 s j) z.2 hzp
  apply integrable_of_dense_integrable_of_ae_lipschitz
    (ρ.prod (dirichletOne m)) H G hlip Bᶜ (hB.dense_compl ℝ) ?_ t
  intro u hu
  exact integrable_parameterized_dirichlet_semidiscreteValue μ ρ
    (fun v j s ↦ c v j s + u * g v j s)
    (fun j ↦ (hc j).add ((hg j).const_mul u))
    (fun j ↦ (hci j).add ((hgi j).const_mul u)) (not_not.mp hu)

variable {T : Type*} [MeasurableSpace T] [StandardBorelSpace T]

/-- Every tilted primal is jointly integrable on the original iid targets and Dirichlet masses. -/
theorem integrable_bipartite_dirichlet_semidiscreteValue
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (c g : S → T → ℝ) (hc : Measurable (Function.uncurry c))
    (hci : Integrable (Function.uncurry c) (μ.prod ν))
    (hg : Measurable (Function.uncurry g))
    (hatom : ∀ y z, y ≠ z → NullSingletonClass (μ.map (fun x ↦ c x y - c x z)))
    (G : ℝ≥0) (hbound : ∀ x y, |g x y| ≤ G) (t : ℝ) :
    Integrable (fun z : (Fin (m + 1) → T) × (Fin (m + 1) → ℝ) ↦
      semidiscreteValue μ (fun s j ↦ c s (z.1 j) + t * g s (z.1 j)) z.2)
      ((Measure.pi (fun _ ↦ ν)).prod (dirichletOne m)) := by
  have hpair (j : Fin (m + 1)) :
      MeasurePreserving (fun z : (Fin (m + 1) → T) × S ↦ (z.2, z.1 j))
        ((Measure.pi (fun _ ↦ ν)).prod μ) (μ.prod ν) :=
    Measure.measurePreserving_swap.comp
      ((measurePreserving_eval (fun _ : Fin (m + 1) ↦ ν) j).prod
        (MeasurePreserving.id μ))
  have hat : ∀ᵐ y ∂Measure.pi (fun _ : Fin (m + 1) ↦ ν), ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ c s (y j) - c s (y l))) := by
    filter_upwards [ae_injective_pi_of_nullSingletonClass (ι := Fin (m + 1)) ν] with y hy
    exact fun j l hjl ↦ hatom (y j) (y l) (hy.ne hjl)
  exact integrable_parameterized_dirichlet_semidiscreteValue_tilt
    μ (Measure.pi (fun _ : Fin (m + 1) ↦ ν))
    (fun y j s ↦ c s (y j)) (fun y j s ↦ g s (y j))
    (fun j ↦ hc.comp (hpair j).measurable)
    (fun j ↦ (hpair j).integrable_comp_of_integrable hci)
    (fun j ↦ hg.comp (hpair j).measurable) hat G (fun y s j ↦ hbound s (y j)) t

/-- The original finite iid pressure equals a single jointly integrable target-weight integral. -/
theorem integral_bipartite_pressure_eq_joint_dirichlet_semidiscreteValue
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (c g : S → T → ℝ) (hc : Measurable (Function.uncurry c))
    (hci : Integrable (Function.uncurry c) (μ.prod ν))
    (hg : Measurable (Function.uncurry g))
    (hatom : ∀ y z, y ≠ z → NullSingletonClass (μ.map (fun x ↦ c x y - c x z)))
    (G : ℝ≥0) (hbound : ∀ x y, |g x y| ≤ G) (t : ℝ) :
    (∫ q : (Fin (m + 1) → T) × (Fin (m + 1) → S),
      perturbedAssignmentValue (fun i j ↦ c (q.2 i) (q.1 j))
        (fun i j ↦ g (q.2 i) (q.1 j)) t / (m + 1 : ℕ)
        ∂(Measure.pi (fun _ ↦ ν)).prod (Measure.pi (fun _ ↦ μ))) =
      ∫ z : (Fin (m + 1) → T) × (Fin (m + 1) → ℝ),
        semidiscreteValue μ (fun s j ↦ c s (z.1 j) + t * g s (z.1 j)) z.2
          ∂(Measure.pi (fun _ ↦ ν)).prod (dirichletOne m) := by
  exact (integral_bipartite_pressure_eq_dirichlet_semidiscreteValue
    μ ν c g hc hci hg hatom G hbound t).2.trans
      (integral_prod _ (integrable_bipartite_dirichlet_semidiscreteValue
        μ ν c g hc hci hg hatom G hbound t)).symm

/-- The same genuine product integral uses actual independent exponential marks after
normalization. Joint integrability is retained, so it supports localized comparisons. -/
theorem integral_bipartite_pressure_eq_joint_normalizedExp_semidiscreteValue
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (c g : S → T → ℝ) (hc : Measurable (Function.uncurry c))
    (hci : Integrable (Function.uncurry c) (μ.prod ν))
    (hg : Measurable (Function.uncurry g))
    (hatom : ∀ y z, y ≠ z → NullSingletonClass (μ.map (fun x ↦ c x y - c x z)))
    (G : ℝ≥0) (hbound : ∀ x y, |g x y| ≤ G) (t : ℝ) :
    Integrable (fun z : (Fin (m + 1) → T) × (Fin (m + 1) → ℝ) ↦
      semidiscreteValue μ (fun s j ↦ c s (z.1 j) + t * g s (z.1 j)) (normalizedMass m z.2))
      ((Measure.pi (fun _ ↦ ν)).prod (Measure.pi (fun _ ↦ expMeasure 1))) ∧
    (∫ q : (Fin (m + 1) → T) × (Fin (m + 1) → S),
      perturbedAssignmentValue (fun i j ↦ c (q.2 i) (q.1 j))
        (fun i j ↦ g (q.2 i) (q.1 j)) t / (m + 1 : ℕ)
        ∂(Measure.pi (fun _ ↦ ν)).prod (Measure.pi (fun _ ↦ μ))) =
      ∫ z : (Fin (m + 1) → T) × (Fin (m + 1) → ℝ),
        semidiscreteValue μ (fun s j ↦ c s (z.1 j) + t * g s (z.1 j)) (normalizedMass m z.2)
          ∂(Measure.pi (fun _ ↦ ν)).prod (Measure.pi (fun _ ↦ expMeasure 1)) := by
  let := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  have hnorm : MeasurePreserving (normalizedMass m)
      (Measure.pi (fun _ : Fin (m + 1) ↦ expMeasure 1)) (dirichletOne m) :=
    ⟨measurable_normalizedMass m, map_normalizedMass_pi_exp m⟩
  have hpres := (MeasurePreserving.id (Measure.pi (fun _ : Fin (m + 1) ↦ ν))).prod hnorm
  have hi := integrable_bipartite_dirichlet_semidiscreteValue (m := m)
    μ ν c g hc hci hg hatom G hbound t
  refine ⟨hpres.integrable_comp_of_integrable hi, ?_⟩
  rw [integral_bipartite_pressure_eq_joint_dirichlet_semidiscreteValue
    μ ν c g hc hci hg hatom G hbound t, ← hpres.map_eq,
    integral_map hpres.measurable.aemeasurable]
  · rfl
  · rw [hpres.map_eq]
    exact hi.aestronglyMeasurable

end OTSelector.Probability
