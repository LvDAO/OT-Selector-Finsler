import OTSelector.Probability.CavitySemidiscretePressureJoint
import OTSelector.Probability.CavitySemidiscreteTiltSupergradient
import OTSelector.Probability.CavitySemidiscreteJointReadout

/-!
# Supergradients of the expected semidiscrete pressure

On a common random environment `v` (for example a target cloud) and Dirichlet
mass vector, a jointly measurable optimal allocation for the tilted cost
`c v + t g v` produces a supergradient of the *expected* pressure at tilt `t`:
the expectation of its probe cost `∫ g v da`.

The proof integrates the pointwise supergradient inequality of
`semidiscreteValue_supergradient_of_tilted_optimal` against the environment law.
Joint integrability of the tilted value is supplied by
`integrable_parameterized_dirichlet_semidiscreteValue_tilt`, and joint
integrability of the probe readout by
`integrable_parameterized_dirichlet_allocationCost`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S V : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [MeasurableSpace V] [StandardBorelSpace V]

/-- **Expected supergradient from a jointly measurable tilted optimum.** -/
theorem integral_semidiscreteValue_supergradient_of_tilted_optimal
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ρ : Measure V) [IsProbabilityMeasure ρ]
    (c g : V → Fin (m + 1) → S → ℝ)
    (hc : ∀ j, Measurable (fun z : V × S ↦ c z.1 j z.2))
    (hci : ∀ j, Integrable (fun z : V × S ↦ c z.1 j z.2) (ρ.prod μ))
    (hg : ∀ j, Measurable (fun z : V × S ↦ g z.1 j z.2))
    (hatom : ∀ᵐ v ∂ρ, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ c v j s - c v l s)))
    (G : ℝ≥0) (hbound : ∀ v s j, |g v j s| ≤ G)
    (a : ((V × (Fin (m + 1) → ℝ)) × S) → Fin (m + 1) → ℝ)
    (ha : ∀ j, Measurable (fun z ↦ a z j))
    {t : ℝ}
    (hopt : ∀ᵐ z ∂ρ.prod (dirichletOne m),
      IsOptimalSemidiscreteAllocation μ z.2
        (fun s j ↦ c z.1 j s + t * g z.1 j s) (fun s ↦ a (z, s))) :
    let P : ℝ → ℝ := fun u ↦ ∫ z : V × (Fin (m + 1) → ℝ),
      semidiscreteValue μ (fun s j ↦ c z.1 j s + u * g z.1 j s) z.2
        ∂ρ.prod (dirichletOne m)
    ∀ u : ℝ, P u ≤ P t + (u - t) * ∫ z : V × (Fin (m + 1) → ℝ),
      semidiscreteAllocationCost μ (fun s j ↦ g z.1 j s) (fun s ↦ a (z, s))
        ∂ρ.prod (dirichletOne m) := by
  dsimp only
  intro u
  have hgi : ∀ j, Integrable (fun z : V × S ↦ g z.1 j z.2) (ρ.prod μ) := fun j =>
    (integrable_const (G : ℝ)).mono' (hg j).aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hbound z.1 z.2 j)
  have hgs (v : V) (j : Fin (m + 1)) : Integrable (g v j) μ :=
    (integrable_const (G : ℝ)).mono'
      ((hg j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using hbound v s j)
  have hic : ∀ᵐ z ∂ρ.prod (dirichletOne m), ∀ j, Integrable (c z.1 j) μ :=
    measurePreserving_fst.quasiMeasurePreserving.ae
      (ae_all_iff.mpr (fun j => (hci j).prod_right_ae))
  -- Integrability of the tilted value at the two tilts.
  have hVu : Integrable (fun z : V × (Fin (m + 1) → ℝ) =>
      semidiscreteValue μ (fun s j ↦ c z.1 j s + u * g z.1 j s) z.2)
      (ρ.prod (dirichletOne m)) :=
    integrable_parameterized_dirichlet_semidiscreteValue_tilt μ ρ c g hc hci hg hatom G hbound u
  have hVt : Integrable (fun z : V × (Fin (m + 1) → ℝ) =>
      semidiscreteValue μ (fun s j ↦ c z.1 j s + t * g z.1 j s) z.2)
      (ρ.prod (dirichletOne m)) :=
    integrable_parameterized_dirichlet_semidiscreteValue_tilt μ ρ c g hc hci hg hatom G hbound t
  -- Integrability of the probe-cost readout.
  have hfeas : ∀ᵐ z ∂ρ.prod (dirichletOne m),
      IsSemidiscreteAllocation μ z.2 (fun s ↦ a (z, s)) :=
    hopt.mono fun _ hz => hz.1
  have hQ : Integrable (fun z : V × (Fin (m + 1) → ℝ) =>
      semidiscreteAllocationCost μ (fun s j ↦ g z.1 j s) (fun s ↦ a (z, s)))
      (ρ.prod (dirichletOne m)) :=
    integrable_parameterized_dirichlet_allocationCost μ ρ g hg hgi a ha hfeas
  -- Pointwise supergradient inequality, integrated.
  have hpoint : ∀ᵐ z ∂ρ.prod (dirichletOne m),
      semidiscreteValue μ (fun s j ↦ c z.1 j s + u * g z.1 j s) z.2 ≤
        semidiscreteValue μ (fun s j ↦ c z.1 j s + t * g z.1 j s) z.2 +
          (u - t) * semidiscreteAllocationCost μ (fun s j ↦ g z.1 j s)
            (fun s ↦ a (z, s)) := by
    filter_upwards [hopt, hic] with z hz hcz
    exact semidiscreteValue_supergradient_of_tilted_optimal μ
      (fun s j ↦ c z.1 j s) (fun s j ↦ g z.1 j s) (fun s ↦ a (z, s))
      hz.1 hcz (hgs z.1) hz.2 u
  calc
    (∫ z : V × (Fin (m + 1) → ℝ),
        semidiscreteValue μ (fun s j ↦ c z.1 j s + u * g z.1 j s) z.2
          ∂ρ.prod (dirichletOne m))
        ≤ ∫ z : V × (Fin (m + 1) → ℝ),
            (semidiscreteValue μ (fun s j ↦ c z.1 j s + t * g z.1 j s) z.2 +
              (u - t) * semidiscreteAllocationCost μ (fun s j ↦ g z.1 j s)
                (fun s ↦ a (z, s))) ∂ρ.prod (dirichletOne m) :=
          integral_mono_ae hVu (hVt.add (hQ.const_mul (u - t))) hpoint
    _ = (∫ z : V × (Fin (m + 1) → ℝ),
          semidiscreteValue μ (fun s j ↦ c z.1 j s + t * g z.1 j s) z.2
            ∂ρ.prod (dirichletOne m)) +
          (u - t) * ∫ z : V × (Fin (m + 1) → ℝ),
            semidiscreteAllocationCost μ (fun s j ↦ g z.1 j s) (fun s ↦ a (z, s))
              ∂ρ.prod (dirichletOne m) := by
          rw [integral_add hVt (hQ.const_mul (u - t)), integral_const_mul]

end OTSelector.Probability
