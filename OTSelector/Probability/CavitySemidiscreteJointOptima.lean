import OTSelector.Probability.CavitySemidiscretePressureComparison
import OTSelector.Probability.CavitySemidiscreteParameterizedOptimizer

/-!
# Measurable opposite-tilt optimizers on a common random environment

A deterministic sequence of good tilts works for the original random parameters.
The complete allocations at zero and both signs are jointly measurable on the same
parameter, Dirichlet mass, and source space. Their averaged base-cost excess has the
explicit bound needed before local geometric replacement.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S V : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [MeasurableSpace V] [StandardBorelSpace V]

/-- One measurable zero-tilt optimizer and two measurable sequences of opposite-tilt
optimizers share the actual environment and masses. Their average is `t n * G` near-optimal. -/
theorem exists_jointlyMeasurable_opposite_semidiscrete_optima_sequence
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ρ : Measure V) [IsProbabilityMeasure ρ]
    (c g : V → Fin (m + 1) → S → ℝ)
    (hc : ∀ j, Measurable (fun z : V × S ↦ c z.1 j z.2))
    (hci : ∀ᵐ v ∂ρ, ∀ j, Integrable (c v j) μ)
    (hg : ∀ j, Measurable (fun z : V × S ↦ g z.1 j z.2))
    (hatom : ∀ᵐ v ∂ρ, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ c v j s - c v l s)))
    (G : ℝ≥0) (hbound : ∀ v s j, |g v j s| ≤ G) :
    ∃ t : ℕ → ℝ, ∃ A₀ : ((V × (Fin (m + 1) → ℝ)) × S) → Fin (m + 1) → ℝ,
    ∃ Aplus Amin : ℕ → ((V × (Fin (m + 1) → ℝ)) × S) → Fin (m + 1) → ℝ,
      StrictAnti t ∧ (∀ n, 0 < t n) ∧ Tendsto t atTop (nhds 0) ∧
      (∀ j, Measurable (fun z ↦ A₀ z j)) ∧
      (∀ n j, Measurable (fun z ↦ Aplus n z j)) ∧
      (∀ n j, Measurable (fun z ↦ Amin n z j)) ∧
      ∀ᵐ z ∂ρ.prod (dirichletOne m),
        IsOptimalSemidiscreteAllocation μ z.2 (fun s j ↦ c z.1 j s)
          (fun s ↦ A₀ (z, s)) ∧ ∀ n,
        IsOptimalSemidiscreteAllocation μ z.2
          (fun s j ↦ c z.1 j s + t n * g z.1 j s) (fun s ↦ Aplus n (z, s)) ∧
        IsOptimalSemidiscreteAllocation μ z.2
          (fun s j ↦ c z.1 j s + (-t n) * g z.1 j s) (fun s ↦ Amin n (z, s)) ∧
        0 ≤ semidiscreteAllocationCost μ (fun s j ↦ c z.1 j s)
          (fun s j ↦ (Aplus n (z, s) j + Amin n (z, s) j) / 2) -
            semidiscreteAllocationCost μ (fun s j ↦ c z.1 j s) (fun s ↦ A₀ (z, s)) ∧
        semidiscreteAllocationCost μ (fun s j ↦ c z.1 j s)
          (fun s j ↦ (Aplus n (z, s) j + Amin n (z, s) j) / 2) -
            semidiscreteAllocationCost μ (fun s j ↦ c z.1 j s) (fun s ↦ A₀ (z, s)) ≤ t n * G := by
  let B : Set ℝ := {u | ¬∀ᵐ v ∂ρ, ∀ j l, j ≠ l → NullSingletonClass
    (μ.map (fun s ↦ (c v j s + u * g v j s) - (c v l s + u * g v l s)))}
  have hB : B.Countable := countable_bad_parameterized_cavity_tilts μ ρ
    (fun j v s ↦ c v j s) (fun j v s ↦ g v j s) hc hg hatom
  let N := B ∪ Neg.neg '' B
  have hN : N.Countable := hB.union (hB.image Neg.neg)
  obtain ⟨t, ht, hmem, hlim⟩ := (hN.dense_compl ℝ).exists_seq_strictAnti_tendsto (0 : ℝ)
  have hp (n : ℕ) : t n ∉ B := fun h ↦ (hmem n).2 (Or.inl h)
  have hm (n : ℕ) : -t n ∉ B := fun h ↦ (hmem n).2 (Or.inr ⟨-t n, h, neg_neg _⟩)
  have hgi (v : V) (j : Fin (m + 1)) : Integrable (g v j) μ :=
    (integrable_const (G : ℝ)).mono'
      ((hg j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun s ↦ by simpa only [Real.norm_eq_abs] using hbound v s j)
  have halloc (u : ℝ) (hu : u ∉ B) :
      ∃ A : ((V × (Fin (m + 1) → ℝ)) × S) → Fin (m + 1) → ℝ,
        (∀ j, Measurable (fun z ↦ A z j)) ∧
        ∀ᵐ z ∂ρ.prod (dirichletOne m),
          IsOptimalSemidiscreteAllocation μ z.2
            (fun s j ↦ c z.1 j s + u * g z.1 j s) (fun s ↦ A (z, s)) := by
    have hat : ∀ᵐ v ∂ρ, ∀ j l, j ≠ l → NullSingletonClass
        (μ.map (fun s ↦ (c v j s + u * g v j s) - (c v l s + u * g v l s))) :=
      not_not.mp hu
    obtain ⟨A, hA, hopt⟩ := exists_jointlyMeasurable_parameterized_dirichlet_optimalAllocation
      μ ρ (fun v j s ↦ c v j s + u * g v j s)
      (fun j ↦ (hc j).add ((hg j).const_mul u))
      (hci.mono fun v hv j ↦ (hv j).add ((hgi v j).const_mul u)) hat
    exact ⟨A, hA, hopt.mono fun _ h ↦ h.1⟩
  choose Aplus hAplus hplus using fun n ↦ halloc (t n) (hp n)
  choose Amin hAmin hminus using fun n ↦ halloc (-t n) (hm n)
  obtain ⟨A₀, hA₀, hzero⟩ :=
    exists_jointlyMeasurable_parameterized_dirichlet_optimalAllocation μ ρ c hc hci hatom
  refine ⟨t, A₀, Aplus, Amin, ht, fun n ↦ (hmem n).1, hlim, hA₀, hAplus, hAmin, ?_⟩
  have hic : ∀ᵐ z ∂ρ.prod (dirichletOne m), ∀ j, Integrable (c z.1 j) μ :=
    measurePreserving_fst.quasiMeasurePreserving.ae hci
  filter_upwards [hzero, ae_all_iff.mpr hplus, ae_all_iff.mpr hminus, hic]
    with z hz hzp hzm hcz
  refine ⟨hz.1, fun n ↦ ?_⟩
  have hcmp := semidiscrete_opposite_tilt_excess μ z.2
    (fun s j ↦ c z.1 j s) (fun s j ↦ g z.1 j s)
    (fun s ↦ A₀ (z, s)) (fun s ↦ Aplus n (z, s)) (fun s ↦ Amin n (z, s))
    hz.1.1 (hzp n).1 (hzm n).1 hcz (hgi z.1) G
    (Eventually.of_forall fun s j ↦ hbound z.1 s j)
    (t n) (hmem n).1.le hz.1.2 (hzp n).2 (hzm n).2
  exact ⟨hzp n, hzm n, hcmp.1, hcmp.2.1.trans hcmp.2.2.1⟩

end OTSelector.Probability
