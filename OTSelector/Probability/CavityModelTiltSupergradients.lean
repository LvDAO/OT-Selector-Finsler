import OTSelector.Probability.CavitySemidiscretePressureComparison
import OTSelector.Probability.CavitySemidiscreteJointOptima
import OTSelector.Probability.CavityExpectedTiltSupergradient

/-!
# Opposite-tilt optima and supergradients on a prescribed tilt sequence

The cavity construction produces jointly measurable optima at both signs of any
prescribed tilt sequence, provided the tilted pairwise cost differences are
atomless on the source law at each tilt.  Feeding these optima into
`integral_semidiscreteValue_supergradient_of_tilted_optimal` gives the two
expected probe costs as supergradients of the expected pressure.

The only remaining stochastic input to differentiability is then the asymptotic
equality of those two probe costs.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S V : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [MeasurableSpace V] [StandardBorelSpace V]

/-- **Prescribed tilts: jointly measurable opposite-tilt optima.**  If the
tilted cost differences are atomless at every `± t n`, the cavity construction
supplies jointly measurable optima at the zero and both signed tilts, together
with the quantitative excess bound. -/
theorem exists_jointlyMeasurable_opposite_semidiscrete_optima_for_tilts
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ρ : Measure V) [IsProbabilityMeasure ρ]
    (c g : V → Fin (m + 1) → S → ℝ)
    (hc : ∀ j, Measurable (fun z : V × S ↦ c z.1 j z.2))
    (hci : ∀ᵐ v ∂ρ, ∀ j, Integrable (c v j) μ)
    (hg : ∀ j, Measurable (fun z : V × S ↦ g z.1 j z.2))
    (hatom : ∀ᵐ v ∂ρ, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ c v j s - c v l s)))
    (G : ℝ≥0) (hbound : ∀ v s j, |g v j s| ≤ G)
    (t : ℕ → ℝ) (htpos : ∀ n, 0 < t n)
    (htatom : ∀ n, ∀ᵐ v ∂ρ, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦
        (c v j s + t n * g v j s) - (c v l s + t n * g v l s))))
    (htatomneg : ∀ n, ∀ᵐ v ∂ρ, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦
        (c v j s + (-t n) * g v j s) - (c v l s + (-t n) * g v l s)))) :
    ∃ A₀ : ((V × (Fin (m + 1) → ℝ)) × S) → Fin (m + 1) → ℝ,
    ∃ Aplus Amin : ℕ → ((V × (Fin (m + 1) → ℝ)) × S) → Fin (m + 1) → ℝ,
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
  have hgi (v : V) (j : Fin (m + 1)) : Integrable (g v j) μ :=
    (integrable_const (G : ℝ)).mono'
      ((hg j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using hbound v s j)
  have halloc (u : ℝ) (hu : ∀ᵐ v ∂ρ, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦
        (c v j s + u * g v j s) - (c v l s + u * g v l s)))) :
      ∃ A : ((V × (Fin (m + 1) → ℝ)) × S) → Fin (m + 1) → ℝ,
        (∀ j, Measurable (fun z ↦ A z j)) ∧
        ∀ᵐ z ∂ρ.prod (dirichletOne m),
          IsOptimalSemidiscreteAllocation μ z.2
            (fun s j ↦ c z.1 j s + u * g z.1 j s) (fun s ↦ A (z, s)) := by
    obtain ⟨A, hA, hopt⟩ := exists_jointlyMeasurable_parameterized_dirichlet_optimalAllocation
      μ ρ (fun v j s ↦ c v j s + u * g v j s)
      (fun j => (hc j).add ((hg j).const_mul u))
      (hci.mono fun v hv j => (hv j).add ((hgi v j).const_mul u)) hu
    exact ⟨A, hA, hopt.mono fun _ h => h.1⟩
  choose Aplus hAplus hplus using fun n => halloc (t n) (htatom n)
  choose Amin hAmin hminus using fun n => halloc (-t n) (htatomneg n)
  obtain ⟨A₀, hA₀, hzero⟩ :=
    exists_jointlyMeasurable_parameterized_dirichlet_optimalAllocation μ ρ c hc hci hatom
  refine ⟨A₀, Aplus, Amin, hA₀, hAplus, hAmin, ?_⟩
  have hic : ∀ᵐ z ∂ρ.prod (dirichletOne m), ∀ j, Integrable (c z.1 j) μ :=
    measurePreserving_fst.quasiMeasurePreserving.ae hci
  filter_upwards [hzero, ae_all_iff.mpr hplus, ae_all_iff.mpr hminus, hic]
    with z hz hzp hzm hcz
  refine ⟨hz.1, fun n => ?_⟩
  have hcmp := semidiscrete_opposite_tilt_excess μ z.2
    (fun s j ↦ c z.1 j s) (fun s j ↦ g z.1 j s)
    (fun s ↦ A₀ (z, s)) (fun s ↦ Aplus n (z, s)) (fun s ↦ Amin n (z, s))
    hz.1.1 (hzp n).1 (hzm n).1 hcz (hgi z.1) G
    (Eventually.of_forall fun s j ↦ hbound z.1 s j)
    (t n) (htpos n).le hz.1.2 (hzp n).2 (hzm n).2
  exact ⟨hzp n, hzm n, hcmp.1, hcmp.2.1.trans hcmp.2.2.1⟩

/-- **Expected probe costs are opposite-tilt supergradients.**  Under the
tilt-specific atomlessness hypotheses, the expected probe costs of the cavity
optima bracket the expected pressure at both signs of every tilt. -/
theorem exists_opposite_tilt_supergradient_pair
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ρ : Measure V) [IsProbabilityMeasure ρ]
    (c g : V → Fin (m + 1) → S → ℝ)
    (hc : ∀ j, Measurable (fun z : V × S ↦ c z.1 j z.2))
    (hcij : ∀ j, Integrable (fun z : V × S ↦ c z.1 j z.2) (ρ.prod μ))
    (hg : ∀ j, Measurable (fun z : V × S ↦ g z.1 j z.2))
    (hatom : ∀ᵐ v ∂ρ, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ c v j s - c v l s)))
    (G : ℝ≥0) (hbound : ∀ v s j, |g v j s| ≤ G)
    (t : ℕ → ℝ) (htpos : ∀ n, 0 < t n)
    (htatom : ∀ n, ∀ᵐ v ∂ρ, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦
        (c v j s + t n * g v j s) - (c v l s + t n * g v l s))))
    (htatomneg : ∀ n, ∀ᵐ v ∂ρ, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦
        (c v j s + (-t n) * g v j s) - (c v l s + (-t n) * g v l s)))) :
    let P : ℝ → ℝ := fun u => ∫ z : V × (Fin (m + 1) → ℝ),
      semidiscreteValue μ (fun s j ↦ c z.1 j s + u * g z.1 j s) z.2
        ∂ρ.prod (dirichletOne m)
    ∃ qpos qneg : ℕ → ℝ,
      (∀ n, ∀ s, P s ≤ P (t n) + qpos n * (s - t n)) ∧
      (∀ n, ∀ s, P s ≤ P (-(t n)) + qneg n * (s + t n)) := by
  dsimp only
  have hci : ∀ᵐ v ∂ρ, ∀ j, Integrable (c v j) μ :=
    ae_all_iff.mpr fun j => (hcij j).prod_right_ae
  obtain ⟨A₀, Aplus, Amin, hA₀, hAplus, hAmin, hopt⟩ :=
    exists_jointlyMeasurable_opposite_semidiscrete_optima_for_tilts
      μ ρ c g hc hci hg hatom G hbound t htpos htatom htatomneg
  refine ⟨(fun n => ∫ z : V × (Fin (m + 1) → ℝ),
      semidiscreteAllocationCost μ (fun s j ↦ g z.1 j s)
        (fun s ↦ Aplus n (z, s)) ∂ρ.prod (dirichletOne m)),
    (fun n => ∫ z : V × (Fin (m + 1) → ℝ),
      semidiscreteAllocationCost μ (fun s j ↦ g z.1 j s)
        (fun s ↦ Amin n (z, s)) ∂ρ.prod (dirichletOne m)), ?_, ?_⟩
  · intro n s
    have hoptplus : ∀ᵐ z ∂ρ.prod (dirichletOne m),
        IsOptimalSemidiscreteAllocation μ z.2
          (fun s j ↦ c z.1 j s + t n * g z.1 j s) (fun s ↦ Aplus n (z, s)) :=
      hopt.mono fun z hz => hz.2 n |>.1
    have h := integral_semidiscreteValue_supergradient_of_tilted_optimal
      μ ρ c g hc hcij hg hatom G hbound (Aplus n) (hAplus n) hoptplus
    simpa only [mul_comm] using h s
  · intro n s
    have hoptminus : ∀ᵐ z ∂ρ.prod (dirichletOne m),
        IsOptimalSemidiscreteAllocation μ z.2
          (fun s j ↦ c z.1 j s + (-t n) * g z.1 j s) (fun s ↦ Amin n (z, s)) :=
      hopt.mono fun z hz => hz.2 n |>.2.1
    have h := integral_semidiscreteValue_supergradient_of_tilted_optimal
      μ ρ c g hc hcij hg hatom G hbound (Amin n) (hAmin n) hoptminus
    simpa only [sub_neg_eq_add, mul_comm] using h s

set_option maxHeartbeats 800000 in
/-- **Bipartite supergradient pair on a prescribed good tilt sequence.**  This is
the iid-target form used by the pressure: pairwise atomlessness of the tilted
cost differences at each tilt supplies the expected probe costs as
opposite-tilt supergradients of the finite pressure. -/
theorem exists_bipartite_opposite_tilt_supergradients
    {T : Type*} [MeasurableSpace T] [StandardBorelSpace T]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (c g : S → T → ℝ) (hc : Measurable (Function.uncurry c))
    (hci : Integrable (Function.uncurry c) (μ.prod ν))
    (hg : Measurable (Function.uncurry g))
    (hatom : ∀ y z, y ≠ z → NullSingletonClass (μ.map (fun x ↦ c x y - c x z)))
    (G : ℝ≥0) (hbound : ∀ x y, |g x y| ≤ G)
    (t : ℕ → ℝ) (htpos : ∀ n, 0 < t n)
    (htgood : ∀ n, ∀ᵐ y ∂Measure.pi (fun _ : Fin (m + 1) ↦ ν), ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦
        (c s (y j) + t n * g s (y j)) - (c s (y l) + t n * g s (y l)))))
    (htgoodneg : ∀ n, ∀ᵐ y ∂Measure.pi (fun _ : Fin (m + 1) ↦ ν), ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦
        (c s (y j) + (-t n) * g s (y j)) - (c s (y l) + (-t n) * g s (y l))))) :
    let P : ℝ → ℝ := fun u => ∫ z : (Fin (m + 1) → T) × (Fin (m + 1) → ℝ),
      semidiscreteValue μ (fun s j ↦ c s (z.1 j) + u * g s (z.1 j)) z.2
        ∂(Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod (dirichletOne m)
    ∃ qpos qneg : ℕ → ℝ,
      (∀ n, ∀ s, P s ≤ P (t n) + qpos n * (s - t n)) ∧
      (∀ n, ∀ s, P s ≤ P (-(t n)) + qneg n * (s + t n)) := by
  let ρ : Measure (Fin (m + 1) → T) := Measure.pi (fun _ : Fin (m + 1) ↦ ν)
  let cpar : (Fin (m + 1) → T) → Fin (m + 1) → S → ℝ := fun y j s ↦ c s (y j)
  let gpar : (Fin (m + 1) → T) → Fin (m + 1) → S → ℝ := fun y j s ↦ g s (y j)
  have hcpar (j : Fin (m + 1)) : Measurable (fun z : (Fin (m + 1) → T) × S ↦
      cpar z.1 j z.2) :=
    hc.comp (measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst))
  have hgpar (j : Fin (m + 1)) : Measurable (fun z : (Fin (m + 1) → T) × S ↦
      gpar z.1 j z.2) :=
    hg.comp (measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst))
  have hcij : ∀ j : Fin (m + 1),
      Integrable (fun z : (Fin (m + 1) → T) × S ↦ cpar z.1 j z.2) (ρ.prod μ) := by
    intro j
    have hpair : MeasurePreserving (fun z : (Fin (m + 1) → T) × S ↦ (z.2, z.1 j))
        (ρ.prod μ) (μ.prod ν) :=
      Measure.measurePreserving_swap.comp
        ((measurePreserving_eval (fun _ : Fin (m + 1) ↦ ν) j).prod
          (MeasurePreserving.id μ))
    exact hpair.integrable_comp_of_integrable hci
  have hatompar : ∀ᵐ y ∂ρ, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ cpar y j s - cpar y l s)) := by
    filter_upwards [ae_injective_pi_of_nullSingletonClass (ι := Fin (m + 1)) ν] with y hy
    exact fun j l hjl ↦ hatom (y j) (y l) (hy.ne hjl)
  have hboundpar : ∀ y s j, |gpar y j s| ≤ (G : ℝ) := fun y s j ↦ hbound s (y j)
  have htgood' : ∀ n, ∀ᵐ y ∂ρ, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦
        (cpar y j s + t n * gpar y j s) - (cpar y l s + t n * gpar y l s))) := by
    intro n
    filter_upwards [htgood n] with y hy j l hjl
    have heq : (fun s ↦ (cpar y j s + t n * gpar y j s) - (cpar y l s + t n * gpar y l s)) =
        (fun s ↦ (c s (y j) + t n * g s (y j)) - (c s (y l) + t n * g s (y l))) := by
      funext s
      simp only [cpar, gpar]
    rw [heq]
    exact hy j l hjl
  have htgoodneg' : ∀ n, ∀ᵐ y ∂ρ, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦
        (cpar y j s + (-t n) * gpar y j s) - (cpar y l s + (-t n) * gpar y l s))) := by
    intro n
    filter_upwards [htgoodneg n] with y hy j l hjl
    have heq : (fun s ↦ (cpar y j s + (-t n) * gpar y j s) - (cpar y l s + (-t n) * gpar y l s)) =
        (fun s ↦ (c s (y j) + (-t n) * g s (y j)) - (c s (y l) + (-t n) * g s (y l))) := by
      funext s
      simp only [cpar, gpar]
    rw [heq]
    exact hy j l hjl
  simpa only [cpar, gpar, ρ] using
    (exists_opposite_tilt_supergradient_pair (m := m) (V := Fin (m + 1) → T)
      μ ρ cpar gpar hcpar hcij hgpar hatompar
      G hboundpar t htpos htgood' htgoodneg')

end OTSelector.Probability
