import OTSelector.Probability.CavitySemidiscreteOptimizer
import OTSelector.Probability.CavityDirichletOriginal

/-!
# Jointly measurable optimizers with random target parameters

The parameter and actual cavity mass vector are the factor statistic. Conditioning
the complete allocation on this statistic supplies a jointly measurable optimizer
on the exact parameter-times-Dirichlet law. The original cost hypotheses need hold
only almost surely in the parameter; no measurable good-set or optimizer oracle is used.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S V : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [MeasurableSpace V] [StandardBorelSpace V]

/-- The whole actual allocation is jointly measurable in source, random parameters,
and Dirichlet masses, and is the unique full-face optimizer almost surely. -/
theorem exists_jointlyMeasurable_parameterized_dirichlet_optimalAllocation
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ρ : Measure V) [IsProbabilityMeasure ρ]
    (c : V → Fin (m + 1) → S → ℝ)
    (hc : ∀ j, Measurable (fun z : V × S ↦ c z.1 j z.2))
    (hci : ∀ᵐ v ∂ρ, ∀ j, Integrable (c v j) μ)
    (hatom : ∀ᵐ v ∂ρ, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ c v j s - c v l s))) :
    ∃ A : ((V × (Fin (m + 1) → ℝ)) × S) → Fin (m + 1) → ℝ,
      (∀ j, Measurable (fun z ↦ A z j)) ∧
      ∀ᵐ z ∂ρ.prod (dirichletOne m),
        IsOptimalSemidiscreteAllocation μ z.2 (fun s j ↦ c z.1 j s)
          (fun s ↦ A (z, s)) ∧
        ∀ b, IsSemidiscreteAllocation μ z.2 b →
          semidiscreteAllocationCost μ (fun s j ↦ c z.1 j s) (fun s ↦ A (z, s)) =
            semidiscreteAllocationCost μ (fun s j ↦ c z.1 j s) b →
          (fun s ↦ A (z, s)) =ᵐ[μ] b := by
  let : Nonempty S := nonempty_of_isProbabilityMeasure μ
  let : Nonempty V := nonempty_of_isProbabilityMeasure ρ
  let P := ρ.prod (Measure.pi (fun _ : Fin m ↦ μ))
  let retained : V × (Fin m → S) → Fin (m + 1) → Fin (m + 1) → ℝ :=
    fun q ↦ iidCapacityInputCost (c q.1) (fun k w ↦ w k) q.2
  let row : (V × (Fin m → S)) × S → Fin (m + 1) → ℝ :=
    fun z j ↦ c z.1.1 j z.2
  let a : ((V × (Fin m → S)) × S) → Fin (m + 1) → ℝ :=
    fun z ↦ cavityAllocation retained row 0 z.1 z.2
  let f : V × (Fin m → S) → V × (Fin (m + 1) → ℝ) :=
    fun q ↦ (q.1, iidCavityMassVector μ (c q.1) q.2)
  let Good : V × (Fin m → S) → Prop := fun q ↦
    (∀ j, Integrable (c q.1 j) μ) ∧ ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ c q.1 j s - c q.1 l s))
  have hgood : ∀ᵐ q ∂P, Good q :=
    measurePreserving_fst.quasiMeasurePreserving.ae (hci.and hatom)
  have hpres := measurePreserving_parameterizedIidCavityMassVector μ ρ c hc hatom
  have hret (k j : Fin (m + 1)) : Measurable (fun q ↦ retained q k j) := by
    refine Fin.succAboveCases 0 ?_ (fun l ↦ ?_) k
    · simp only [retained, iidCapacityInputCost, Fin.insertNth_apply_same]
      exact measurable_const
    · simpa only [retained, iidCapacityInputCost_retained, Function.comp_def] using
        (hc j).comp (measurable_fst.prodMk ((measurable_pi_apply l).comp measurable_snd))
  have hrow j : Measurable (fun z ↦ row z j) :=
    (hc j).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have ha j : Measurable (fun z ↦ a z j) :=
    measurable_const.indicator (measurableSet_cavityCell retained row hret hrow 0 j)
  have hconst (w : V × (Fin m → S)) (hw : Good w) (v : V × (Fin m → S))
      (hmass : f w = f v) : (fun s ↦ a (w, s)) =ᵐ[μ] fun s ↦ a (v, s) := by
    obtain ⟨b, w⟩ := w
    obtain ⟨d, v⟩ := v
    have hbd : b = d := congrArg Prod.fst hmass
    subst d
    have hp : iidCavityMassVector μ (c b) w = iidCavityMassVector μ (c b) v :=
      congrArg Prod.snd hmass
    apply cavityAllocation_eq_of_same_masses μ
      (iidCapacityInputCost (c b) (fun k w ↦ w k))
      (measurable_iidCavityRetained (c b) (fun j ↦ (hc j).comp measurable_prodMk_left))
      (fun s j ↦ c b j s) (fun j ↦ (hc j).comp measurable_prodMk_left) hw.1 hw.2 0 w v
    intro j
    have hj := congrArg (fun p ↦ ENNReal.ofReal (p j)) hp
    simpa only [ofReal_iidCavityMassVector] using hj
  obtain ⟨A, hA, hrep⟩ := exists_measurable_allocation_of_ae_fiber_constancy P μ f
    hpres.measurable a ha Good hgood hconst
  change ∀ᵐ z ∂P.map f, _ at hrep
  rw [hpres.map_eq] at hrep
  refine ⟨A, hA, ?_⟩
  filter_upwards [hrep] with z hz
  obtain ⟨⟨v, w⟩, hgoodw, hw, heq⟩ := hz
  have hv : v = z.1 := congrArg Prod.fst hw
  subst v
  have hmass : (fun j ↦ (cavityCellMass μ retained row 0 j (z.1, w)).toReal) = z.2 :=
    congrArg Prod.snd hw
  have hno (j l : Fin (m + 1)) (hjl : j ≠ l) :
      μ {s | cavityScore retained row 0 ((z.1, w), s) j =
        cavityScore retained row 0 ((z.1, w), s) l} = 0 := by
    have := hgoodw.2 j l hjl
    exact measure_cavityScore_eq_zero_of_atomless μ retained row hrow 0 j l (z.1, w)
  have hwalloc := isSemidiscreteAllocation_cavityAllocation μ retained row hret hrow
    0 (z.1, w) hno
  have hfeas : IsSemidiscreteAllocation μ z.2 (fun s ↦ a ((z.1, w), s)) := hmass ▸ hwalloc
  have hopt : IsOptimalSemidiscreteAllocation μ z.2 (fun s j ↦ c z.1 j s)
      (fun s ↦ a ((z.1, w), s)) := by
    refine ⟨hfeas, fun b hb ↦ ?_⟩
    exact (cavityAllocation_unique_optimal μ retained row hret hrow 0 (z.1, w)
      hno hgoodw.1 b (hmass.symm ▸ hb)).1
  refine ⟨hopt.congr heq.symm, ?_⟩
  intro b hb hcost
  apply heq.trans
  apply (cavityAllocation_unique_optimal μ retained row hret hrow 0 (z.1, w)
    hno hgoodw.1 b (hmass.symm ▸ hb)).2
  exact (semidiscreteAllocationCost_congr μ _ heq).symm.trans hcost

end OTSelector.Probability
