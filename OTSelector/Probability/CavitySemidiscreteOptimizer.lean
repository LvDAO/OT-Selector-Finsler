import OTSelector.Probability.CavitySemidiscreteMeasurable

/-!
# A jointly measurable actual semidiscrete optimizer

The whole cavity allocation factors through its mass vector. Its jointly measurable
factor is an actual optimizer for almost every Dirichlet vector, simultaneously for all
paired tests. This supplies allocation coefficients for a common random environment.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S : Type*} [MeasurableSpace S]

/-- Feasibility depends only on the almost everywhere allocation class. -/
theorem IsSemidiscreteAllocation.congr {μ : Measure S} {p : Fin (m + 1) → ℝ}
    {a b : S → Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ p a)
    (hab : a =ᵐ[μ] b) : IsSemidiscreteAllocation μ p b := by
  refine ⟨fun j ↦ (ha.integrable j).congr (hab.mono fun _ h ↦ congrFun h j), ?_, ?_, ?_⟩
  · filter_upwards [ha.nonneg, hab] with s hs heq
    simpa only [← heq] using hs
  · filter_upwards [ha.sum_one, hab] with s hs heq
    simpa only [← heq] using hs
  · intro j
    exact (integral_congr_ae (hab.mono fun _ h ↦ congrFun h j)).symm.trans (ha.mass j)

/-- All paired objectives depend only on the allocation class. -/
theorem semidiscreteAllocationCost_congr (μ : Measure S)
    (c : S → Fin (m + 1) → ℝ) {a b : S → Fin (m + 1) → ℝ} (hab : a =ᵐ[μ] b) :
    semidiscreteAllocationCost μ c a = semidiscreteAllocationCost μ c b := by
  apply integral_congr_ae
  filter_upwards [hab] with s hs
  simp only [hs]

/-- Actual full-face optimality passes to any almost everywhere equal coefficient version. -/
theorem IsOptimalSemidiscreteAllocation.congr {μ : Measure S} {p : Fin (m + 1) → ℝ}
    {c a b : S → Fin (m + 1) → ℝ} (ha : IsOptimalSemidiscreteAllocation μ p c a)
    (hab : a =ᵐ[μ] b) : IsOptimalSemidiscreteAllocation μ p c b := by
  refine ⟨ha.1.congr hab, fun d hd ↦ ?_⟩
  rw [← semidiscreteAllocationCost_congr μ c hab]
  exact ha.2 d hd

/-- Joint measurability of the actual optimum's full allocation, obtained from cavity cells
and disintegration of their original mass statistic. -/
theorem exists_jointlyMeasurable_dirichlet_optimalAllocation [StandardBorelSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c : Fin (m + 1) → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hci : ∀ j, Integrable (c j) μ)
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c j s - c l s))) :
    ∃ A : ((Fin (m + 1) → ℝ) × S) → Fin (m + 1) → ℝ,
      (∀ j, Measurable (fun z ↦ A z j)) ∧
      ∀ᵐ p ∂dirichletOne m,
        IsOptimalSemidiscreteAllocation μ p (fun s j ↦ c j s) (fun s ↦ A (p, s)) ∧
        ∀ b, IsSemidiscreteAllocation μ p b →
          semidiscreteAllocationCost μ (fun s j ↦ c j s) (fun s ↦ A (p, s)) =
            semidiscreteAllocationCost μ (fun s j ↦ c j s) b →
          (fun s ↦ A (p, s)) =ᵐ[μ] b := by
  let : Nonempty S := nonempty_of_isProbabilityMeasure μ
  let retained := iidCapacityInputCost c (fun (k : Fin m) (w : Fin m → S) ↦ w k)
  let row : (Fin m → S) × S → Fin (m + 1) → ℝ := fun z j ↦ c j z.2
  let a : ((Fin m → S) × S) → Fin (m + 1) → ℝ :=
    fun z ↦ cavityAllocation retained row 0 z.1 z.2
  have hret := measurable_iidCavityRetained c hc
  have hrow j : Measurable (fun z ↦ row z j) := (hc j).comp measurable_snd
  have ha j : Measurable (fun z ↦ a z j) :=
    measurable_const.indicator (measurableSet_cavityCell retained row hret hrow 0 j)
  have hconst (w v : Fin m → S) (hmass : iidCavityMassVector μ c w = iidCavityMassVector μ c v) :
      (fun s ↦ a (w, s)) =ᵐ[μ] fun s ↦ a (v, s) := by
    apply cavityAllocation_eq_of_same_masses μ retained hret (fun s j ↦ c j s)
      hc hci hatom 0 w v
    intro j
    have hj := congrArg (fun p ↦ ENNReal.ofReal (p j)) hmass
    simpa only [ofReal_iidCavityMassVector] using hj
  obtain ⟨A, hA, hrep⟩ := exists_measurable_allocation_of_fiber_constancy
    (Measure.pi (fun _ : Fin m ↦ μ)) μ (iidCavityMassVector μ c)
    (measurable_iidCavityMassVector μ c hc) a ha hconst
  rw [map_iidCavityMassVector_eq_dirichletOne μ c hc hatom] at hrep
  refine ⟨A, hA, ?_⟩
  filter_upwards [hrep] with p hp
  obtain ⟨w, hw, heq⟩ := hp
  have hno (j l : Fin (m + 1)) (hjl : j ≠ l) :
      μ {s | cavityScore retained row 0 (w, s) j = cavityScore retained row 0 (w, s) l} = 0 := by
    have := hatom j l hjl
    exact measure_cavityScore_eq_zero_of_atomless μ retained row hrow 0 j l w
  have hwalloc := isSemidiscreteAllocation_cavityAllocation μ retained row hret hrow 0 w hno
  have hmass : (fun j ↦ (cavityCellMass μ retained row 0 j w).toReal) = p := hw
  have hfeas : IsSemidiscreteAllocation μ p (fun s ↦ a (w, s)) := hmass ▸ hwalloc
  have hopt : IsOptimalSemidiscreteAllocation μ p (fun s j ↦ c j s) (fun s ↦ a (w, s)) := by
    refine ⟨hfeas, fun b hb ↦ ?_⟩
    exact (cavityAllocation_unique_optimal μ retained row hret hrow 0 w hno hci b
      (hmass.symm ▸ hb)).1
  refine ⟨hopt.congr heq.symm, ?_⟩
  intro b hb hcost
  apply heq.trans
  apply (cavityAllocation_unique_optimal μ retained row hret hrow 0 w hno hci b
    (hmass.symm ▸ hb)).2
  exact (semidiscreteAllocationCost_congr μ _ heq).symm.trans hcost

end OTSelector.Probability
