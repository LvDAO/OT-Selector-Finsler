import OTSelector.Probability.CavitySemidiscreteDisintegration

/-!
# Equality with the full physical semidiscrete coupling primal

A measurable embedding of the target labels preserves the entire coupling objective set.
For a distinct finite target cloud this identifies the allocation infimum with the infimum
over all couplings to the actual weighted target atoms, including every fractional optimum.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {S T J : Type*} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace J]

/-- Replacing target labels by a measurable embedding preserves all feasible paired costs. -/
theorem coupling_objectives_map_target [Nonempty J]
    (μ : Measure S) (ν : Measure J) (Y : J → T) (hY : MeasurableEmbedding Y)
    (c : S → T → ℝ) (hc : Measurable (Function.uncurry c)) :
    ((fun γ : Measure (S × T) ↦ ∫ z, c z.1 z.2 ∂γ) ''
      {γ | Vlasov.IsCoupling γ μ (ν.map Y)}) =
    ((fun γ : Measure (S × J) ↦ ∫ z, c z.1 (Y z.2) ∂γ) ''
      {γ | Vlasov.IsCoupling γ μ ν}) := by
  ext r
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    let L : S × T → S × J := Prod.map id hY.invFun
    have hL : Measurable L := measurable_id.prodMap hY.measurable_invFun
    have htarget : (ν.map Y).map hY.invFun = ν := by
      rw [Measure.map_map hY.measurable_invFun hY.measurable]
      have heq : hY.invFun ∘ Y = id := funext hY.leftInverse_invFun
      rw [heq, Measure.map_id]
    have hπ : Vlasov.IsCoupling (γ.map L) μ ν := by
      simpa only [L, Measure.map_id, htarget] using
        hγ.map id hY.invFun measurable_id hY.measurable_invFun
    refine ⟨γ.map L, hπ, ?_⟩
    have hm : Measurable (fun z : S × J ↦ c z.1 (Y z.2)) :=
      hc.comp (measurable_fst.prodMk (hY.measurable.comp measurable_snd))
    change (∫ z, c z.1 (Y z.2) ∂γ.map L) = ∫ z, c z.1 z.2 ∂γ
    rw [integral_map hL.aemeasurable hm.aestronglyMeasurable]
    have hrange : ∀ᵐ z ∂γ, z.2 ∈ range Y := by
      have h := ae_map_mem_range Y hY.measurableSet_range ν
      rw [← hγ.2] at h
      exact ae_of_ae_map measurable_snd.aemeasurable h
    apply integral_congr_ae
    filter_upwards [hrange] with z hz
    obtain ⟨j, hj⟩ := hz
    change c z.1 (Y (hY.invFun z.2)) = c z.1 z.2
    rw [← hj, hY.leftInverse_invFun j]
  · rintro ⟨γ, hγ, rfl⟩
    let R : S × J → S × T := Prod.map id Y
    have hR : Measurable R := measurable_id.prodMap hY.measurable
    refine ⟨γ.map R, ?_, ?_⟩
    · change Vlasov.IsCoupling (γ.map R) μ (ν.map Y)
      simpa only [R, Measure.map_id] using hγ.map id Y measurable_id hY.measurable
    · exact integral_map hR.aemeasurable hc.aestronglyMeasurable

variable {m : ℕ}

/-- The physical semidiscrete primal ranges over every measure coupling, not a selected plan. -/
def fullSemidiscreteValue (μ : Measure S) (Y : Fin (m + 1) → T)
    (c : S → T → ℝ) (p : Fin (m + 1) → ℝ) : ℝ :=
  sInf ((fun γ : Measure (S × T) ↦ ∫ z, c z.1 z.2 ∂γ) ''
    {γ | Vlasov.IsCoupling γ μ ((semidiscreteLabelMeasure p).map Y)})

/-- The allocation objective set equals the full label-coupling objective set. -/
theorem semidiscrete_coupling_objectives_eq_allocation_objectives
    (μ : Measure S) [IsProbabilityMeasure μ]
    (p : Fin (m + 1) → ℝ) (hp : ∀ j, 0 ≤ p j)
    (c : S → Fin (m + 1) → ℝ) (hcm : Measurable (Function.uncurry c))
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ) :
    ((fun γ : Measure (S × Fin (m + 1)) ↦ ∫ z, c z.1 z.2 ∂γ) ''
      {γ | Vlasov.IsCoupling γ μ (semidiscreteLabelMeasure p)}) =
      semidiscreteAllocationCost μ c '' {a | IsSemidiscreteAllocation μ p a} := by
  ext r
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨a, ha, hcost⟩ := exists_semidiscreteAllocation_of_isCoupling μ p hp γ hγ
    exact ⟨a, ha, (hcost c hcm hc).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨semidiscreteAllocationMeasure μ a, ha.isCoupling,
      ha.integral_allocationMeasure c hcm hc⟩

/-- The full physical coupling value is exactly the actual allocation value for distinct targets. -/
theorem fullSemidiscreteValue_eq_semidiscreteValue [MeasurableSingletonClass T]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (Y : Fin (m + 1) → T) (hY : Function.Injective Y)
    (c : S → T → ℝ) (hcm : Measurable (Function.uncurry c))
    (hc : ∀ j, Integrable (fun s ↦ c s (Y j)) μ)
    (p : Fin (m + 1) → ℝ) (hp : ∀ j, 0 ≤ p j) :
    fullSemidiscreteValue μ Y c p = semidiscreteValue μ (fun s j ↦ c s (Y j)) p := by
  have hemb : MeasurableEmbedding Y :=
    ⟨hY, measurable_of_countable Y, fun s _ ↦ (s.toFinite.image Y).measurableSet⟩
  unfold fullSemidiscreteValue semidiscreteValue
  rw [coupling_objectives_map_target μ (semidiscreteLabelMeasure p) Y hemb c hcm]
  congr 1
  exact semidiscrete_coupling_objectives_eq_allocation_objectives μ p hp
    (fun s j ↦ c s (Y j))
    (hcm.comp (measurable_fst.prodMk (hemb.measurable.comp measurable_snd))) hc

end OTSelector.Probability
