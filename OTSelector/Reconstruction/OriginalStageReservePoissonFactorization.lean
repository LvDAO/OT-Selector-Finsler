import OTSelector.Reconstruction.OriginalStageReserveFactorization

/-! The literal original reserve cloud splits into count and marks independent of positions. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Probability

/-- The original Poisson count and every original clock mark, with their actual joint law. -/
def originalReserveCountMarkLaw {A : Type*} [MeasurableSpace A] (α : Measure A) [IsProbabilityMeasure α]
    (rate : ℝ≥0) : Measure (ℕ × (ℕ → A)) :=
  (poissonMeasure rate).prod (Measure.infinitePi (fun _ : ℕ ↦ α))

instance originalReserveCountMarkLaw_probability {A : Type*} [MeasurableSpace A] (α : Measure A)
    [IsProbabilityMeasure α] (rate : ℝ≥0) : IsProbabilityMeasure (originalReserveCountMarkLaw α rate) := by
  unfold originalReserveCountMarkLaw
  infer_instance

/-- Split the same original observation into its unchanged count/marks and original positions. -/
def originalReserveCloudSplit {q : ℕ} {A : Type*} (z : MarkedCloudSpace q A) :
    (ℕ × (ℕ → A)) × (ℕ → (Fin q → ℝ)) :=
  ((z.1, fun i ↦ (z.2 i).2), fun i ↦ (z.2 i).1)

/-- Reassemble the very same indexed original reserve observation. -/
def originalReserveCloudJoin {q : ℕ} {A : Type*}
    (z : (ℕ × (ℕ → A)) × (ℕ → (Fin q → ℝ))) : MarkedCloudSpace q A :=
  (z.1.1, fun i ↦ (z.2 i, z.1.2 i))

/-- Splitting and rejoining retains the original count, every index, each mark and each position. -/
theorem originalReserveCloudJoin_split {q : ℕ} {A : Type*} (z : MarkedCloudSpace q A) :
    originalReserveCloudJoin (originalReserveCloudSplit z) = z := by
  rcases z with ⟨n, z⟩
  rfl

/-- The original marked Poisson law, rather than a new sampler, has the exact product
factorization required for selecting original reserve positions by marks and auxiliary indices. -/
theorem map_originalReserveCloudSplit_markedPoissonLaw (q : ℕ)
    {A : Type*} [MeasurableSpace A] (α : Measure A) [IsProbabilityMeasure α] (rate : ℝ≥0) :
    (markedPoissonLaw q A α rate).map originalReserveCloudSplit =
      (originalReserveCountMarkLaw α rate).prod
        (Measure.infinitePi (fun _ : ℕ ↦ cubeMeasure (Fin q) 1)) := by
  let : IsProbabilityMeasure (cubeMeasure (Fin q) 1) := isProbabilityMeasure_cubeMeasure (by norm_num)
  let split : (ℕ → (Fin q → ℝ) × A) → (ℕ → A) × (ℕ → (Fin q → ℝ)) :=
    fun z ↦ (fun i ↦ (z i).2, fun i ↦ (z i).1)
  have hm : Measurable split := by fun_prop
  have hseq : (markedSeqLaw q A α).map split =
      (Measure.infinitePi (fun _ : ℕ ↦ α)).prod
        (Measure.infinitePi (fun _ : ℕ ↦ cubeMeasure (Fin q) 1)) := by
    rw [show split = Prod.swap ∘ (fun z : ℕ → (Fin q → ℝ) × A ↦
        (fun i ↦ (z i).1, fun i ↦ (z i).2)) from rfl,
      ← Measure.map_map measurable_swap (by fun_prop)]
    rw [markedSeqLaw, map_split_original_infinitePairLaw, Measure.prod_swap]
  have hprod : (markedPoissonLaw q A α rate).map (Prod.map id split) =
      (poissonMeasure rate).prod ((Measure.infinitePi (fun _ : ℕ ↦ α)).prod
        (Measure.infinitePi (fun _ : ℕ ↦ cubeMeasure (Fin q) 1))) := by
    rw [markedPoissonLaw, ← Measure.map_prod_map _ _ measurable_id hm, Measure.map_id, hseq]
  rw [show originalReserveCloudSplit = MeasurableEquiv.prodAssoc.symm ∘ Prod.map id split from rfl,
    ← Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable (measurable_id.prodMap hm), hprod]
  have hassoc := Measure.prodAssoc_prod (μ := poissonMeasure rate)
    (ν := Measure.infinitePi (fun _ : ℕ ↦ α))
    (τ := Measure.infinitePi (fun _ : ℕ ↦ cubeMeasure (Fin q) 1))
  conv_lhs => rw [← hassoc]
  rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable MeasurableEquiv.prodAssoc.measurable]
  simp only [MeasurableEquiv.symm_comp_self, Measure.map_id, originalReserveCountMarkLaw]

end OTSelector.Probability
