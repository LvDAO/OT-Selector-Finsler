import OTSelector.Reconstruction.MarkedStationaryValueLegalInputLaplace
import OTSelector.Probability.PoissonPrefixMoments
import OTSelector.Probability.MarkedBlockLaw
import OTSelector.Probability.FiniteMeasureConditioning

/-! Exact original physical first moments of the prescribed finite Poisson window. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- The literal counted finite prefix has its original Poisson first moment. -/
theorem lintegral_legalInputBlockTest_ofReal
    {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    (f : X → ℝ) (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    (∫⁻ b, ENNReal.ofReal (legalInputBlockTest f b)
      ∂blockDataLaw ν (fun n ↦ poissonMeasure r {n})) =
      (r : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (f x) ∂ν := by
  let enc : ℕ × (ℕ → X) → BlockData X := fun z ↦ ⟨z.1, fun j ↦ z.2 j⟩
  have henc : Measurable enc := by
    apply measurable_from_prod_countable_right
    intro n
    exact (measurable_sigma_mk n).comp
      (measurable_pi_lambda _ (fun j ↦ measurable_pi_apply (j : ℕ)))
  rw [blockDataLaw_eq_map_cloud, lintegral_map
    ((measurable_legalInputBlockTest hf).ennreal_ofReal) henc]
  change (∫⁻ z, ENNReal.ofReal (poissonPrefixSum f z)
    ∂(poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν))) = _
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_poissonPrefixSum ν r hf hB)
    (.of_forall (fun z ↦ Finset.sum_nonneg (fun i _ ↦ hfn _))), integral_poissonPrefixSum ν r hf hB]
  have hfi : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable B
    (.of_forall (fun x ↦ by simpa only [Real.norm_eq_abs] using hB x))
  rw [ENNReal.ofReal_mul r.coe_nonneg,
    ofReal_integral_eq_lintegral_ofReal hfi (.of_forall hfn)]
  simp

/-- Undoing original finite Haar normalization preserves its exact physical
intensity on the same prescribed input window. -/
theorem physicalIntensity_smul_normalized_window (q : ℕ)
    {U : Set (Fin q → ℝ)} (hUfin : volume U ≠ ∞) (hUpos : volume U ≠ 0)
    (α : Measure ℝ) [IsProbabilityMeasure α] :
    volume U • ((normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)).prod α) =
      ((volume : Measure (Fin q → ℝ)).restrict U).prod α := by
  rw [normalizedFiniteLaw_restrict_eq_cond _ _ hUfin, ProbabilityTheory.cond,
    Measure.prod_smul_left, ← smul_assoc, smul_eq_mul,
    ENNReal.mul_inv_cancel hUpos hUfin, one_smul]

/-- Original full source and target window test means have their exact
physical Haar-clock intensity, before any matching or weak limit. -/
theorem lintegral_legalInputPoissonWindowLaw_sourceTest (q : ℕ)
    {U : Set (Fin q → ℝ)} (_hU : MeasurableSet U)
    (hUfin : volume U ≠ ∞) (hUpos : volume U ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (f : LegalMarkedPhysicalPoint q → ℝ) (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    (∫⁻ b, ENNReal.ofReal (legalInputBlockTest f b.1) ∂legalInputPoissonWindowLaw q U α β) =
      ∫⁻ x, ENNReal.ofReal (f x) ∂((volume : Measure (Fin q → ℝ)).restrict U).prod α := by
  have : IsFiniteMeasure ((volume : Measure (Fin q → ℝ)).restrict U) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hUfin.lt_top⟩
  have hmass : 0 < ((volume : Measure (Fin q → ℝ)).restrict U).real univ := by
    rw [Measure.real, Measure.restrict_apply_univ]
    exact ENNReal.toReal_pos hUpos hUfin
  let ν := normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)
  have : IsProbabilityMeasure ν := normalizedFiniteLaw_probability _ hmass
  let P := blockDataLaw (ν.prod α) (fun n ↦ poissonMeasure (volume U).toNNReal {n})
  let Q := blockDataLaw (ν.prod β) (fun n ↦ poissonMeasure (volume U).toNNReal {n})
  have hprob (γ : Measure ℝ) [IsProbabilityMeasure γ] :
      IsProbabilityMeasure (blockDataLaw (ν.prod γ) (fun n ↦ poissonMeasure (volume U).toNNReal {n})) := by
    rw [blockDataLaw_eq_map_cloud]
    have hm : Measurable (fun z : ℕ × (ℕ → LegalMarkedPhysicalPoint q) ↦
        (⟨z.1, fun j : Fin z.1 ↦ z.2 j⟩ : BlockData (LegalMarkedPhysicalPoint q))) := by
      apply measurable_from_prod_countable_right
      intro n
      exact (measurable_sigma_mk n).comp
        (measurable_pi_lambda (fun (y : ℕ → LegalMarkedPhysicalPoint q) (j : Fin n) ↦ y j)
          (fun j ↦ measurable_pi_apply (j : ℕ)))
    exact Measure.isProbabilityMeasure_map hm.aemeasurable
  have : IsProbabilityMeasure P := hprob α
  have : IsProbabilityMeasure Q := hprob β
  change (∫⁻ b, ENNReal.ofReal (legalInputBlockTest f b.1) ∂P.prod Q) = _
  have hread : Measurable (fun b : BlockData (LegalMarkedPhysicalPoint q) ×
      BlockData (LegalMarkedPhysicalPoint q) ↦ ENNReal.ofReal (legalInputBlockTest f b.1)) := by
    exact ((measurable_legalInputBlockTest hf).ennreal_ofReal).comp
      (measurable_fst : Measurable (Prod.fst : BlockData (LegalMarkedPhysicalPoint q) ×
        BlockData (LegalMarkedPhysicalPoint q) → BlockData (LegalMarkedPhysicalPoint q)))
  rw [lintegral_prod _ hread.aemeasurable]
  simp only [lintegral_const, measure_univ, mul_one]
  rw [lintegral_legalInputBlockTest_ofReal (ν.prod α) (volume U).toNNReal f hf hfn hB,
    ENNReal.coe_toNNReal hUfin]
  calc
    _ = ∫⁻ x, ENNReal.ofReal (f x) ∂(volume U • ν.prod α) := by
      rw [lintegral_smul_measure]
      rfl
    _ = _ := by rw [physicalIntensity_smul_normalized_window q hUfin hUpos α]

/-- Original full source and target window test means have their exact
physical Haar-clock intensity, before any matching or weak limit. -/
theorem lintegral_legalInputPoissonWindowLaw_targetTest (q : ℕ)
    {U : Set (Fin q → ℝ)} (_hU : MeasurableSet U)
    (hUfin : volume U ≠ ∞) (hUpos : volume U ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (f : LegalMarkedPhysicalPoint q → ℝ) (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    (∫⁻ b, ENNReal.ofReal (legalInputBlockTest f b.2) ∂legalInputPoissonWindowLaw q U α β) =
      ∫⁻ x, ENNReal.ofReal (f x) ∂((volume : Measure (Fin q → ℝ)).restrict U).prod β := by
  have : IsFiniteMeasure ((volume : Measure (Fin q → ℝ)).restrict U) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hUfin.lt_top⟩
  have hmass : 0 < ((volume : Measure (Fin q → ℝ)).restrict U).real univ := by
    rw [Measure.real, Measure.restrict_apply_univ]
    exact ENNReal.toReal_pos hUpos hUfin
  let ν := normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)
  have : IsProbabilityMeasure ν := normalizedFiniteLaw_probability _ hmass
  let P := blockDataLaw (ν.prod α) (fun n ↦ poissonMeasure (volume U).toNNReal {n})
  let Q := blockDataLaw (ν.prod β) (fun n ↦ poissonMeasure (volume U).toNNReal {n})
  have hprob (γ : Measure ℝ) [IsProbabilityMeasure γ] :
      IsProbabilityMeasure (blockDataLaw (ν.prod γ) (fun n ↦ poissonMeasure (volume U).toNNReal {n})) := by
    rw [blockDataLaw_eq_map_cloud]
    have hm : Measurable (fun z : ℕ × (ℕ → LegalMarkedPhysicalPoint q) ↦
        (⟨z.1, fun j : Fin z.1 ↦ z.2 j⟩ : BlockData (LegalMarkedPhysicalPoint q))) := by
      apply measurable_from_prod_countable_right
      intro n
      exact (measurable_sigma_mk n).comp
        (measurable_pi_lambda (fun (y : ℕ → LegalMarkedPhysicalPoint q) (j : Fin n) ↦ y j)
          (fun j ↦ measurable_pi_apply (j : ℕ)))
    exact Measure.isProbabilityMeasure_map hm.aemeasurable
  have : IsProbabilityMeasure P := hprob α
  have : IsProbabilityMeasure Q := hprob β
  change (∫⁻ b, ENNReal.ofReal (legalInputBlockTest f b.2) ∂P.prod Q) = _
  have hread : Measurable (fun b : BlockData (LegalMarkedPhysicalPoint q) ×
      BlockData (LegalMarkedPhysicalPoint q) ↦ ENNReal.ofReal (legalInputBlockTest f b.2)) := by
    exact ((measurable_legalInputBlockTest hf).ennreal_ofReal).comp
      (measurable_snd : Measurable (Prod.snd : BlockData (LegalMarkedPhysicalPoint q) ×
        BlockData (LegalMarkedPhysicalPoint q) → BlockData (LegalMarkedPhysicalPoint q)))
  rw [lintegral_prod_symm _ hread.aemeasurable]
  simp only [lintegral_const, measure_univ, mul_one]
  rw [lintegral_legalInputBlockTest_ofReal (ν.prod β) (volume U).toNNReal f hf hfn hB,
    ENNReal.coe_toNNReal hUfin]
  calc
    _ = ∫⁻ x, ENNReal.ofReal (f x) ∂(volume U • ν.prod β) := by
      rw [lintegral_smul_measure]
      rfl
    _ = _ := by rw [physicalIntensity_smul_normalized_window q hUfin hUpos β]


end OTSelector.Reconstruction
