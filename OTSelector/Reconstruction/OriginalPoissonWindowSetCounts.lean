import OTSelector.Probability.PoissonBlockSetCounts
import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonLaplaceFormula
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputWindowMoment

/-! Exact original source and target set-count laws in physical Poisson windows. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The literal thinning rate is exactly the original physical intensity
of the fixed point set inside the original window. -/
theorem originalPoissonWindow_setCount_rate_eq (q : ℕ)
    {U : Set (Fin q → ℝ)} (hUfin : volume U ≠ ∞) (hUpos : volume U ≠ 0)
    (α : Measure ℝ) [IsProbabilityMeasure α] (S : Set (LegalMarkedPhysicalPoint q)) :
    (volume U).toNNReal * restrictionWeight
      ((normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)).prod α) S =
      ((((volume : Measure (Fin q → ℝ)).restrict U).prod α) S).toNNReal := by
  have : IsFiniteMeasure ((volume : Measure (Fin q → ℝ)).restrict U) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hUfin.lt_top⟩
  have hr : 0 < (volume U).toReal := ENNReal.toReal_pos hUpos hUfin
  apply NNReal.eq
  change (volume U).toReal *
    (((normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)).prod α) S).toReal = _
  rw [normalizedFiniteLaw, Measure.prod_smul_left, Measure.smul_apply]
  simp only [ENNReal.toReal_smul, Measure.real, Measure.restrict_apply_univ, NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (inv_nonneg.mpr hr.le)]
  rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  rfl

/-- The original finite physical-window source count in any fixed measurable
point restriction is Poisson with its literal original thinning intensity. -/
theorem hasLaw_originalPoissonWindow_sourceSetCount (q : ℕ)
    {U : Set (Fin q → ℝ)} (hUfin : volume U ≠ ∞) (hUpos : volume U ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {S : Set (LegalMarkedPhysicalPoint q)} (hS : MeasurableSet S) :
    HasLaw (fun b ↦ blockSetCount S b.1)
      (poissonMeasure ((volume U).toNNReal * restrictionWeight
        ((normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)).prod α) S))
      (legalInputPoissonWindowLaw q U α β) := by
  have : IsFiniteMeasure ((volume : Measure (Fin q → ℝ)).restrict U) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hUfin.lt_top⟩
  have hmass : 0 < ((volume : Measure (Fin q → ℝ)).restrict U).real univ := by
    rw [Measure.real, Measure.restrict_apply_univ]
    exact ENNReal.toReal_pos hUpos hUfin
  let ν := normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)
  have : IsProbabilityMeasure ν := normalizedFiniteLaw_probability _ hmass
  let P := blockDataLaw (ν.prod α) (fun n ↦ poissonMeasure (volume U).toNNReal {n})
  let R := blockDataLaw (ν.prod β) (fun n ↦ poissonMeasure (volume U).toNNReal {n})
  have : IsProbabilityMeasure P := isProbabilityMeasure_originalPoissonBlockDataLaw _ _
  have : IsProbabilityMeasure R := isProbabilityMeasure_originalPoissonBlockDataLaw _ _
  have hproj : HasLaw (Prod.fst : BlockData (LegalMarkedPhysicalPoint q) ×
      BlockData (LegalMarkedPhysicalPoint q) → BlockData (LegalMarkedPhysicalPoint q)) P (P.prod R) :=
    ⟨measurable_fst.aemeasurable, by simp only [Measure.map_fst_prod, measure_univ, one_smul]⟩
  exact (hasLaw_blockSetCount_poisson (ν.prod α) (volume U).toNNReal hS).fun_comp hproj

/-- The corresponding original target count law, before selecting any edge
or any random phase curve. -/
theorem hasLaw_originalPoissonWindow_targetSetCount (q : ℕ)
    {U : Set (Fin q → ℝ)} (hUfin : volume U ≠ ∞) (hUpos : volume U ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {S : Set (LegalMarkedPhysicalPoint q)} (hS : MeasurableSet S) :
    HasLaw (fun b ↦ blockSetCount S b.2)
      (poissonMeasure ((volume U).toNNReal * restrictionWeight
        ((normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)).prod β) S))
      (legalInputPoissonWindowLaw q U α β) := by
  have : IsFiniteMeasure ((volume : Measure (Fin q → ℝ)).restrict U) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hUfin.lt_top⟩
  have hmass : 0 < ((volume : Measure (Fin q → ℝ)).restrict U).real univ := by
    rw [Measure.real, Measure.restrict_apply_univ]
    exact ENNReal.toReal_pos hUpos hUfin
  let ν := normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)
  have : IsProbabilityMeasure ν := normalizedFiniteLaw_probability _ hmass
  let P := blockDataLaw (ν.prod α) (fun n ↦ poissonMeasure (volume U).toNNReal {n})
  let R := blockDataLaw (ν.prod β) (fun n ↦ poissonMeasure (volume U).toNNReal {n})
  have : IsProbabilityMeasure P := isProbabilityMeasure_originalPoissonBlockDataLaw _ _
  have : IsProbabilityMeasure R := isProbabilityMeasure_originalPoissonBlockDataLaw _ _
  have hproj : HasLaw (Prod.snd : BlockData (LegalMarkedPhysicalPoint q) ×
      BlockData (LegalMarkedPhysicalPoint q) → BlockData (LegalMarkedPhysicalPoint q)) R (P.prod R) :=
    ⟨measurable_snd.aemeasurable, by simp only [Measure.map_snd_prod, measure_univ, one_smul]⟩
  exact (hasLaw_blockSetCount_poisson (ν.prod β) (volume U).toNNReal hS).fun_comp hproj

/-- The source set-count rate is the unnormalized original physical intensity. -/
theorem hasLaw_originalPoissonWindow_sourceSetCount_physical (q : ℕ)
    {U : Set (Fin q → ℝ)} (hUfin : volume U ≠ ∞) (hUpos : volume U ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {S : Set (LegalMarkedPhysicalPoint q)} (hS : MeasurableSet S) :
    HasLaw (fun b ↦ blockSetCount S b.1)
      (poissonMeasure (((((volume : Measure (Fin q → ℝ)).restrict U).prod α) S).toNNReal))
      (legalInputPoissonWindowLaw q U α β) := by
  have h := hasLaw_originalPoissonWindow_sourceSetCount q hUfin hUpos α β hS
  rw [originalPoissonWindow_setCount_rate_eq q hUfin hUpos α S] at h
  exact h

/-- The target set-count rate is likewise its unchanged physical intensity. -/
theorem hasLaw_originalPoissonWindow_targetSetCount_physical (q : ℕ)
    {U : Set (Fin q → ℝ)} (hUfin : volume U ≠ ∞) (hUpos : volume U ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {S : Set (LegalMarkedPhysicalPoint q)} (hS : MeasurableSet S) :
    HasLaw (fun b ↦ blockSetCount S b.2)
      (poissonMeasure (((((volume : Measure (Fin q → ℝ)).restrict U).prod β) S).toNNReal))
      (legalInputPoissonWindowLaw q U α β) := by
  have h := hasLaw_originalPoissonWindow_targetSetCount q hUfin hUpos α β hS
  rw [originalPoissonWindow_setCount_rate_eq q hUfin hUpos β S] at h
  exact h

end OTSelector.Reconstruction
