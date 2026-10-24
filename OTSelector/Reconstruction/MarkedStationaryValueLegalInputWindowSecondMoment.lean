import OTSelector.Reconstruction.MarkedStationaryValueLegalInputWindowMoment
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputWindowMeasureLaw
import OTSelector.Probability.PoissonSignedIntegralMoments

/-! True second moments of the literal original finite Poisson input windows. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal CompactlySupported BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- The actual Poisson count has a finite true square moment. -/
theorem integrable_sq_originalPoisson_count (r : ℝ≥0) :
    Integrable (fun n : ℕ ↦ (n : ℝ) ^ 2) (poissonMeasure r) := by
  exact integrable_sq_id_poissonMeasure r

/-- Encoding the original counted iid prefix preserves its actual count square. -/
theorem integrable_sq_originalPoisson_blockSize
    {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0) :
    Integrable (fun b : BlockData X ↦ (b.1 : ℝ) ^ 2)
      (blockDataLaw ν (fun n ↦ poissonMeasure r {n})) := by
  let enc : ℕ × (ℕ → X) → BlockData X := fun z ↦ ⟨z.1, fun j ↦ z.2 j⟩
  have henc : Measurable enc := by
    apply measurable_from_prod_countable_right
    intro n
    exact (measurable_sigma_mk n).comp
      (measurable_pi_lambda _ (fun j ↦ measurable_pi_apply (j : ℕ)))
  rw [blockDataLaw_eq_map_cloud]
  have hm : Measurable (fun b : BlockData X ↦ (b.1 : ℝ) ^ 2) :=
    (measurable_from_nat.comp measurable_blockData_fst).pow_const 2
  apply (integrable_map_measure hm.aestronglyMeasurable henc.aemeasurable).mpr
  exact (integrable_sq_originalPoisson_count r).comp_fst _

/-- A bounded test on the original finite enumeration has a true square moment. -/
theorem integrable_sq_originalPoisson_blockTest
    {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    (f : X → ℝ) (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, |f x| ≤ B) :
    Integrable (fun b ↦ legalInputBlockTest f b ^ 2)
      (blockDataLaw ν (fun n ↦ poissonMeasure r {n})) := by
  apply ((integrable_sq_originalPoisson_blockSize ν r).const_mul (B ^ 2)).mono'
    ((measurable_legalInputBlockTest hf).pow_const 2).aestronglyMeasurable
  filter_upwards with b
  change |legalInputBlockTest f b ^ 2| ≤ B ^ 2 * (b.1 : ℝ) ^ 2
  rw [abs_of_nonneg (sq_nonneg _)]
  have hsum : |legalInputBlockTest f b| ≤ (b.1 : ℝ) * B := by
    calc
      _ ≤ ∑ i : Fin b.1, |f (b.2 i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin b.1, B := Finset.sum_le_sum (fun _ _ ↦ hbound _)
      _ = _ := by simp
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hB)).mpr hsum
  simpa only [sq_abs, mul_pow, mul_comm] using hs

/-- Every actual compact colored input test in the original finite physical
Poisson window has a true second moment. -/
theorem integrable_sq_originalPoisson_windowTest (q : ℕ)
    {U : Set (Fin q → ℝ)} (hUfin : volume U ≠ ∞) (hUpos : volume U ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (F : C_c(LegalColoredInputPoint q, ℝ)) :
    Integrable (fun b ↦ LocalFiniteMeasure.testIntegral (legalInputTwoBlockLocal q b) F ^ 2)
      (legalInputPoissonWindowLaw q U α β) := by
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
      IsProbabilityMeasure (blockDataLaw (ν.prod γ)
        (fun n ↦ poissonMeasure (volume U).toNNReal {n})) := by
    rw [blockDataLaw_eq_map_cloud]
    apply Measure.isProbabilityMeasure_map
    apply Measurable.aemeasurable
    apply measurable_from_prod_countable_right
    intro n
    exact (measurable_sigma_mk n).comp
      (measurable_pi_lambda _ (fun j ↦ measurable_pi_apply (j : ℕ)))
  have : IsProbabilityMeasure P := hprob α
  have : IsProbabilityMeasure Q := hprob β
  have hm (c : Fin 2) : Measurable (fun x : LegalMarkedPhysicalPoint q ↦ F (x, c)) :=
    F.continuous.measurable.comp (measurable_id.prodMk measurable_const)
  have hb (c : Fin 2) (x : LegalMarkedPhysicalPoint q) :
      |F (x, c)| ≤ ‖F.toBoundedContinuousFunction‖ := by
    change ‖F.toBoundedContinuousFunction (x, c)‖ ≤ _
    exact F.toBoundedContinuousFunction.norm_coe_le_norm _
  have hs := integrable_sq_originalPoisson_blockTest (ν.prod α) (volume U).toNNReal
    (fun x ↦ F (x, 0)) (hm 0) (norm_nonneg _) (hb 0)
  have ht := integrable_sq_originalPoisson_blockTest (ν.prod β) (volume U).toNNReal
    (fun x ↦ F (x, 1)) (hm 1) (norm_nonneg _) (hb 1)
  have hDom := ((hs.comp_fst Q).add (ht.comp_snd P)).const_mul 2
  have hread (b) : LocalFiniteMeasure.testIntegral (legalInputTwoBlockLocal q b) F =
      legalInputBlockTest (fun x ↦ F (x, 0)) b.1 +
        legalInputBlockTest (fun x ↦ F (x, 1)) b.2 := by
    exact integral_legalInputTwoBlockMeasure q b F
  have hmeas : Measurable (fun b ↦ LocalFiniteMeasure.testIntegral
      (legalInputTwoBlockLocal q b) F ^ 2) :=
    ((LocalFiniteMeasure.continuous_testIntegral F).measurable.comp
      (measurable_legalInputTwoBlockLocal q)).pow_const 2
  apply hDom.mono' hmeas.aestronglyMeasurable
  filter_upwards with b
  change |LocalFiniteMeasure.testIntegral (legalInputTwoBlockLocal q b) F ^ 2| ≤
    2 * (legalInputBlockTest (fun x ↦ F (x, 0)) b.1 ^ 2 +
      legalInputBlockTest (fun x ↦ F (x, 1)) b.2 ^ 2)
  rw [abs_of_nonneg (sq_nonneg _), hread]
  nlinarith [sq_nonneg (legalInputBlockTest (fun x ↦ F (x, 0)) b.1 -
    legalInputBlockTest (fun x ↦ F (x, 1)) b.2)]

end OTSelector.Reconstruction
