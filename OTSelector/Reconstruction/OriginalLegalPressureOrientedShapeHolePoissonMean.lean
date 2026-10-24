import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeHolePoissonPrefix
import OTSelector.Probability.PoissonMinPrefixMoments

/-! Genuine conditioning of two independent Poisson counts and original iid sequences. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

/-- The two actual Poisson counts are independent of the unchanged two iid
sequences. The external physical cost scale is contained only in `cost`. -/
def originalShapeHolePoissonLaw {q : ℕ} (space : Measure (DyadicUnitCube q))
    (α β : Measure ℝ) (a : ℝ≥0) :=
  ((poissonMeasure a).prod (poissonMeasure a)).prod (originalShapeHoleSequenceLaw space α β)

/-- The original unequal-prefix optimum at its two actual Poisson counts. -/
def originalShapeHolePoissonValue {q : ℕ}
    (cost : (DyadicUnitCube q × ℝ) → (DyadicUnitCube q × ℝ) → ℝ)
    (z : (ℕ × ℕ) × ((ℕ → DyadicUnitCube q × ℝ) × (ℕ → DyadicUnitCube q × ℝ))) :=
  originalShapeHolePrefixValue cost z.1.1 z.1.2 z.2

/-- Actual independent Poissonization of the natural fixed-sample rate.
Min-prefix conditioning, original legal deletion stability and all count
moments are internal; no Poisson cost estimate is supplied. -/
theorem originalShapeHolePoisson_integral_le
    {q : ℕ} (hq : 4 < q) (space : Measure (DyadicUnitCube q)) [IsProbabilityMeasure space]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (π : Measure (ℝ × ℝ)) (hπ : Vlasov.IsCoupling π α β)
    {I : Set ℝ} {gap diameter : ℝ} (bins : FiniteScalarBins I gap) (hIm : MeasurableSet I) (hgap : 0 < gap)
    (hsep : ConditionalClockSupportBounds α β gap diameter)
    (hI : ∀ᵐ p ∂π, p.1 ∈ I ∧ p.2 ∈ I) (horder : ∀ᵐ p ∂π, p.1 ≤ p.2)
    (cost : (DyadicUnitCube q × ℝ) → (DyadicUnitCube q × ℝ) → ℝ)
    (hc : Measurable (Function.uncurry cost)) {C : ℝ} (hC : 0 ≤ C)
    (hcn : ∀ x y, 0 ≤ cost x y)
    (hquadratic : ∀ x y, cost x y ≤ C*‖dyadicCubePoint x.1-dyadicCubePoint y.1‖^2) (a : ℝ≥0) :
    Integrable (originalShapeHolePoissonValue cost) (originalShapeHolePoissonLaw space α β a) ∧
      (∫ z, originalShapeHolePoissonValue cost z ∂originalShapeHolePoissonLaw space α β a) ≤
        C*dyadicMatchingConstant q*((bins.count+1 : ℕ) : ℝ)^(2/(q : ℝ))*(a : ℝ)^(1-2/(q : ℝ)) +
        (C+2*((bins.count : ℝ)+1)*C)*Real.sqrt (2*(a : ℝ)*(bins.count+1)) +
        Real.sqrt (2*(a : ℝ))*(2*((bins.count : ℝ)+1)*C) := by
  let Count := (poissonMeasure a).prod (poissonMeasure a)
  let Seq := originalShapeHoleSequenceLaw space α β
  have : IsProbabilityMeasure Seq := by unfold Seq originalShapeHoleSequenceLaw; infer_instance
  have hb (x y : DyadicUnitCube q × ℝ) : |cost x y| ≤ C := by
    rw [abs_of_nonneg (hcn x y)]
    have hd := dyadicCube_dist_le_one x.1 y.1
    have hs : ‖dyadicCubePoint x.1-dyadicCubePoint y.1‖^2 ≤ 1 := by
      nlinarith [norm_nonneg (dyadicCubePoint x.1-dyadicCubePoint y.1)]
    exact (hquadratic x y).trans ((mul_le_mul_of_nonneg_left hs hC).trans_eq (mul_one C))
  have hm : Measurable (originalShapeHolePoissonValue cost) :=
    measurable_from_prod_countable_right fun z : ℕ × ℕ ↦ measurable_originalShapeHolePrefixValue hc z.1 z.2
  have hN : Integrable (fun z : (ℕ × ℕ) × ((ℕ → DyadicUnitCube q × ℝ) × (ℕ → DyadicUnitCube q × ℝ)) ↦
      (z.1.1 : ℝ)*C) (originalShapeHolePoissonLaw space α β a) :=
    (((integrable_id_poissonMeasure a).comp_fst (poissonMeasure a)).comp_fst Seq).mul_const C
  have hvalI : Integrable (originalShapeHolePoissonValue cost) (originalShapeHolePoissonLaw space α β a) := by
    apply hN.mono' hm.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_eq_abs]
    exact (PartialMatching.abs_legalMaximumValue_le_min _ _ hC (fun i j ↦ hb _ _)).trans
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (min_le_left z.1.1 z.1.2)) hC)
  have hM := originalShapeHolePoisson_count_moments hq a (bins.count+1)
  simp only [Nat.cast_add,Nat.cast_one] at hM
  let A := C*dyadicMatchingConstant q*((bins.count+1 : ℕ) : ℝ)^(2/(q : ℝ))
  let B := C+2*((bins.count : ℝ)+1)*C
  let D := 2*((bins.count : ℝ)+1)*C
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg hC (dyadicMatchingConstant_pos hq).le) (Real.rpow_nonneg (by positivity) _)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let bound := fun z : ℕ × ℕ ↦ A*((min z.1 z.2 : ℕ) : ℝ)^(1-2/(q : ℝ))+
    B*Real.sqrt (2*((min z.1 z.2 : ℕ) : ℝ)*(bins.count+1))+|(z.1 : ℝ)-z.2| * D
  have hAI : Integrable (fun z : ℕ × ℕ ↦ A*((min z.1 z.2 : ℕ) : ℝ)^(1-2/(q : ℝ))) Count := hM.1.const_mul A
  have hBI : Integrable (fun z : ℕ × ℕ ↦ B*Real.sqrt (2*((min z.1 z.2 : ℕ) : ℝ)*(bins.count+1))) Count := hM.2.2.1.const_mul B
  have hDI : Integrable (fun z : ℕ × ℕ ↦ |(z.1 : ℝ)-z.2| * D) Count := hM.2.2.2.2.1.mul_const D
  have hbI : Integrable bound Count := by
    dsimp only [bound]
    apply Integrable.add
    · exact hAI.add hBI
    · exact hDI
  have hle : (∫ z, originalShapeHolePoissonValue cost z ∂originalShapeHolePoissonLaw space α β a) ≤
      ∫ z, bound z ∂Count := by
    change (∫ z, originalShapeHolePoissonValue cost z ∂Count.prod Seq) ≤ _
    rw [integral_prod _ hvalI]
    apply integral_mono_ae hvalI.integral_prod_left hbI
    filter_upwards with z
    exact originalShapeHolePrefix_integral_le hq space α β π hπ bins hIm hgap hsep hI horder cost hc hC hcn hquadratic z.1 z.2
  have hbound : (∫ z, bound z ∂Count) ≤ A*(a : ℝ)^(1-2/(q : ℝ))+
      B*Real.sqrt (2*(a : ℝ)*(bins.count+1))+Real.sqrt (2*(a : ℝ))*D := by
    have he := integral_add (hAI.add hBI) hDI
    have he' := integral_add hAI hBI
    simp only [Pi.add_apply] at he he'
    change (∫ z, A*((min z.1 z.2 : ℕ) : ℝ)^(1-2/(q : ℝ))+
      B*Real.sqrt (2*((min z.1 z.2 : ℕ) : ℝ)*(bins.count+1))+|(z.1 : ℝ)-z.2| * D ∂Count) ≤ _
    rw [he,he']
    simp only [integral_const_mul,integral_mul_const]
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hM.2.1 hA)
      (mul_le_mul_of_nonneg_left hM.2.2.2.1 hB)) (mul_le_mul_of_nonneg_right hM.2.2.2.2.2 hD)
  exact ⟨hvalI,hle.trans hbound⟩

end OTSelector.Reconstruction
