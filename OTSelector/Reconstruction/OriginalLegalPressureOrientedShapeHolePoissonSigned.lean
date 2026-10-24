import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeHolePoissonMean
import OTSelector.Reconstruction.MarkedStationaryValueLegalRegularity

/-! A bounded original marked probe pays the actual Poisson source mean only. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- The actual unequal-count Poisson legal optimum pays a bounded probe by its
true source mean; no probe term is charged to the square-root kinetic error. -/
theorem originalShapeHolePoisson_signed_integral_le
    {q : ℕ} (hq : 4 < q) (space : Measure (DyadicUnitCube q)) [IsProbabilityMeasure space]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (π : Measure (ℝ × ℝ)) (hπ : Vlasov.IsCoupling π α β)
    {I : Set ℝ} {gap diameter : ℝ} (bins : FiniteScalarBins I gap) (hIm : MeasurableSet I) (hgap : 0 < gap)
    (hsep : ConditionalClockSupportBounds α β gap diameter)
    (hI : ∀ᵐ p ∂π, p.1 ∈ I ∧ p.2 ∈ I) (horder : ∀ᵐ p ∂π, p.1 ≤ p.2)
    (cost probe : (DyadicUnitCube q × ℝ) → (DyadicUnitCube q × ℝ) → ℝ)
    (hc : Measurable (Function.uncurry cost)) (hg : Measurable (Function.uncurry probe))
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G) (t : ℝ)
    (hcn : ∀ x y, 0 ≤ cost x y)
    (hquadratic : ∀ x y, cost x y ≤ C*‖dyadicCubePoint x.1-dyadicCubePoint y.1‖^2)
    (hgb : ∀ x y, |probe x y| ≤ G) (a : ℝ≥0) :
    Integrable (originalShapeHolePoissonValue (fun x y ↦ cost x y+t*probe x y))
      (originalShapeHolePoissonLaw space α β a) ∧
    (∫ z, originalShapeHolePoissonValue (fun x y ↦ cost x y+t*probe x y) z
      ∂originalShapeHolePoissonLaw space α β a) ≤
      C*dyadicMatchingConstant q*((bins.count+1 : ℕ) : ℝ)^(2/(q : ℝ))*(a : ℝ)^(1-2/(q : ℝ)) +
      (C+2*((bins.count : ℝ)+1)*C)*Real.sqrt (2*(a : ℝ)*(bins.count+1)) +
      Real.sqrt (2*(a : ℝ))*(2*((bins.count : ℝ)+1)*C)+(a : ℝ)*(|t| * G) := by
  have hbase := originalShapeHolePoisson_integral_le hq space α β π hπ bins hIm hgap hsep hI horder
    cost hc hC hcn hquadratic a
  let P := originalShapeHolePoissonLaw space α β a
  let tilted := fun x y ↦ cost x y+t*probe x y
  have htilt : Measurable (uncurry tilted) := hc.add (hg.const_mul t)
  have hbound (x y : DyadicUnitCube q × ℝ) : |tilted x y| ≤ C+|t| * G := by
    have hd := dyadicCube_dist_le_one x.1 y.1
    have hs : ‖dyadicCubePoint x.1-dyadicCubePoint y.1‖^2 ≤ 1 := by
      nlinarith [norm_nonneg (dyadicCubePoint x.1-dyadicCubePoint y.1)]
    have hb : cost x y ≤ C := (hquadratic x y).trans ((mul_le_mul_of_nonneg_left hs hC).trans_eq (mul_one C))
    exact (abs_add_le _ _).trans (add_le_add (by simpa only [abs_of_nonneg (hcn x y)] using hb)
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hgb x y) (abs_nonneg t)))
  have hm : Measurable (originalShapeHolePoissonValue tilted) :=
    measurable_from_prod_countable_right fun z : ℕ × ℕ ↦ measurable_originalShapeHolePrefixValue htilt z.1 z.2
  have hSeq : IsProbabilityMeasure (originalShapeHoleSequenceLaw space α β) := by
    unfold originalShapeHoleSequenceLaw
    infer_instance
  have hN : Integrable (fun z : (ℕ × ℕ) × ((ℕ → DyadicUnitCube q × ℝ) × (ℕ → DyadicUnitCube q × ℝ)) ↦
      (z.1.1 : ℝ)) P :=
    ((integrable_id_poissonMeasure a).comp_fst (poissonMeasure a)).comp_fst _
  have htI : Integrable (originalShapeHolePoissonValue tilted) P := by
    apply (hN.mul_const (C+|t| * G)).mono' hm.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_eq_abs]
    exact (PartialMatching.abs_legalMaximumValue_le_min _ _ (by positivity : 0 ≤ C+|t| * G)
      (fun i j ↦ hbound _ _)).trans (mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (min_le_left z.1.1 z.1.2)) (by positivity))
  have hpoint (z : (ℕ × ℕ) × ((ℕ → DyadicUnitCube q × ℝ) × (ℕ → DyadicUnitCube q × ℝ))) :
      originalShapeHolePoissonValue tilted z ≤ originalShapeHolePoissonValue cost z+(z.1.1 : ℝ)*(|t| * G) := by
    let allowed := scalarClockLegalGraph (fun i : Fin z.1.1 ↦ (z.2.1 i).2) (fun j : Fin z.1.2 ↦ (z.2.2 j).2)
    have hcard : (PartialMatching.legalMaximumCard allowed : ℝ) ≤ z.1.1 :=
      Nat.cast_le.mpr ((PartialMatching.legalMaximumCard_le_min allowed).trans (min_le_left _ _))
    apply (PartialMatching.legalMaximumValue_le_add_of_allowed allowed
      (fun i j ↦ tilted (z.2.1 i) (z.2.2 j)) (fun i j ↦ cost (z.2.1 i) (z.2.2 j)) (B := |t| * G) ?_).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right hcard (mul_nonneg (abs_nonneg t) hG)))
    intro i j _
    have hb : t*probe (z.2.1 i) (z.2.2 j) ≤ |t| * G :=
      (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hgb _ _) (abs_nonneg t))
    dsimp only [tilted]
    linarith only [hb]
  have hmean : (∫ z, (z.1.1 : ℝ) ∂P) = (a : ℝ) := by
    change (∫ z, (z.1.1 : ℝ) ∂((poissonMeasure a).prod (poissonMeasure a)).prod
      (originalShapeHoleSequenceLaw space α β)) = _
    rw [integral_prod _ hN]
    simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
    simpa only [integral_fun_fst,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] using
      integral_id_poissonMeasure a
  refine ⟨htI,?_⟩
  have hh := integral_mono_ae htI (hbase.1.add (hN.mul_const (|t| * G))) (Filter.Eventually.of_forall hpoint)
  simp only [Pi.add_apply] at hh
  rw [integral_add hbase.1 (hN.mul_const (|t| * G)),integral_mul_const,hmean] at hh
  exact hh.trans (add_le_add hbase.2 le_rfl)

end OTSelector.Reconstruction
