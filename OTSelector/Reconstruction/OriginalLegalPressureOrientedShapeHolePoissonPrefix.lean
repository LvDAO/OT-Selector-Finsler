import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeHoleIID
import OTSelector.Reconstruction.MarkedStationaryValueLegalSubcloudStability
import OTSelector.Probability.MarkedBlockLaw

/-! Actual unequal iid prefixes reduce to the same original equal-prefix legal problem. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Two unchanged independent original infinite point sequences. -/
def originalShapeHoleSequenceLaw {q : ℕ} (space : Measure (DyadicUnitCube q)) (α β : Measure ℝ) :
    Measure ((ℕ → DyadicUnitCube q × ℝ) × (ℕ → DyadicUnitCube q × ℝ)) :=
  (Measure.infinitePi (fun _ : ℕ ↦ space.prod α)).prod
    (Measure.infinitePi (fun _ : ℕ ↦ space.prod β))

/-- The literal original scalar-legal optimum of two actual unequal prefixes. -/
def originalShapeHolePrefixValue {q : ℕ}
    (cost : (DyadicUnitCube q × ℝ) → (DyadicUnitCube q × ℝ) → ℝ) (m n : ℕ)
    (sample : (ℕ → DyadicUnitCube q × ℝ) × (ℕ → DyadicUnitCube q × ℝ)) : ℝ :=
  PartialMatching.legalMaximumValue
    (scalarClockLegalGraph (fun i : Fin m ↦ (sample.1 i).2) (fun j : Fin n ↦ (sample.2 j).2))
    (fun i j ↦ cost (sample.1 i) (sample.2 j))

/-- Actual unequal-prefix scalar values are measurable in the original words. -/
theorem measurable_originalShapeHolePrefixValue {q : ℕ}
    {cost : (DyadicUnitCube q × ℝ) → (DyadicUnitCube q × ℝ) → ℝ}
    (hc : Measurable (Function.uncurry cost)) (m n : ℕ) :
    Measurable (originalShapeHolePrefixValue cost m n) := by
  unfold originalShapeHolePrefixValue
  apply PartialMatching.measurable_legalMaximumValue _
    (measurableSet_scalarClockLegalGraph_eq
      (fun (i : Fin m) (sample : (ℕ → DyadicUnitCube q × ℝ) × (ℕ → DyadicUnitCube q × ℝ)) ↦ (sample.1 (i : ℕ)).2)
      (fun (j : Fin n) (sample : (ℕ → DyadicUnitCube q × ℝ) × (ℕ → DyadicUnitCube q × ℝ)) ↦ (sample.2 (j : ℕ)).2) (by fun_prop) (by fun_prop)) _
  intro i j
  exact hc.comp (show Measurable (fun sample :
    (ℕ → DyadicUnitCube q × ℝ) × (ℕ → DyadicUnitCube q × ℝ) ↦ (sample.1 (i : ℕ),sample.2 (j : ℕ))) by fun_prop)

/-- Bounded actual costs are integrable for every original finite prefix. -/
theorem originalShapeHolePrefixValue_integrable
    {q : ℕ} (space : Measure (DyadicUnitCube q)) [IsProbabilityMeasure space]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {cost : (DyadicUnitCube q × ℝ) → (DyadicUnitCube q × ℝ) → ℝ}
    (hc : Measurable (Function.uncurry cost)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x y, |cost x y| ≤ C) (m n : ℕ) :
    Integrable (originalShapeHolePrefixValue cost m n) (originalShapeHoleSequenceLaw space α β) := by
  have : IsProbabilityMeasure (originalShapeHoleSequenceLaw space α β) := by
    unfold originalShapeHoleSequenceLaw
    infer_instance
  have hm := measurable_originalShapeHolePrefixValue hc m n
  apply Integrable.of_bound hm.aestronglyMeasurable (((min m n : ℕ) : ℝ)*C)
  filter_upwards with sample
  rw [Real.norm_eq_abs]
  exact PartialMatching.abs_legalMaximumValue_le_min _ _ hC (fun i j ↦ hb _ _)

/-- The actual min-prefix has the unchanged original equal-size two-iid law. -/
theorem originalShapeHolePrefix_integral_eq_iid
    {q : ℕ} (space : Measure (DyadicUnitCube q)) [IsProbabilityMeasure space]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {cost : (DyadicUnitCube q × ℝ) → (DyadicUnitCube q × ℝ) → ℝ}
    (hc : Measurable (Function.uncurry cost)) (n : ℕ) :
    (∫ sample, originalShapeHolePrefixValue cost n n sample ∂originalShapeHoleSequenceLaw space α β) =
      ∫ sample, originalShapeHoleIIDValue cost sample ∂originalShapeHoleIIDLaw space α β n := by
  let read := fun sample : (ℕ → DyadicUnitCube q × ℝ) × (ℕ → DyadicUnitCube q × ℝ) ↦
    ((fun i : Fin n ↦ sample.1 i),(fun j : Fin n ↦ sample.2 j))
  have hr : Measurable read := by fun_prop
  have hp : MeasurePreserving read (originalShapeHoleSequenceLaw space α β)
      (originalShapeHoleIIDLaw space α β n) := by
    refine ⟨hr,?_⟩
    change ((Measure.infinitePi (fun _ : ℕ ↦ space.prod α)).prod
      (Measure.infinitePi (fun _ : ℕ ↦ space.prod β))).map
      (Prod.map (fun (seq : ℕ → DyadicUnitCube q × ℝ) (i : Fin n) ↦ seq i) (fun (seq : ℕ → DyadicUnitCube q × ℝ) (j : Fin n) ↦ seq j)) = _
    rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),infinitePi_map_fin,infinitePi_map_fin]
    rfl
  have hm : Measurable (originalShapeHoleIIDValue cost (n := n)) := by
    unfold originalShapeHoleIIDValue
    apply PartialMatching.measurable_legalMaximumValue _
      (measurableSet_scalarClockLegalGraph_eq
        (fun (i : Fin n) (sample : (Fin n → DyadicUnitCube q × ℝ) × (Fin n → DyadicUnitCube q × ℝ)) ↦ (sample.1 i).2)
        (fun (j : Fin n) (sample : (Fin n → DyadicUnitCube q × ℝ) × (Fin n → DyadicUnitCube q × ℝ)) ↦ (sample.2 j).2) (by fun_prop) (by fun_prop)) _
    intro i j
    exact hc.comp (show Measurable (fun sample :
      (Fin n → DyadicUnitCube q × ℝ) × (Fin n → DyadicUnitCube q × ℝ) ↦ (sample.1 i,sample.2 j)) by fun_prop)
  exact hp.hasLaw.integral_comp hm.aestronglyMeasurable

/-- The original source/target clock gap gives genuine legal deletion
stability for unequal iid prefix counts. Equal-prefix spatial rates come from
the actual fixed-sample construction, without a Poisson-rate input. -/
theorem originalShapeHolePrefix_integral_le
    {q : ℕ} (hq : 4 < q) (space : Measure (DyadicUnitCube q)) [IsProbabilityMeasure space]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (π : Measure (ℝ × ℝ)) (hπ : Vlasov.IsCoupling π α β)
    {I : Set ℝ} {gap diameter : ℝ} (bins : FiniteScalarBins I gap) (hIm : MeasurableSet I) (hgap : 0 < gap)
    (hsep : ConditionalClockSupportBounds α β gap diameter)
    (hI : ∀ᵐ p ∂π, p.1 ∈ I ∧ p.2 ∈ I) (horder : ∀ᵐ p ∂π, p.1 ≤ p.2)
    (cost : (DyadicUnitCube q × ℝ) → (DyadicUnitCube q × ℝ) → ℝ)
    (hc : Measurable (Function.uncurry cost)) {C : ℝ} (hC : 0 ≤ C)
    (hcn : ∀ x y, 0 ≤ cost x y)
    (hquadratic : ∀ x y, cost x y ≤ C*‖dyadicCubePoint x.1-dyadicCubePoint y.1‖^2)
    (m n : ℕ) :
    (∫ sample, originalShapeHolePrefixValue cost m n sample ∂originalShapeHoleSequenceLaw space α β) ≤
      C*dyadicMatchingConstant q*((bins.count+1 : ℕ) : ℝ)^(2/(q : ℝ))*(min m n : ℕ)^(1-2/(q : ℝ)) +
      (C+2*((bins.count : ℝ)+1)*C)*Real.sqrt (2*(min m n : ℕ)*(bins.count+1)) +
      |(m : ℝ)-n| *(2*((bins.count : ℝ)+1)*C) := by
  have hb (x y : DyadicUnitCube q × ℝ) : |cost x y| ≤ C := by
    rw [abs_of_nonneg (hcn x y)]
    have hd := dyadicCube_dist_le_one x.1 y.1
    have hs : ‖dyadicCubePoint x.1-dyadicCubePoint y.1‖^2 ≤ 1 := by
      nlinarith [norm_nonneg (dyadicCubePoint x.1-dyadicCubePoint y.1)]
    exact (hquadratic x y).trans ((mul_le_mul_of_nonneg_left hs hC).trans_eq (mul_one C))
  let P := originalShapeHoleSequenceLaw space α β
  have : IsProbabilityMeasure P := by dsimp [P,originalShapeHoleSequenceLaw]; infer_instance
  have hα : ∀ᵐ a ∂α, a ∈ I := by
    rw [← hπ.1]
    exact (ae_map_iff measurable_fst.aemeasurable hIm).mpr (hI.mono fun _ h ↦ h.1)
  have hsrc := ae_all_iff.mpr (fun i : ℕ ↦
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ space.prod α) i).quasiMeasurePreserving.ae
      (Measure.quasiMeasurePreserving_snd.ae (hα.and α.support_mem_ae)))
  have htgt := ae_all_iff.mpr (fun j : ℕ ↦
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ space.prod β) j).quasiMeasurePreserving.ae
      (Measure.quasiMeasurePreserving_snd.ae β.support_mem_ae))
  let k := min m n
  let e : Fin k ↪ Fin m := ⟨fun i ↦ ⟨i.val,lt_of_lt_of_le i.isLt (min_le_left m n)⟩,
    fun _ _ h ↦ Fin.ext (congrArg (fun i : Fin m ↦ i.val) h)⟩
  let f : Fin k ↪ Fin n := ⟨fun i ↦ ⟨i.val,lt_of_lt_of_le i.isLt (min_le_right m n)⟩,
    fun _ _ h ↦ Fin.ext (congrArg (fun i : Fin n ↦ i.val) h)⟩
  have hpoint : ∀ᵐ sample ∂P,
      originalShapeHolePrefixValue cost m n sample ≤ originalShapeHolePrefixValue cost k k sample+
        |(m : ℝ)-n| *(2*((bins.count : ℝ)+1)*C) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hsrc,Measure.quasiMeasurePreserving_snd.ae htgt] with sample hs ht
    have hd := bins.abs_legalMaximumValue_subcloud_sub_le hgap
      (fun i : Fin m ↦ (sample.1 i).2) (fun j : Fin n ↦ (sample.2 j).2)
      (fun i ↦ (hs i).1)
      (fun i j ↦ by simpa only [Real.dist_eq,abs_sub_comm] using hsep.separated _ (hs i).2 _ (ht j))
      e f (fun i j ↦ cost (sample.1 i) (sample.2 j)) hC (fun i j _ ↦ hb _ _)
    have hcounts : (((m-k)+(n-k) : ℕ) : ℝ) = |(m : ℝ)-n| := by
      rcases le_total m n with h | h
      · simp only [k,min_eq_left h,Nat.sub_self,zero_add,Nat.cast_sub h]
        rw [abs_of_nonpos (by have hr : (m : ℝ) ≤ n := Nat.cast_le.mpr h; linarith : (m : ℝ)-n ≤ 0)]
        ring
      · simp only [k,min_eq_right h,Nat.sub_self,add_zero,Nat.cast_sub h]
        rw [abs_of_nonneg (by have hr : (n : ℝ) ≤ m := Nat.cast_le.mpr h; linarith : 0 ≤ (m : ℝ)-n)]
    rw [hcounts] at hd
    change |originalShapeHolePrefixValue cost k k sample-originalShapeHolePrefixValue cost m n sample| ≤ _ at hd
    linarith only [(neg_le_abs (originalShapeHolePrefixValue cost k k sample-originalShapeHolePrefixValue cost m n sample)).trans hd]
  have hL := integral_mono_ae (originalShapeHolePrefixValue_integrable space α β hc hC hb m n)
    ((originalShapeHolePrefixValue_integrable space α β hc hC hb k k).add (integrable_const _)) hpoint
  simp only [Pi.add_apply] at hL
  rw [integral_add (originalShapeHolePrefixValue_integrable space α β hc hC hb k k) (integrable_const _),
    integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul,originalShapeHolePrefix_integral_eq_iid space α β hc] at hL
  have hbmin := (originalShapeHole_integral_legalMaximumValue_le_of_space_clock_law
    (n := k) hq space α β π hπ bins hgap hsep hI horder cost hc hC hcn hquadratic).2
  linarith only [hL,hbmin]

end OTSelector.Reconstruction
