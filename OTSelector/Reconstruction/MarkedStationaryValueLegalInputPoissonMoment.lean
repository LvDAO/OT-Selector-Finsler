import OTSelector.Reconstruction.MarkedStationaryValueLegalInputLaplaceMoment
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputWindowMoment
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputColorMarginals

/-!
# Exact prescribed Poisson input first moments of the actual joint weak limit

The already identified compact Laplace functional determines the extended mean.
The finite physical Poisson window mean then cancels its actual Haar mass,
yielding the original physical Haar-clock intensity for both immutable colors.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalInputPoissonMomentInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalInputPoissonMomentPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Every nonnegative compact input test of the same actual joint weak limit
has its exact original independent physical Haar-clock first moment. -/
theorem lintegral_legalMarkedInput_testIntegral_eq_of_tendsto
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k) (hlarge : Tendsto L atTop atTop)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q))
    (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x) :
    (∫⁻ s, ENNReal.ofReal (LocalFiniteMeasure.testIntegral s.2 F)
      ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
      (∫⁻ x, ENNReal.ofReal (F (x, 0)) ∂(volume : Measure (Fin q → ℝ)).prod α) +
        ∫⁻ x, ENNReal.ofReal (F (x, 1)) ∂(volume : Measure (Fin q → ℝ)).prod β := by
  obtain ⟨S, hS, hbound⟩ := (F.hasCompactSupport.image
    (continuous_fst.comp continuous_fst)).isBounded.exists_pos_norm_lt
  have hzero (c : Fin 2) (x : LegalMarkedPhysicalPoint q)
      (hx : x.1 ∉ haarRootCube (Fin q) S) : F (x, c) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hsupp
    apply hx
    have hn : ‖x.1‖ < S := hbound _ ⟨(x, c), hsupp, rfl⟩
    have hi (i : Fin q) : |x.1 i| ≤ S := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x.1 i).trans hn.le
    exact ⟨fun i ↦ (abs_le.mp (hi i)).1, fun i ↦ (abs_le.mp (hi i)).2⟩
  let U := haarRootCube (Fin q) S
  have hU : MeasurableSet U := measurableSet_Icc
  have hUfin : volume U ≠ ∞ := isCompact_Icc.measure_ne_top
  have hUpos : volume U ≠ 0 := by
    rw [volume_haarRootCube (Fin q) hS.le, Fintype.card_fin]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity : 0 < 2 * S) q)).ne'
  let κ := legalInputPoissonWindowLaw q U α β
  have : IsProbabilityMeasure κ := isProbabilityMeasure_legalInputPoissonWindowLaw q hS.le hU
    (Subset.refl _) hUpos α β
  let X (s : LegalMarkedOptimalInputScene q) := LocalFiniteMeasure.testIntegral s.2 F
  let Y (b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)) :=
    legalInputBlockTest (fun x ↦ F (x, 0)) b.1 + legalInputBlockTest (fun x ↦ F (x, 1)) b.2
  have hm (c : Fin 2) : Measurable (fun x : LegalMarkedPhysicalPoint q ↦ F (x, c)) :=
    F.continuous.measurable.comp (measurable_id.prodMk measurable_const)
  have hX : Measurable X := (LocalFiniteMeasure.continuous_testIntegral F).measurable.comp measurable_snd
  have hY : Measurable Y := by
    exact ((measurable_legalInputBlockTest (hm 0)).comp measurable_fst).add
      ((measurable_legalInputBlockTest (hm 1)).comp measurable_snd)
  have hXn : ∀ s, 0 ≤ X s := fun s ↦ integral_nonneg hF
  have hYn : ∀ b, 0 ≤ Y b := fun b ↦ add_nonneg
    (Finset.sum_nonneg (fun i _ ↦ hF _)) (Finset.sum_nonneg (fun i _ ↦ hF _))
  have hlap (a : ℝ) (ha : 0 < a) :
      (∫ s, Real.exp (-a * X s) ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
        ∫ b, Real.exp (-a * Y b) ∂κ := by
    have haF : ∀ x, 0 ≤ (a • F) x := fun x ↦ mul_nonneg ha.le (hF x)
    have hw : ∀ (x : LegalMarkedPhysicalPoint q) (c : Fin 2),
        x.1 ∉ haarRootCube (Fin q) S → (a • F) (x, c) = 0 := by
      intro x c hx
      change a * F (x, c) = 0
      rw [hzero c x hx, mul_zero]
    have h := integral_legalMarkedInputSceneLaplace_eq_originalPoisson_window_of_tendsto q α β
      kin hk g hg t L hL hlarge hweak hS (a • F) haF hw
    have htest (s : LegalMarkedOptimalInputScene q) :
        LocalFiniteMeasure.testIntegral s.2 (a • F) = a * X s := by
      change (∫ x, a * F x ∂(s.2 : Measure (LegalColoredInputPoint q))) = _
      exact integral_const_mul _ _
    have hblock (b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)) :
        legalInputBlockLaplace (fun x ↦ (a • F) (x, 0)) (fun x ↦ (a • F) (x, 1)) b =
          Real.exp (-a * Y b) := by
      change Real.exp (-((∑ i, a * F (b.1.2 i, 0)) + (∑ j, a * F (b.2.2 j, 1)))) =
        Real.exp (-a * ((∑ i, F (b.1.2 i, 0)) + (∑ j, F (b.2.2 j, 1))))
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      congr 1
      ring
    change (∫ s, Real.exp (-LocalFiniteMeasure.testIntegral s.2 (a • F))
      ∂(Q : Measure (LegalMarkedOptimalInputScene q))) = _ at h
    simpa only [htest, hblock, neg_mul] using h
  have he := lintegral_ofReal_eq_of_nonnegative_laplace_eq (Q : Measure (LegalMarkedOptimalInputScene q))
    κ X Y hX hY hXn hYn hlap
  apply he.trans
  have hfb (c : Fin 2) : ∀ x, |F (x, c)| ≤ ‖F.toBoundedContinuousFunction‖ := by
    intro x
    change ‖F.toBoundedContinuousFunction (x, c)‖ ≤ _
    exact F.toBoundedContinuousFunction.norm_coe_le_norm _
  have hy (b) : ENNReal.ofReal (Y b) =
      ENNReal.ofReal (legalInputBlockTest (fun x ↦ F (x, 0)) b.1) +
        ENNReal.ofReal (legalInputBlockTest (fun x ↦ F (x, 1)) b.2) :=
    ENNReal.ofReal_add (Finset.sum_nonneg (fun i _ ↦ hF _)) (Finset.sum_nonneg (fun i _ ↦ hF _))
  simp_rw [hy]
  rw [lintegral_add_left (show Measurable (fun b : BlockData (LegalMarkedPhysicalPoint q) ×
    BlockData (LegalMarkedPhysicalPoint q) ↦ ENNReal.ofReal (legalInputBlockTest (fun x ↦ F (x, 0)) b.1)) from
      ((measurable_legalInputBlockTest (hm 0)).ennreal_ofReal).comp measurable_fst),
    lintegral_legalInputPoissonWindowLaw_sourceTest q hU hUfin hUpos α β _ (hm 0) (fun x ↦ hF (x, 0)) (hfb 0),
    lintegral_legalInputPoissonWindowLaw_targetTest q hU hUfin hUpos α β _ (hm 1) (fun x ↦ hF (x, 1)) (hfb 1)]
  have hfull (c : Fin 2) (γ : Measure ℝ) [IsProbabilityMeasure γ] :
      (∫⁻ x, ENNReal.ofReal (F (x, c)) ∂((volume : Measure (Fin q → ℝ)).restrict U).prod γ) =
        ∫⁻ x, ENNReal.ofReal (F (x, c)) ∂(volume : Measure (Fin q → ℝ)).prod γ := by
    rw [Measure.restrict_prod_eq_prod_univ, ← lintegral_indicator (hU.prod MeasurableSet.univ)]
    apply lintegral_congr
    intro x
    by_cases hx : x.1 ∈ U
    · rw [indicator_of_mem (show x ∈ U ×ˢ univ from ⟨hx, mem_univ _⟩)]
    · rw [indicator_of_notMem (show x ∉ U ×ˢ univ from fun h ↦ hx h.1), hzero c x hx, ENNReal.ofReal_zero]
  rw [hfull 0 α, hfull 1 β]

end OTSelector.Reconstruction
