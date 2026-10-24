import OTSelector.MeasureTheory.CompactProductMarginalTests
import OTSelector.MeasureTheory.SpatialTargetCutoff
import OTSelector.Probability.CavitySemidiscreteSourceMassLaw

/-!
# Actual source-marginal test errors from transport energy

Two plans with the same source can differ on a compact product test only through
long edges leaving its target cutoff. The expectation is taken on the unchanged
joint environment-root space.
-/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Probability

variable {ι A B : Type*} [Fintype ι]
  [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
  [T2Space A] [LocallyCompactSpace A] [PseudoMetrizableSpace A]
  [SigmaCompactSpace A] [SecondCountableTopology A]
  [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [T2Space B] [LocallyCompactSpace B] [PseudoMetrizableSpace B]
  [SigmaCompactSpace B] [SecondCountableTopology B] [CompactSpace B]

omit [LocallyCompactSpace A] [PseudoMetrizableSpace A] [SigmaCompactSpace A]
  [SigmaCompactSpace B] in
/-- The actual finite plans' compact-test difference is controlled by their
actual long-edge masses, without replacing either plan by a matching. -/
theorem ofReal_abs_product_tests_sub_le_longEdge_mass
    (π₀ π₁ : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B)))
    [IsFiniteMeasure π₀] [IsFiniteMeasure π₁]
    (hsource : π₀.fst = π₁.fst)
    (f : C_c((ι → ℝ) × A, ℝ)) (U : Set (ι → ℝ)) (R₀ : ℝ)
    (hU : ∀ x ∈ tsupport f, x.1 ∈ U) (hR₀ : ∀ x ∈ tsupport f, ‖x.1‖ ≤ R₀)
    (n : ℕ) :
    ENNReal.ofReal |(∫ e, cavityProductTest f
        (LocalFiniteMeasure.exhaustionCutoff (cavitySpatialTargetExhaustion R₀) n) e ∂π₀) -
      ∫ e, cavityProductTest f
        (LocalFiniteMeasure.exhaustionCutoff (cavitySpatialTargetExhaustion R₀) n) e ∂π₁| ≤
    ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
      (π₀ (cavityLongEdgeWindow U (ENNReal.ofReal (((n : ℝ) + 1) ^ 2))) +
       π₁ (cavityLongEdgeWindow U (ENNReal.ofReal (((n : ℝ) + 1) ^ 2)))) := by
  have hf₀ : Integrable (fun e : (((ι → ℝ) × A) × ((ι → ℝ) × B)) ↦ f e.1) π₀ :=
    Integrable.of_bound (f.continuous.measurable.comp measurable_fst).aestronglyMeasurable
      ‖f.toBoundedContinuousFunction‖ (Filter.Eventually.of_forall fun e ↦
        f.toBoundedContinuousFunction.norm_coe_le_norm e.1)
  have hf₁ : Integrable (fun e : (((ι → ℝ) × A) × ((ι → ℝ) × B)) ↦ f e.1) π₁ :=
    Integrable.of_bound (f.continuous.measurable.comp measurable_fst).aestronglyMeasurable
      ‖f.toBoundedContinuousFunction‖ (Filter.Eventually.of_forall fun e ↦
        f.toBoundedContinuousFunction.norm_coe_le_norm e.1)
  have h := ENNReal.ofReal_le_ofReal (abs_product_tests_sub_le_common_source_tails π₀ π₁ f
    (LocalFiniteMeasure.exhaustionCutoff (cavitySpatialTargetExhaustion R₀) n)
    hsource hf₀ hf₁ (LocalFiniteMeasure.exhaustionCutoff_bounds _ n)
    (cavitySpatialTargetExhaustion R₀ n) (LocalFiniteMeasure.exhaustionCutoff_eq_one _ n)
    (measure_lt_top _ _) (measure_lt_top _ _))
  rw [ENNReal.ofReal_mul (norm_nonneg _),
    ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg, ofReal_measureReal,
    ofReal_measureReal] at h
  apply h.trans
  apply mul_le_mul_right
  exact add_le_add (measure_source_tail_le_longEdgeWindow π₀ (tsupport f) U R₀ hU hR₀ n)
    (measure_source_tail_le_longEdgeWindow π₁ (tsupport f) U R₀ hU hR₀ n)

local instance cavitySemidiscreteExpectedMarginalErrorLocalInst1 : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × A) × ((ι → ℝ) × B))) :=
  LocalFiniteMeasure.instPolishSpace

/-- The original common scene's compact source-test error has an explicit
inverse-square cutoff bound from its actual expected displacement energies. -/
theorem cavityRootedLocalSceneLaw_product_test_error_le {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (p : Ω → Fin (m + 1) → ℝ)
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hplusm : ∀ j, Measurable (fun v ↦ aplus v j))
    (hminusm : ∀ j, Measurable (fun v ↦ aminus v j))
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j))
    (hfeas : ∀ᵐ ω ∂P,
      IsSemidiscreteAllocation μ (p ω) (fun s ↦ aplus (ω, s)) ∧
      IsSemidiscreteAllocation μ (p ω) (fun s ↦ aminus (ω, s)))
    (N : ℝ) (hN : 0 < N) (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal N)
    (f : C_c((ι → ℝ) × A, ℝ)) (U : Set (ι → ℝ)) (hUm : MeasurableSet U)
    (hUfinite : volume U ≠ ⊤) (R₀ : ℝ)
    (hU : ∀ x ∈ tsupport f, x.1 ∈ U) (hR₀ : ∀ x ∈ tsupport f, ‖x.1‖ ≤ R₀)
    (C : ℝ≥0∞)
    (henergyplus : (∫⁻ ω, ∫⁻ e, ENNReal.ofReal (‖(Y ω e.2).1 - e.1.1‖ ^ 2)
      ∂semidiscreteAllocationMeasure μ (fun s ↦ aplus (ω, s)) ∂P) ≤ C)
    (henergyminus : (∫⁻ ω, ∫⁻ e, ENNReal.ofReal (‖(Y ω e.2).1 - e.1.1‖ ^ 2)
      ∂semidiscreteAllocationMeasure μ (fun s ↦ aminus (ω, s)) ∂P) ≤ C)
    (R : ℕ) :
    (∫⁻ π : CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B),
      ENNReal.ofReal |LocalFiniteMeasure.testIntegral π.1
        (cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff
          (cavitySpatialTargetExhaustion R₀) R)) -
        LocalFiniteMeasure.testIntegral π.2
        (cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff
          (cavitySpatialTargetExhaustion R₀) R))|
      ∂(cavityRootedLocalSceneLaw P μ aplus aminus hplusm hminusm Y hY N hN D hD :
        Measure (CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B)))) ≤
    ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
      (volume U * C / ENNReal.ofReal (((R : ℝ) + 1) ^ 2) +
        volume U * C / ENNReal.ofReal (((R : ℝ) + 1) ^ 2)) := by
  let r := ENNReal.ofReal (((R : ℝ) + 1) ^ 2)
  have hr : r ≠ 0 := by dsimp [r]; positivity
  have hrt : r ≠ ⊤ := ENNReal.ofReal_ne_top
  let W := cavityLongEdgeWindow (A := A) (B := B) U r
  have hW : MeasurableSet W := measurableSet_cavityLongEdgeWindow hUm r
  have hm₀ : Measurable (fun v : Ω × (ι → ℝ) ↦
      cavitySpatialRootedPlan μ (fun s ↦ aplus (v.1, s)) (Y v.1) N v.2 W) :=
    (Measure.measurable_coe hW).comp (measurable_joint_cavitySpatialRootedPlan μ aplus hplusm Y hY N)
  have hb₀ := lintegral_original_rootedPlan_longEdgeWindow_le_of_energy P μ p aplus hplusm
    Y hY (hfeas.mono fun _ h ↦ h.1) N hN D U hUm hUfinite C henergyplus r hr hrt
  have hb₁ := lintegral_original_rootedPlan_longEdgeWindow_le_of_energy P μ p aminus hminusm
    Y hY (hfeas.mono fun _ h ↦ h.2) N hN D U hUm hUfinite C henergyminus r hr hrt
  let φ : C_c((((ι → ℝ) × A) × ((ι → ℝ) × B)), ℝ) := cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff
    (cavitySpatialTargetExhaustion (B := B) R₀) R)
  have htest : Measurable (fun π : CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B) ↦
      ENNReal.ofReal |LocalFiniteMeasure.testIntegral π.1 φ - LocalFiniteMeasure.testIntegral π.2 φ|) :=
    (((LocalFiniteMeasure.continuous_testIntegral φ).comp continuous_fst).sub
      ((LocalFiniteMeasure.continuous_testIntegral φ).comp continuous_snd)).abs.measurable.ennreal_ofReal
  have := isProbabilityMeasure_cavityRootMeasure volume D N hN hD
  have he := (measurePreserving_fst (μ := P)
    (ν := cavityRootMeasure volume D N)).quasiMeasurePreserving.ae hfeas
  change (∫⁻ π : CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B),
      ENNReal.ofReal |LocalFiniteMeasure.testIntegral π.1 φ - LocalFiniteMeasure.testIntegral π.2 φ|
    ∂(P.prod (cavityRootMeasure volume D N)).map
      (cavityRootedLocalScene μ aplus aminus Y N)) ≤ _
  rw [lintegral_map htest (measurable_cavityRootedLocalScene μ aplus aminus hplusm hminusm Y hY N)]
  calc
    _ ≤ ∫⁻ v : Ω × (ι → ℝ), ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        (cavitySpatialRootedPlan μ (fun s ↦ aplus (v.1, s)) (Y v.1) N v.2 W +
          cavitySpatialRootedPlan μ (fun s ↦ aminus (v.1, s)) (Y v.1) N v.2 W)
        ∂P.prod (cavityRootMeasure volume D N) := by
      apply lintegral_mono_ae
      filter_upwards [he] with v hv
      have := hv.1.isFiniteMeasure_cavitySpatialRootedPlan (Y v.1) N v.2
      have := hv.2.isFiniteMeasure_cavitySpatialRootedPlan (Y v.1) N v.2
      simp only [cavityRootedLocalScene, LocalFiniteMeasure.testIntegral,
        coe_finitePlanLocalVersion, ite_eq_left (measure_lt_top _ univ)]
      apply ofReal_abs_product_tests_sub_le_longEdge_mass _ _ _ f U R₀ hU hR₀ R
      rw [hv.1.fst_cavitySpatialRootedPlan, hv.2.fst_cavitySpatialRootedPlan]
    _ = ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        ((∫⁻ v : Ω × (ι → ℝ),
          cavitySpatialRootedPlan μ (fun s ↦ aplus (v.1, s)) (Y v.1) N v.2 W
          ∂P.prod (cavityRootMeasure volume D N)) +
        ∫⁻ v : Ω × (ι → ℝ),
          cavitySpatialRootedPlan μ (fun s ↦ aminus (v.1, s)) (Y v.1) N v.2 W
          ∂P.prod (cavityRootMeasure volume D N)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hm₀]
    _ ≤ _ := mul_le_mul_right (add_le_add hb₀ hb₁) _

end OTSelector.Probability
