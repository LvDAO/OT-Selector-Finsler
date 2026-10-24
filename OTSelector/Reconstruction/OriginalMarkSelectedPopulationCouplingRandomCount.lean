import OTSelector.MeasureTheory.CountFiberIntegration
import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingRandomCountMoment
import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingActualReserve

/-! Actual original reserve population plans at their full random retained count. -/

open MeasureTheory Set Function
open OTSelector.Probability
open scoped NNReal ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {q : ℕ}

/-- The concrete population plan uses all actual kept class indices, at their actual count. -/
def originalReserveExcessClassPopulationCouplingRandom (R : ℝ) (own other : Fin 2)
    (C D : Set ℝ) (z : EuclideanSpace ℝ (Fin q)) (L : ℝ)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ) :
    Measure (EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin q)) :=
  originalReserveExcessClassPopulationCoupling R own other C D
    (originalReserveExcessClassCount R own other C D p) z L p

/-- Selecting the actual count preserves measurability in the fixed space of measures. -/
theorem measurable_originalReserveExcessClassPopulationCouplingRandom
    (R : ℝ) (own other : Fin 2) {C D : Set ℝ} (hC : MeasurableSet C) (hD : MeasurableSet D)
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) :
    Measurable (originalReserveExcessClassPopulationCouplingRandom R own other C D z L) := by
  unfold originalReserveExcessClassPopulationCouplingRandom
  refine measurable_count_diagonal (originalReserveExcessClassCount (q := q) R own other C D)
    (measurable_originalReserveExcessClassCount R own other hC hD)
    (fun k p ↦ originalReserveExcessClassPopulationCoupling R own other C D k z L p) ?_
  intro k
  unfold originalReserveExcessClassPopulationCoupling
  exact (originalRawCubePopulationCoupling_spec (n := k) z L).1.comp
    ((measurable_originalReserveExcessClassInputReadout R own other hC hD k).snd)

private theorem measurable_populationSquareEnergy
    {Ω : Type*} [MeasurableSpace Ω]
    (Γ : Ω → Measure (EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin q)))
    (hΓ : Measurable Γ) : Measurable (fun p ↦ ∫ v, ‖v.1-v.2‖^2 ∂Γ p) := by
  have hc : Measurable (fun v : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin q) ↦
      ‖v.1-v.2‖^2) := (measurable_fst.sub measurable_snd).norm.pow_const 2
  have hh := (Measure.measurable_lintegral hc.ennreal_ofReal).comp hΓ
  convert hh.ennreal_toReal using 1
  funext p
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _) hc.aestronglyMeasurable

private theorem originalReserveClass_random_bound
    {Ω : Type*} [MeasurableSpace Ω] (M : Measure Ω) [IsFiniteMeasure M]
    (view : Ω → (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ)
    (hv : Measurable view) (R : ℝ) (own other : Fin 2)
    {C D : Set ℝ} (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hq : 4 < q) (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) (rate : ℝ≥0)
    (hmoment : let N := originalReserveExcessClassCount R own other C D ∘ view
      Integrable (fun p ↦ (N p : ℝ) ^ (1-2/(q : ℝ))) M ∧
      (∫ p, (N p : ℝ) ^ (1-2/(q : ℝ)) ∂M) ≤ (rate : ℝ) ^ (1-2/(q : ℝ)))
    (hfibre : ∀ k,
      let Mk := M.restrict {p | originalReserveExcessClassCount R own other C D (view p) = k}
      let Γk := fun p ↦ originalReserveExcessClassPopulationCoupling R own other C D k z L (view p)
      Integrable (fun p ↦ ∫ v, ‖v.1-v.2‖^2 ∂Γk p) Mk ∧
      (∫ p, ∫ v, ‖v.1-v.2‖^2 ∂Γk p ∂Mk) ≤
        Mk.real univ * (((q : ℝ)*L^2)*dyadicMatchingConstant q*(k : ℝ)^(1-2/(q : ℝ)))) :
    let Γ := originalReserveExcessClassPopulationCouplingRandom R own other C D z L ∘ view
    Measurable Γ ∧ Measurable (fun p ↦ ∫ v, ‖v.1-v.2‖^2 ∂Γ p) ∧
      Integrable (fun p ↦ ∫ v, ‖v.1-v.2‖^2 ∂Γ p) M ∧
      (∫ p, ∫ v, ‖v.1-v.2‖^2 ∂Γ p ∂M) ≤
        ((q : ℝ)*L^2)*dyadicMatchingConstant q*(rate : ℝ)^(1-2/(q : ℝ)) := by
  let N := originalReserveExcessClassCount R own other C D ∘ view
  let A := ((q : ℝ)*L^2)*dyadicMatchingConstant q
  let e := fun k p ↦ ∫ v, ‖v.1-v.2‖^2 ∂originalReserveExcessClassPopulationCoupling
    R own other C D k z L (view p)
  have hN := (measurable_originalReserveExcessClassCount R own other hC hD).comp hv
  have hΓ := (measurable_originalReserveExcessClassPopulationCouplingRandom R own other hC hD z L).comp hv
  have he (k) : Measurable (e k) := measurable_populationSquareEnergy _
    (((originalRawCubePopulationCoupling_spec (n := k) z L).1.comp
      (measurable_originalReserveExcessClassInputReadout R own other hC hD k).snd).comp hv)
  have hb (k) : (∫ p, e k p ∂M.restrict {p | N p = k}) ≤
      A * M.real {p | N p = k} * (k : ℝ) ^ (1-2/(q : ℝ)) := by
    simpa only [N, e, A, comp_apply, measureReal_def, Measure.restrict_apply_univ,
      mul_left_comm, mul_assoc]
      using (hfibre k).2
  have h := randomCount_energy_integrable_and_integral_le M N hN e he
    (fun _ _ ↦ integral_nonneg fun _ ↦ sq_nonneg _) A hmoment.1
    (fun k ↦ (hfibre k).1) hb
  exact ⟨hΓ, h.1, h.2.1, h.2.2.trans
    (mul_le_mul_of_nonneg_left hmoment.2 (mul_nonneg
      (mul_nonneg (Nat.cast_nonneg q) (sq_nonneg L)) (dyadicMatchingConstant_pos hq).le))⟩

variable {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- The actual source plan has a complete expectation bound under the original
joined scene and both reserves, with no fixed-count condition or rate callback. -/
theorem LegalWeightedStationaryPoissonMatching.original_sourceReserveClass_randomPopulationCoupling
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (rate : ℝ≥0) (R : ℝ)
    {C D : Set ℝ} (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hq : 4 < q) (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) :
    let Γ := originalReserveExcessClassPopulationCouplingRandom R 0 1 C D z L ∘
      originalSourceReserveExperimentSplice
    Measurable Γ ∧ Measurable (fun p ↦ ∫ v, ‖v.1-v.2‖^2 ∂Γ p) ∧
      Integrable (fun p ↦ ∫ v, ‖v.1-v.2‖^2 ∂Γ p) (originalMainReserveExperimentLaw Q rate) ∧
      (∫ p, ∫ v, ‖v.1-v.2‖^2 ∂Γ p ∂originalMainReserveExperimentLaw Q rate) ≤
        ((q : ℝ)*L^2)*dyadicMatchingConstant q*(rate : ℝ)^(1-2/(q : ℝ)) := by
  have : IsProbabilityMeasure (originalMainReserveExperimentLaw Q rate) := by
    unfold originalMainReserveExperimentLaw twoMarkedCloudLaw
    infer_instance
  have hqR : (4 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hr₀ : 0 < 1-2/(q : ℝ) := by
    have : 2/(q : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  have hr₁ : 1-2/(q : ℝ) < 1 := by have := div_pos (by norm_num : (0 : ℝ)<2) (by linarith : (0 : ℝ)<q); linarith
  exact originalReserveClass_random_bound _ _
    (by unfold originalSourceReserveExperimentSplice; fun_prop) R 0 1 hC hD hq z L rate
    (Q.original_sourceReserveClass_count_rpow rate R hC hD hr₀ hr₁)
    (fun k ↦ let h := Q.original_sourceReserveClass_populationCoupling rate R hC hD k hq z L
      ⟨h.2.2.1, h.2.2.2⟩)

/-- The actual target plan obeys the same complete rate under that identical experiment. -/
theorem LegalWeightedStationaryPoissonMatching.original_targetReserveClass_randomPopulationCoupling
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (rate : ℝ≥0) (R : ℝ)
    {C D : Set ℝ} (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hq : 4 < q) (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) :
    let Γ := originalReserveExcessClassPopulationCouplingRandom R 1 0 C D z L ∘
      originalTargetReserveExperimentSplice
    Measurable Γ ∧ Measurable (fun p ↦ ∫ v, ‖v.1-v.2‖^2 ∂Γ p) ∧
      Integrable (fun p ↦ ∫ v, ‖v.1-v.2‖^2 ∂Γ p) (originalMainReserveExperimentLaw Q rate) ∧
      (∫ p, ∫ v, ‖v.1-v.2‖^2 ∂Γ p ∂originalMainReserveExperimentLaw Q rate) ≤
        ((q : ℝ)*L^2)*dyadicMatchingConstant q*(rate : ℝ)^(1-2/(q : ℝ)) := by
  have : IsProbabilityMeasure (originalMainReserveExperimentLaw Q rate) := by
    unfold originalMainReserveExperimentLaw twoMarkedCloudLaw
    infer_instance
  have hqR : (4 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hr₀ : 0 < 1-2/(q : ℝ) := by
    have : 2/(q : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  have hr₁ : 1-2/(q : ℝ) < 1 := by have := div_pos (by norm_num : (0 : ℝ)<2) (by linarith : (0 : ℝ)<q); linarith
  exact originalReserveClass_random_bound _ _
    (by unfold originalTargetReserveExperimentSplice; fun_prop) R 1 0 hC hD hq z L rate
    (Q.original_targetReserveClass_count_rpow rate R hC hD hr₀ hr₁)
    (fun k ↦ let h := Q.original_targetReserveClass_populationCoupling rate R hC hD k hq z L
      ⟨h.2.2.1, h.2.2.2⟩)

end OTSelector.Reconstruction
