import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockOrientedPopulationFibre
import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingCountMomentPoisson

/-! The actual random fine-class count inherits the true Poisson fractional
moment, and count-fibre population energies assemble without a rate callback. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ}
set_option backward.isDefEq.respectTransparency false

private theorem measurable_orientedPopulationEnergy
    {Ω : Type*} [MeasurableSpace Ω]
    (Γ : Ω → Measure (EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin q))) (hΓ : Measurable Γ) :
    Measurable (fun p ↦ ∫ v, ‖v.1-v.2‖^2 ∂Γ p) := by
  have hc : Measurable (fun v : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin q) ↦
      ‖v.1-v.2‖^2) := (measurable_fst.sub measurable_snd).norm.pow_const 2
  convert ((Measure.measurable_lintegral hc.ennreal_ofReal).comp hΓ).ennreal_toReal using 1
  funext p
  exact integral_eq_lintegral_of_nonneg_ae (.of_forall fun _ ↦ sq_nonneg _) hc.aestronglyMeasurable

/-- Arbitrary independent original auxiliary observations, including a truly
dilated main scene, produce actual same-frame class plans and the full random
energy rate. No spatial-law, count-moment or energy estimate is an input. -/
theorem originalReserveBlockClassOrientedPopulation_random_spec_and_energy
    (P : Measure (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ)) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (rate : ℝ≥0)
    (frame : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (hR : 0 < R)
    (own other : Fin 2) {S T C D : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hC : MeasurableSet C) (hD : MeasurableSet D) (hq : 4 < q) :
    let K := originalCenteredPhysicalCubeRegion frame (2*R)
    let M := P.prod (markedPoissonLaw q ℝ μ rate)
    let N := originalReserveBlockClassCount K own other S T C D
    let Γ := originalReserveBlockClassOrientedPopulationRandom frame R own other S T C D
    (∀ᵐ p ∂M, IsFiniteMeasure (Γ p) ∧ Integrable (fun v ↦ ‖v.1-v.2‖^2) (Γ p) ∧
      (Γ p).map Prod.fst = ∑ i, Measure.dirac
        ((EuclideanSpace.equiv (Fin q) ℝ).symm (originalOrientedRawCubePhysicalMap frame R
          ((originalReserveBlockClassInputReadout K own other S T C D (N p) p).2 i))) ∧
      (Γ p).map Prod.snd = ((volume.restrict K).withDensity
        (fun _ ↦ ENNReal.ofReal ((N p : ℝ) / volume.real K))).map (EuclideanSpace.equiv (Fin q) ℝ).symm) ∧
    Integrable (fun p ↦ ∫ v, ‖v.1-v.2‖^2 ∂Γ p) M ∧
    (∫ p, ∫ v, ‖v.1-v.2‖^2 ∂Γ p ∂M) ≤
      ((q : ℝ)*(2*R)^2)*dyadicMatchingConstant q*(rate : ℝ)^(1-2/(q : ℝ)) := by
  let K := originalCenteredPhysicalCubeRegion frame (2*R)
  let M := P.prod (markedPoissonLaw q ℝ μ rate)
  let N := originalReserveBlockClassCount K own other S T C D
  let A := ((q : ℝ)*(2*R)^2)*dyadicMatchingConstant q
  let r := 1-2/(q : ℝ)
  let e := fun k p ↦ ∫ v, ‖v.1-v.2‖^2
    ∂originalReserveBlockClassOrientedPopulation frame R own other S T C D k p
  have hK := (isCompact_originalStagePhysicalCube frame (2*R)).measurableSet
  have hN : Measurable N := measurable_originalReserveBlockClassCount hK own other hS hT hC hD
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hr₀ : 0 < r := sub_pos.mpr ((div_lt_one hqpos).mpr (by exact_mod_cast (show 2 < q by omega)))
  have hr₁ : r < 1 := sub_lt_self _ (div_pos (by norm_num) hqpos)
  have hNI : Integrable (fun p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) ×
      MarkedCloudSpace q ℝ ↦ (p.2.1 : ℝ)) M :=
    ((integrable_id_poissonMeasure rate).comp_fst _).comp_snd P
  have hmean : (∫ p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) ×
      MarkedCloudSpace q ℝ, (p.2.1 : ℝ) ∂M) = (rate : ℝ) := by
    change (∫ p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) ×
      MarkedCloudSpace q ℝ, (p.2.1 : ℝ) ∂P.prod (markedPoissonLaw q ℝ μ rate)) = _
    rw [integral_fun_snd (μ := P) (fun z : MarkedCloudSpace q ℝ ↦ (z.1 : ℝ))]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    rw [markedPoissonLaw, integral_fun_fst (fun n : ℕ ↦ (n : ℝ))]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    exact integral_id_poissonMeasure rate
  have hmoment := retainedCount_rpow_integrable_and_integral_le M (fun p ↦ p.2.1) N
    measurable_snd.fst hN hNI (originalReserveBlockClassCount_le K own other S T C D) hr₀ hr₁
  rw [hmean] at hmoment
  have hfibre (k) := originalReserveBlockClassOrientedPopulation_count_fibre P μ rate frame hR
    own other hS hT hC hD k hq
  have he (k) : Measurable (e k) := measurable_orientedPopulationEnergy _
    ((measurable_originalOrientedEuclideanCubePopulationCoupling frame R).comp
      (measurable_originalReserveBlockClassInputReadout hK own other hS hT hC hD k).snd)
  have hb (k) : (∫ p, e k p ∂M.restrict {p | N p = k}) ≤
      A * M.real {p | N p = k} * (k : ℝ)^r := by
    simpa only [M, N, A, e, r, measureReal_def, Measure.restrict_apply_univ, mul_left_comm, mul_assoc]
      using (hfibre k).2.2
  have hE := randomCount_energy_integrable_and_integral_le M N hN e he
    (fun _ _ ↦ integral_nonneg fun _ ↦ sq_nonneg _) A hmoment.1
    (fun k ↦ (hfibre k).2.1) hb
  refine ⟨?_, hE.2.1, hE.2.2.trans ?_⟩
  · exact randomCount_ae_of_restrict M N _ (fun k ↦ (hfibre k).1)
  · exact mul_le_mul_of_nonneg_left hmoment.2
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg q) (sq_nonneg (2*R))) (dyadicMatchingConstant_pos hq).le)

end OTSelector.Reconstruction
