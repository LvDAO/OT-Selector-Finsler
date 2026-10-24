import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockOrientedPopulationData

/-! Actual fine-class count fibres supply the unchanged iid cube positions
and hence a genuine same-frame population plan with its true assignment rate. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ}
set_option backward.isDefEq.respectTransparency false

/-- On every actual h_D fibre, the class's literal original reserve points
have a true same-frame population coupling and the finite-mass expected rate. -/
theorem originalReserveBlockClassOrientedPopulation_count_fibre
    (P : Measure (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ)) [IsFiniteMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (rate : ℝ≥0)
    (frame : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (hR : 0 < R)
    (own other : Fin 2) {S T C D : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (k : ℕ) (hq : 4 < q) :
    let K := originalCenteredPhysicalCubeRegion frame (2*R)
    let M := (P.prod (markedPoissonLaw q ℝ μ rate)).restrict
      {p | originalReserveBlockClassCount K own other S T C D p = k}
    let read := originalReserveBlockClassInputReadout K own other S T C D k
    let Γ := originalReserveBlockClassOrientedPopulation frame R own other S T C D k
    (∀ᵐ p ∂M, IsFiniteMeasure (Γ p) ∧ Integrable (fun v ↦ ‖v.1-v.2‖^2) (Γ p) ∧
      (Γ p).map Prod.fst = ∑ i, Measure.dirac
        ((EuclideanSpace.equiv (Fin q) ℝ).symm (originalOrientedRawCubePhysicalMap frame R ((read p).2 i))) ∧
      (Γ p).map Prod.snd = ((volume.restrict K).withDensity
        (fun _ ↦ ENNReal.ofReal ((k : ℝ) / volume.real K))).map (EuclideanSpace.equiv (Fin q) ℝ).symm) ∧
    Integrable (fun p ↦ ∫ v, ‖v.1-v.2‖^2 ∂Γ p) M ∧
    (∫ p, ∫ v, ‖v.1-v.2‖^2 ∂Γ p ∂M) ≤
      M.real univ * (((q : ℝ)*(2*R)^2)*dyadicMatchingConstant q*(k : ℝ)^(1-2/(q : ℝ))) := by
  let K := originalCenteredPhysicalCubeRegion frame (2*R)
  have hK := (isCompact_originalStagePhysicalCube frame (2*R)).measurableSet
  let M := (P.prod (markedPoissonLaw q ℝ μ rate)).restrict
    {p | originalReserveBlockClassCount K own other S T C D p = k}
  let A := (P.prod (originalReserveCountMarkLaw μ rate)).restrict
    {z | (originalReserveBlockClassKept K own other S T C D z).card = k}
  let π := Measure.pi (fun _ : Fin k ↦ cubeMeasure (Fin q) 1)
  let read := originalReserveBlockClassInputReadout K own other S T C D k
  have hr := measurable_originalReserveBlockClassInputReadout hK own other hS hT hC hD k
  have hlaw : M.map read = A.prod π := by
    exact map_originalReserveBlockClassSelection_actual_jointLaw P μ rate hK own other hS hT hC hD k
  have hp : MeasurePreserving read M (A.prod π) := ⟨hr, hlaw⟩
  have : IsProbabilityMeasure (cubeMeasure (Fin q) 1) := isProbabilityMeasure_cubeMeasure (by norm_num)
  have hmass : M.real univ = A.real univ := by
    have hh := congrArg (fun ν ↦ ν univ) hlaw
    rw [Measure.map_apply hr MeasurableSet.univ, preimage_univ] at hh
    have ht : (A.prod π) univ = A univ := by
      calc
        _ = (A.prod π) (univ ×ˢ univ) := congrArg (A.prod π) univ_prod_univ.symm
        _ = A univ * π univ := Measure.prod_prod univ univ
        _ = _ := by rw [measure_univ (μ := π), mul_one]
    exact congrArg ENNReal.toReal (hh.trans ht)
  let f := fun x : Fin k → (Fin q → ℝ) ↦
    ∫ v, ‖v.1-v.2‖^2 ∂originalOrientedEuclideanCubePopulationCoupling frame R x
  have he := expected_originalOrientedEuclideanCubePopulationCoupling_squareCost_rate (n := k) hq frame R
  have hprod : Integrable (fun z : OriginalReserveSceneAux q × (Fin k → (Fin q → ℝ)) ↦ f z.2) (A.prod π) :=
    he.1.comp_snd A
  have hunit : ∀ᵐ x ∂π, ∀ i, x i ∈ unitCube q := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin k ↦ cubeMeasure (Fin q) 1) i).quasiMeasurePreserving.ae
      ((mem_ae_iff_prob_eq_one (measurableSet_unitCube q)).2 (cubeMeasure_unitCube q))
  have hprodunit : ∀ᵐ z : OriginalReserveSceneAux q × (Fin k → (Fin q → ℝ)) ∂A.prod π,
      ∀ i, z.2 i ∈ unitCube q := by
    apply ae_of_ae_map (μ := A.prod π) (p := fun x : Fin k → (Fin q → ℝ) ↦ ∀ i, x i ∈ unitCube q)
      measurable_snd.aemeasurable
    rw [Measure.map_snd_prod]
    exact Measure.ae_smul_measure hunit _
  refine ⟨?_, hp.integrable_comp_of_integrable hprod, ?_⟩
  · filter_upwards [hp.quasiMeasurePreserving.ae hprodunit] with p hpunit
    have hs := originalOrientedEuclideanCubePopulationCoupling_spec frame hR (read p).2 hpunit
    exact ⟨hs.1, (originalOrientedEuclideanCubePopulationCoupling_squareCost_eq frame R (read p).2).1,
      hs.2.1, originalOrientedEuclideanCubePopulationCoupling_target_density frame hR (read p).2 hpunit⟩
  · calc
      _ = ∫ z : OriginalReserveSceneAux q × (Fin k → (Fin q → ℝ)), f z.2 ∂A.prod π :=
        hp.hasLaw.integral_comp hprod.aestronglyMeasurable
      _ = A.real univ * ∫ x, f x ∂π := by
        simpa only [smul_eq_mul] using integral_fun_snd (μ := A) f
      _ ≤ A.real univ * (((q : ℝ)*(2*R)^2)*dyadicMatchingConstant q*(k : ℝ)^(1-2/(q : ℝ))) :=
        mul_le_mul_of_nonneg_left he.2 measureReal_nonneg
      _ = _ := by rw [hmass]

end OTSelector.Reconstruction
