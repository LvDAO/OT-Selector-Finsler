import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingRawCube
import OTSelector.Reconstruction.OriginalReserveSelectedSpatialLawJoinedClassExperiment

/-! Genuine population transport for the actual classwise surviving original reserve
positions, under the same joined main-scene and two-reserve experiment. -/
open Set Function MeasureTheory
open OTSelector.Probability
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {q k : ℕ}

private theorem rawCubePopulation_of_jointLaw
    {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (M : Measure Ω) [IsFiniteMeasure M] (P : Measure Z) [IsFiniteMeasure P]
    (read : Ω → Z × (Fin k → (Fin q → ℝ))) (hr : Measurable read)
    (hlaw : M.map read = P.prod (Measure.pi (fun _ : Fin k ↦ cubeMeasure (Fin q) 1)))
    (hq : 4 < q) (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) :
    Measurable (fun p ↦ originalRawCubePopulationCoupling z L (read p).2) ∧
    (∀ᵐ p ∂M, let Γ := originalRawCubePopulationCoupling z L (read p).2
      IsFiniteMeasure Γ ∧ Integrable (fun v ↦ ‖v.1-v.2‖^2) Γ ∧
      Γ.map Prod.fst = ∑ j, Measure.dirac (originalRawCubePhysicalMap z L ((read p).2 j)) ∧
      Γ.map Prod.snd = (k : ℝ≥0∞) •
        (cubeMeasure (Fin q) 1).map (originalRawCubePhysicalMap z L)) ∧
    Integrable (fun p ↦ ∫ v, ‖v.1-v.2‖^2 ∂originalRawCubePopulationCoupling z L (read p).2) M ∧
    (∫ p, ∫ v, ‖v.1-v.2‖^2 ∂originalRawCubePopulationCoupling z L (read p).2 ∂M) ≤
      M.real univ * (((q : ℝ)*L^2)*dyadicMatchingConstant q*(k : ℝ)^(1-2/(q : ℝ))) := by
  have : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  let π := Measure.pi (fun _ : Fin k ↦ cubeMeasure (Fin q) 1)
  have hp : MeasurePreserving read M (P.prod π) := ⟨hr, hlaw⟩
  have hun : M univ = P univ := by
    have h := congrArg (fun ν ↦ ν univ) hlaw
    rw [Measure.map_apply hr MeasurableSet.univ, preimage_univ] at h
    rw [← univ_prod_univ, Measure.prod_prod] at h
    simpa only [measure_univ (μ := Measure.pi (fun _ : Fin k ↦ cubeMeasure (Fin q) 1)), mul_one] using h
  have hmass : M.real univ = P.real univ := congrArg ENNReal.toReal hun
  let f : (Fin k → (Fin q → ℝ)) → ℝ := fun x ↦
    ∫ v, ‖v.1-v.2‖^2 ∂originalRawCubePopulationCoupling z L x
  have he := expected_originalRawCubePopulationCoupling_squareCost_rate (n := k) hq z L
  have hprod : Integrable (fun p : Z × (Fin k → (Fin q → ℝ)) ↦ f p.2) (P.prod π) :=
    he.1.comp_snd P
  have hmapI := hprod.aestronglyMeasurable
  rw [← hp.map_eq] at hmapI
  have heq := integral_map hr.aemeasurable hmapI
  rw [hp.map_eq] at heq
  have hunit1 : ∀ᵐ x ∂cubeMeasure (Fin q) 1, x ∈ unitCube q := by
    exact (mem_ae_iff_prob_eq_one (measurableSet_unitCube q)).2 (cubeMeasure_unitCube q)
  have hunit : ∀ᵐ x ∂π, ∀ i, x i ∈ unitCube q := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin k ↦ cubeMeasure (Fin q) 1) i).quasiMeasurePreserving.ae hunit1
  have hprodunit : ∀ᵐ p : Z × (Fin k → (Fin q → ℝ)) ∂P.prod π, ∀ i, p.2 i ∈ unitCube q := by
    apply ae_of_ae_map (μ := P.prod π) (p := fun x ↦ ∀ i, x i ∈ unitCube q)
      measurable_snd.aemeasurable
    rw [Measure.map_snd_prod]
    exact Measure.ae_smul_measure hunit _
  refine ⟨(originalRawCubePopulationCoupling_spec z L).1.comp (measurable_snd.comp hr), ?_,
    hp.integrable_comp_of_integrable hprod, ?_⟩
  · filter_upwards [hp.quasiMeasurePreserving.ae hprodunit] with p hpunit
    have h := (originalRawCubePopulationCoupling_spec z L).2 (read p).2 hpunit
    exact ⟨h.1, (originalIIDPhysicalCubePopulationCoupling_squareCost_le
      (originalNormalizedCubeLaw q) z L _).1, h.2⟩
  · calc
      _ = ∫ p : Z × (Fin k → (Fin q → ℝ)), f p.2 ∂P.prod π := heq.symm
      _ = P.real univ * ∫ x, f x ∂π := by
        simpa only [smul_eq_mul] using integral_fun_snd (μ := P) f
      _ ≤ P.real univ * (((q : ℝ)*L^2)*dyadicMatchingConstant q*(k : ℝ)^(1-2/(q : ℝ))) :=
        mul_le_mul_of_nonneg_left he.2 measureReal_nonneg
      _ = _ := by rw [hmass]

/-- The concrete reserve population plan starts at exactly the original observed
indices selected by the actual excess deletion and the independently specified class. -/
def originalReserveExcessClassPopulationCoupling
    (R : ℝ) (own other : Fin 2) (C D : Set ℝ) (k : ℕ)
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ) :=
  originalRawCubePopulationCoupling z L (originalReserveExcessClassInputReadout R own other C D k p).2

variable {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- On the actual source kept-class count fibre, the same original joined experiment
produces a true finite original-atom population plan with its sharp energy rate. -/
theorem LegalWeightedStationaryPoissonMatching.original_sourceReserveClass_populationCoupling
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (rate : ℝ≥0)
    (R : ℝ) {C D : Set ℝ} (hC : MeasurableSet C) (hD : MeasurableSet D) (k : ℕ)
    (hq : 4 < q) (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) :
    let M := (originalMainReserveExperimentLaw Q rate).restrict
      {p | (originalReserveSceneExcessClassKept R 0 1 C D
        (originalReserveExcessInputAux (originalSourceReserveExperimentSplice p))).card = k}
    let read := originalReserveExcessClassInputReadout R 0 1 C D k ∘ originalSourceReserveExperimentSplice
    let Γ := fun p ↦ originalReserveExcessClassPopulationCoupling R 0 1 C D k z L
      (originalSourceReserveExperimentSplice p)
    Measurable Γ ∧
    (∀ᵐ p ∂M, IsFiniteMeasure (Γ p) ∧ Integrable (fun v ↦ ‖v.1-v.2‖^2) (Γ p) ∧
      (Γ p).map Prod.fst = ∑ j, Measure.dirac (originalRawCubePhysicalMap z L ((read p).2 j)) ∧
      (Γ p).map Prod.snd = (k : ℝ≥0∞) •
        (cubeMeasure (Fin q) 1).map (originalRawCubePhysicalMap z L)) ∧
    Integrable (fun p ↦ ∫ v, ‖v.1-v.2‖^2 ∂Γ p) M ∧
    (∫ p, ∫ v, ‖v.1-v.2‖^2 ∂Γ p ∂M) ≤
      M.real univ * (((q : ℝ)*L^2)*dyadicMatchingConstant q*(k : ℝ)^(1-2/(q : ℝ))) := by
  have : IsProbabilityMeasure (originalMainReserveExperimentLaw Q rate) := by
    unfold originalMainReserveExperimentLaw twoMarkedCloudLaw
    infer_instance
  have : IsProbabilityMeasure (originalReserveCountMarkLaw α rate) := by
    unfold originalReserveCountMarkLaw
    infer_instance
  have hs : Measurable (originalSourceReserveExperimentSplice (q := q)) := by
    unfold originalSourceReserveExperimentSplice
    fun_prop
  exact rawCubePopulation_of_jointLaw _ _ _
    ((measurable_originalReserveExcessClassInputReadout R 0 1 hC hD k).comp hs)
    (Q.original_sourceReserveExcessClassSelection_jointLaw rate R hC hD k) hq z L

/-- The analogous target plan uses the identical original joined experiment and actual
original target indices; zero count and zero-probability fibres are included. -/
theorem LegalWeightedStationaryPoissonMatching.original_targetReserveClass_populationCoupling
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (rate : ℝ≥0)
    (R : ℝ) {C D : Set ℝ} (hC : MeasurableSet C) (hD : MeasurableSet D) (k : ℕ)
    (hq : 4 < q) (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) :
    let M := (originalMainReserveExperimentLaw Q rate).restrict
      {p | (originalReserveSceneExcessClassKept R 1 0 C D
        (originalReserveExcessInputAux (originalTargetReserveExperimentSplice p))).card = k}
    let read := originalReserveExcessClassInputReadout R 1 0 C D k ∘ originalTargetReserveExperimentSplice
    let Γ := fun p ↦ originalReserveExcessClassPopulationCoupling R 1 0 C D k z L
      (originalTargetReserveExperimentSplice p)
    Measurable Γ ∧
    (∀ᵐ p ∂M, IsFiniteMeasure (Γ p) ∧ Integrable (fun v ↦ ‖v.1-v.2‖^2) (Γ p) ∧
      (Γ p).map Prod.fst = ∑ j, Measure.dirac (originalRawCubePhysicalMap z L ((read p).2 j)) ∧
      (Γ p).map Prod.snd = (k : ℝ≥0∞) •
        (cubeMeasure (Fin q) 1).map (originalRawCubePhysicalMap z L)) ∧
    Integrable (fun p ↦ ∫ v, ‖v.1-v.2‖^2 ∂Γ p) M ∧
    (∫ p, ∫ v, ‖v.1-v.2‖^2 ∂Γ p ∂M) ≤
      M.real univ * (((q : ℝ)*L^2)*dyadicMatchingConstant q*(k : ℝ)^(1-2/(q : ℝ))) := by
  have : IsProbabilityMeasure (originalMainReserveExperimentLaw Q rate) := by
    unfold originalMainReserveExperimentLaw twoMarkedCloudLaw
    infer_instance
  have : IsProbabilityMeasure (originalReserveCountMarkLaw β rate) := by
    unfold originalReserveCountMarkLaw
    infer_instance
  have hs : Measurable (originalTargetReserveExperimentSplice (q := q)) := by
    unfold originalTargetReserveExperimentSplice
    fun_prop
  exact rawCubePopulation_of_jointLaw _ _ _
    ((measurable_originalReserveExcessClassInputReadout R 1 0 hC hD k).comp hs)
    (Q.original_targetReserveExcessClassSelection_jointLaw rate R hC hD k) hq z L

end OTSelector.Reconstruction
