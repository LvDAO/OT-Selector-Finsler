import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockOrientedPopulationNormalized
import OTSelector.Reconstruction.OriginalStageReserveJoinedExperiment

/-! Actual original-label reserve endpoint energies on the undilated main/reserve experiment. -/

open Set Function MeasureTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- The actual source fine-class labels and RN laws, after genuine block deletion,
have their full endpoint energy bound on the original unit main law and raw reserves. -/
theorem LegalWeightedStationaryPoissonMatching.original_screening_source_atomEnergy
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {R rho : ℝ} (hR : 0 < R) (hrho : 0 ≤ rho) (hq : 4 < q)
    {S T C D : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    let K := originalCenteredPhysicalCubeRegion b (2*R)
    let rate := Real.toNNReal rho * (volume K).toNNReal
    let M := originalMainReserveExperimentLaw Q rate
    let E := originalReserveBlockClassOrientedAtomEnergy b R 0 1 S T C D ∘
      originalSourceReserveExperimentSplice
    (∀ᵐ p ∂M, OriginalReserveBlockClassOrientedAtomSpec b R 0 1 S T C D
      (originalSourceReserveExperimentSplice p)) ∧ Integrable E M ∧
      (∫ p, E p ∂M) / volume.real K ≤ (q : ℝ)*dyadicMatchingConstant q*rho^(1-2/(q : ℝ)) := by
  let K := originalCenteredPhysicalCubeRegion b (2*R)
  let rate := Real.toNNReal rho * (volume K).toNNReal
  let P := (Q.law : Measure (LegalMarkedOptimalInputScene q)).prod (markedPoissonLaw q ℝ β rate)
  have h := originalReserveBlockClassOrientedAtomLaws P α rate b hR 0 1 hS hT hC hD hq
  have hp : MeasurePreserving originalSourceReserveExperimentSplice
      (originalMainReserveExperimentLaw Q rate) (P.prod (markedPoissonLaw q ℝ α rate)) :=
    ⟨by unfold originalSourceReserveExperimentSplice; fun_prop,
      map_originalSourceReserveExperimentSplice Q rate⟩
  refine ⟨hp.quasiMeasurePreserving.ae h.1,hp.integrable_comp_of_integrable h.2.1,?_⟩
  exact (div_le_div_of_nonneg_right
    ((hp.hasLaw.integral_comp h.2.1.aestronglyMeasurable).trans_le h.2.2) measureReal_nonneg).trans_eq
      (originalReserveBlockClassOrientedPopulation_normalizedRate b hR hrho hq)

/-- The target uses the same original joint experiment, including its unchanged
original selected target indices and the same physical cube and reserve rate. -/
theorem LegalWeightedStationaryPoissonMatching.original_screening_target_atomEnergy
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {R rho : ℝ} (hR : 0 < R) (hrho : 0 ≤ rho) (hq : 4 < q)
    {S T C D : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    let K := originalCenteredPhysicalCubeRegion b (2*R)
    let rate := Real.toNNReal rho * (volume K).toNNReal
    let M := originalMainReserveExperimentLaw Q rate
    let E := originalReserveBlockClassOrientedAtomEnergy b R 1 0 S T C D ∘
      originalTargetReserveExperimentSplice
    (∀ᵐ p ∂M, OriginalReserveBlockClassOrientedAtomSpec b R 1 0 S T C D
      (originalTargetReserveExperimentSplice p)) ∧ Integrable E M ∧
      (∫ p, E p ∂M) / volume.real K ≤ (q : ℝ)*dyadicMatchingConstant q*rho^(1-2/(q : ℝ)) := by
  let K := originalCenteredPhysicalCubeRegion b (2*R)
  let rate := Real.toNNReal rho * (volume K).toNNReal
  let P := (Q.law : Measure (LegalMarkedOptimalInputScene q)).prod (markedPoissonLaw q ℝ α rate)
  have h := originalReserveBlockClassOrientedAtomLaws P β rate b hR 1 0 hS hT hC hD hq
  have hp : MeasurePreserving originalTargetReserveExperimentSplice
      (originalMainReserveExperimentLaw Q rate) (P.prod (markedPoissonLaw q ℝ β rate)) :=
    ⟨by unfold originalTargetReserveExperimentSplice; fun_prop,
      map_originalTargetReserveExperimentSplice Q rate⟩
  refine ⟨hp.quasiMeasurePreserving.ae h.1,hp.integrable_comp_of_integrable h.2.1,?_⟩
  exact (div_le_div_of_nonneg_right
    ((hp.hasLaw.integral_comp h.2.1.aestronglyMeasurable).trans_le h.2.2) measureReal_nonneg).trans_eq
      (originalReserveBlockClassOrientedPopulation_normalizedRate b hR hrho hq)

/-- Sum both actual original-label endpoint energies over a fixed finite family
of true block/fine-class selections. Each class retains its own RN laws. -/
def originalScreeningReserveEndpointEnergy {I : Type*} [Fintype I]
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (S T Cs Ct Ds Dt : I → Set ℝ)
    (p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) : ℝ :=
  ∑ i, (originalReserveBlockClassOrientedAtomEnergy b R 0 1 (S i) (T i) (Cs i) (Ds i)
      (originalSourceReserveExperimentSplice p) +
    originalReserveBlockClassOrientedAtomEnergy b R 1 0 (S i) (T i) (Ct i) (Dt i)
      (originalTargetReserveExperimentSplice p))

/-- Actual finite-family endpoint energy is integrable and uniformly bounded
per physical volume. The explicit constant is independent of rho, tilt and Q. -/
theorem LegalWeightedStationaryPoissonMatching.original_screening_reserveEndpointEnergy
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {I : Type*} [Fintype I]
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {R rho : ℝ} (hR : 0 < R) (hrho : 0 ≤ rho) (hq : 4 < q)
    (S T Cs Ct Ds Dt : I → Set ℝ)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ i, MeasurableSet (T i))
    (hCs : ∀ i, MeasurableSet (Cs i)) (hCt : ∀ i, MeasurableSet (Ct i))
    (hDs : ∀ i, MeasurableSet (Ds i)) (hDt : ∀ i, MeasurableSet (Dt i)) :
    let K := originalCenteredPhysicalCubeRegion b (2*R)
    let M := originalMainReserveExperimentLaw Q (Real.toNNReal rho * (volume K).toNNReal)
    Integrable (originalScreeningReserveEndpointEnergy b R S T Cs Ct Ds Dt) M ∧
      (∫ p, originalScreeningReserveEndpointEnergy b R S T Cs Ct Ds Dt p ∂M) / volume.real K ≤
        (2*(Fintype.card I : ℝ)*(q : ℝ)*dyadicMatchingConstant q)*rho^(1-2/(q : ℝ)) := by
  have hs (i) := Q.original_screening_source_atomEnergy b hR hrho hq (hS i) (hT i) (hCs i) (hDs i)
  have ht (i) := Q.original_screening_target_atomEnergy b hR hrho hq (hS i) (hT i) (hCt i) (hDt i)
  refine ⟨integrable_finsetSum _ (fun i _ ↦ (hs i).2.1.add (ht i).2.1),?_⟩
  unfold originalScreeningReserveEndpointEnergy
  have hsum : (∫ p, ∑ i, (originalReserveBlockClassOrientedAtomEnergy b R 0 1
      (S i) (T i) (Cs i) (Ds i) (originalSourceReserveExperimentSplice p) +
    originalReserveBlockClassOrientedAtomEnergy b R 1 0
      (S i) (T i) (Ct i) (Dt i) (originalTargetReserveExperimentSplice p))
      ∂originalMainReserveExperimentLaw Q (Real.toNNReal rho *
        (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)) =
    ∑ i, ∫ p, (originalReserveBlockClassOrientedAtomEnergy b R 0 1
      (S i) (T i) (Cs i) (Ds i) (originalSourceReserveExperimentSplice p) +
    originalReserveBlockClassOrientedAtomEnergy b R 1 0
      (S i) (T i) (Ct i) (Dt i) (originalTargetReserveExperimentSplice p))
      ∂originalMainReserveExperimentLaw Q (Real.toNNReal rho *
        (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal) :=
      integral_finsetSum _ (fun i _ ↦ (hs i).2.1.add (ht i).2.1)
  rw [hsum,Finset.sum_div]
  calc
    _ = ∑ i, ((∫ p, originalReserveBlockClassOrientedAtomEnergy b R 0 1 (S i) (T i) (Cs i) (Ds i)
        (originalSourceReserveExperimentSplice p) ∂originalMainReserveExperimentLaw Q
          (Real.toNNReal rho * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)) /
          volume.real (originalCenteredPhysicalCubeRegion b (2*R)) +
      (∫ p, originalReserveBlockClassOrientedAtomEnergy b R 1 0 (S i) (T i) (Ct i) (Dt i)
        (originalTargetReserveExperimentSplice p) ∂originalMainReserveExperimentLaw Q
          (Real.toNNReal rho * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)) /
          volume.real (originalCenteredPhysicalCubeRegion b (2*R))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun x : ℝ ↦ x / volume.real (originalCenteredPhysicalCubeRegion b (2*R)))
        (integral_add (hs i).2.1 (ht i).2.1) |>.trans (add_div _ _ _)
    _ ≤ ∑ _i : I, ((q : ℝ)*dyadicMatchingConstant q*rho^(1-2/(q : ℝ)) +
        (q : ℝ)*dyadicMatchingConstant q*rho^(1-2/(q : ℝ))) :=
      Finset.sum_le_sum fun i _ ↦ add_le_add (hs i).2.2 (ht i).2.2
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end OTSelector.Reconstruction
