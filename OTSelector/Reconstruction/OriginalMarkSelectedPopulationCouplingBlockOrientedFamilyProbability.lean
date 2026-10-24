import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockOrientedFamily

/-! The true original Poisson sampler produces the global kept-label RN family. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
namespace OriginalReserveFineBlockPartition
variable {q : ℕ} {B I : Type*} [Fintype B] [Fintype I]
  (H : OriginalReserveFineBlockPartition B I)

/-- The genuine auxiliary × own original Poisson law supplies the whole
global original-label family, with no family, selected-law or rate callback.
The rate is arbitrary, including zero and values above one. -/
theorem atomLaws
    (P : Measure (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ)) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (rate : ℝ≥0)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (hR : 0 < R)
    (own other : Fin 2) (hq : 4 < q) :
    let M := P.prod (markedPoissonLaw q ℝ μ rate)
    (∀ᵐ p ∂M, H.AtomSpec b R own other p) ∧
      Integrable (H.atomEnergy b R own other) M ∧
      (∫ p, H.atomEnergy b R own other p ∂M) ≤
        (Fintype.card I : ℝ)*(((q : ℝ)*(2*R)^2)*dyadicMatchingConstant q*(rate : ℝ)^(1-2/(q : ℝ))) := by
  let M := P.prod (markedPoissonLaw q ℝ μ rate)
  let E := fun i ↦ originalReserveBlockClassOrientedAtomEnergy b R own other
    (H.blockCell (H.blockFor i)) (H.oppositeCell (H.blockFor i)) (H.deletionCell (H.blockFor i)) (H.fineCell i)
  have hf (i) := originalReserveBlockClassOrientedAtomLaws P μ rate b hR own other
    (H.measurable_block (H.blockFor i)) (H.measurable_opposite (H.blockFor i))
    (H.measurable_deletion (H.blockFor i)) (H.measurable_fine i) hq
  have he : (H.atomEnergy b R own other) = fun p ↦ ∑ i, E i p :=
    funext (H.atomEnergy_eq_sum b R own other)
  have hi : Integrable (fun p ↦ ∑ i, E i p) M :=
    integrable_finsetSum _ (fun i _ ↦ (hf i).2.1)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [ae_all_iff.mpr (fun i ↦ (hf i).1)] with p hp
    exact H.atomSpec_of_fineSpecs b R own other p hp
  · rw [he]
    exact hi
  · rw [he, integral_finsetSum _ (fun i _ ↦ (hf i).2.1)]
    calc
      _ ≤ ∑ _ : I, (((q : ℝ)*(2*R)^2)*dyadicMatchingConstant q*(rate : ℝ)^(1-2/(q : ℝ))) :=
        Finset.sum_le_sum (fun i _ ↦ (hf i).2.2)
      _ = _ := by simp [nsmul_eq_mul]

/-- At the actual rate λV, the original global family has a uniform true
per-volume budget; λ may be any nonnegative real number. -/
theorem atomLaws_normalized
    (P : Measure (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ)) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {R ρ : ℝ} (hR : 0 < R) (hρ : 0 ≤ ρ) (own other : Fin 2) (hq : 4 < q) :
    let K := originalCenteredPhysicalCubeRegion b (2*R)
    let M := P.prod (markedPoissonLaw q ℝ μ (Real.toNNReal ρ*(volume K).toNNReal))
    (∀ᵐ p ∂M, H.AtomSpec b R own other p) ∧
      Integrable (H.atomEnergy b R own other) M ∧
      (∫ p, H.atomEnergy b R own other p ∂M) / volume.real K ≤
        (Fintype.card I : ℝ)*((q : ℝ)*dyadicMatchingConstant q*ρ^(1-2/(q : ℝ))) := by
  have h := H.atomLaws P μ (Real.toNNReal ρ *
    (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal) b hR own other hq
  refine ⟨h.1, h.2.1, ?_⟩
  exact (div_le_div_of_nonneg_right h.2.2 measureReal_nonneg).trans_eq
    ((mul_div_assoc _ _ _).trans (congrArg (fun t ↦ (Fintype.card I : ℝ)*t)
      (originalReserveBlockClassOrientedPopulation_normalizedRate b hR hρ hq)))

end OriginalReserveFineBlockPartition
end OTSelector.Reconstruction
