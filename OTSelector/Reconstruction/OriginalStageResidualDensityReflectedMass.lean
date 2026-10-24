import OTSelector.Reconstruction.OriginalCubeTraceCompactnessReflectedKernelMass
import OTSelector.Reconstruction.OriginalRetainedSlabResidualReflectedEndpoints
import OTSelector.Reconstruction.OriginalRetainedSlabResidualReadouts
import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonReserveClockSlack

/-! Literal reflected class densities preserve the original marked endpoint counts. -/
open Set Function Filter MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Reflected smoothing of the actual marked endpoints in one unchanged scalar clock class. -/
def originalStageReflectedClassDensity {q : ℕ} (η : (Fin q → ℝ) → ℝ) (R : ℝ)
    (C : Set ℝ) (π : Measure (LegalMarkedPhysicalPoint q)) (z : Fin q → ℝ) : ℝ :=
  ∫ p in {p | p.2 ∈ C}, originalCubeReflectedKernel η R z p.1 ∂π

/-- The literal smoothed class density is nonnegative for a nonnegative original kernel. -/
theorem originalStageReflectedClassDensity_nonneg {q : ℕ}
    {η : (Fin q → ℝ) → ℝ} (hη : ∀ x, 0 ≤ η x) (R : ℝ)
    (C : Set ℝ) (π : Measure (LegalMarkedPhysicalPoint q)) (z : Fin q → ℝ) :
    0 ≤ originalStageReflectedClassDensity η R C π z :=
  integral_nonneg (fun p ↦ originalCubeReflectedKernel_nonneg hη R z p.1)

/-- On an actual finite marked endpoint measure the reflected class density is genuinely
integrable and has exactly its original class count as total mass. -/
theorem originalStageReflectedClassDensity_integrable_mass {q : ℕ}
    {η : (Fin q → ℝ) → ℝ} (hη : Measurable η) (hηI : Integrable η volume)
    (hηone : ∫ x, η x = 1) (hηsupport : ∀ x, 1 ≤ ‖x‖ → η x = 0)
    (hηeven : ∀ v w : Fin q → ℝ, (∀ i, |v i| = |w i|) → η v = η w)
    {M R : ℝ} (hηM : ∀ x, |η x| ≤ M) (hR : 1 ≤ R)
    (π : Measure (LegalMarkedPhysicalPoint q)) [IsFiniteMeasure π]
    (hπ : ∀ᵐ p ∂π, p.1 ∈ haarRootCube (Fin q) R) (C : Set ℝ) :
    Integrable (originalStageReflectedClassDensity η R C π)
      (volume.restrict (haarRootCube (Fin q) R)) ∧
    (∫ z in haarRootCube (Fin q) R, originalStageReflectedClassDensity η R C π z) =
      π.real {p | p.2 ∈ C} := by
  let σ := π.restrict {p | p.2 ∈ C}
  let μ := volume.restrict (haarRootCube (Fin q) R)
  have : IsFiniteMeasure μ := ⟨by
    change (volume.restrict (haarRootCube (Fin q) R)) univ < ∞
    rw [Measure.restrict_apply_univ]
    exact isCompact_Icc.measure_lt_top⟩
  have hkernel : Measurable (fun zp : (Fin q → ℝ) × LegalMarkedPhysicalPoint q ↦
      originalCubeReflectedKernel η R zp.1 zp.2.1) :=
    (measurable_originalCubeReflectedKernel hη R).comp (measurable_fst.prodMk measurable_snd.fst)
  have hprod : Integrable (fun zp : (Fin q → ℝ) × LegalMarkedPhysicalPoint q ↦
      originalCubeReflectedKernel η R zp.1 zp.2.1) (μ.prod σ) := by
    apply Integrable.of_bound hkernel.aestronglyMeasurable ((3 : ℝ) ^ q * M)
    apply Eventually.of_forall
    intro zp
    simpa only [Real.norm_eq_abs, Fintype.card_fin] using
      abs_originalCubeReflectedKernel_le hηM R zp.1 zp.2.1
  refine ⟨hprod.integral_prod_left, ?_⟩
  change (∫ z, ∫ p, originalCubeReflectedKernel η R z p.1 ∂σ ∂μ) = _
  rw [integral_integral_swap hprod]
  have hone : (fun p ↦ ∫ z, originalCubeReflectedKernel η R z p.1 ∂μ) =ᵐ[σ]
      fun _ ↦ (1 : ℝ) := by
    filter_upwards [ae_restrict_of_ae hπ] with p hp
    exact integral_originalCubeReflectedKernel_eq_one hηI hηone hηsupport hηeven hR hp
  rw [integral_congr_ae hone]
  simp [σ, Measure.real]

end OTSelector.Reconstruction
