import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedKernel
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedWindowPorts

/-! Genuine class-mass preservation in the same chosen physical cube. -/
open Set Function Filter MeasureTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 600000
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Actual reflected smoothing of unchanged marked endpoints in one original clock class,
using the canonical kernel in the chosen physical orientation. -/
def originalOrientedStageReflectedClassDensity {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (C : Set ℝ) (π : Measure (LegalMarkedPhysicalPoint q)) (z : Fin q → ℝ) : ℝ :=
  ∫ p in {p | p.2 ∈ C}, originalCanonicalOrientedReflectedKernel b R z p.1 ∂π

/-- The actual physical class smoothing remains positive. -/
theorem originalOrientedStageReflectedClassDensity_nonneg {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (C : Set ℝ) (π : Measure (LegalMarkedPhysicalPoint q)) (z : Fin q → ℝ) :
    0 ≤ originalOrientedStageReflectedClassDensity b R C π z :=
  integral_nonneg (fun p ↦ originalCanonicalOrientedReflectedKernel_nonneg b R z p.1)

/-- Actual oriented reflected smoothing has exactly the original endpoint class count as
mass, on the same physical cube and with no law of selected ports as a premise. -/
theorem originalOrientedStageReflectedClassDensity_integrable_mass {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (hR : 1 ≤ R)
    (π : Measure (LegalMarkedPhysicalPoint q)) [IsFiniteMeasure π]
    (hπ : ∀ᵐ p ∂π, p.1 ∈ originalCenteredPhysicalCubeRegion b (2 * R)) (C : Set ℝ) :
    Integrable (originalOrientedStageReflectedClassDensity b R C π)
      (volume.restrict (originalCenteredPhysicalCubeRegion b (2 * R))) ∧
    (∫ z in originalCenteredPhysicalCubeRegion b (2 * R),
      originalOrientedStageReflectedClassDensity b R C π z) = π.real {p | p.2 ∈ C} := by
  let σ := π.restrict {p | p.2 ∈ C}
  let μ := volume.restrict (originalCenteredPhysicalCubeRegion b (2 * R))
  let : IsFiniteMeasure μ := ⟨by
    change (volume.restrict (originalCenteredPhysicalCubeRegion b (2 * R))) univ < ∞
    rw [Measure.restrict_apply_univ]
    exact (isCompact_originalStagePhysicalCube b (2 * R)).measure_lt_top⟩
  have hmap : Measurable (fun zp : (Fin q → ℝ) × LegalMarkedPhysicalPoint q ↦
      (zp.1, zp.2.1)) := measurable_fst.prodMk measurable_snd.fst
  have hkernel : Measurable (fun zp : (Fin q → ℝ) × LegalMarkedPhysicalPoint q ↦
      originalCanonicalOrientedReflectedKernel b R zp.1 zp.2.1) := by
    simpa only [Function.comp_def] using
      (measurable_originalCanonicalOrientedReflectedKernel b R).comp hmap
  have hprod : Integrable (fun zp : (Fin q → ℝ) × LegalMarkedPhysicalPoint q ↦
      originalCanonicalOrientedReflectedKernel b R zp.1 zp.2.1) (μ.prod σ) := by
    apply Integrable.of_bound hkernel.aestronglyMeasurable ((3 : ℝ) ^ q * originalEuclideanMollifierBound q)
    apply Eventually.of_forall
    intro zp
    simpa only [originalCanonicalOrientedReflectedKernel, Real.norm_eq_abs, Fintype.card_fin] using
      abs_originalCubeReflectedKernel_le (abs_originalEuclideanMollifier_le q) R
        ((orthonormalPhysicalCubeMap b).symm zp.1) ((orthonormalPhysicalCubeMap b).symm zp.2.1)
  refine ⟨hprod.integral_prod_left, ?_⟩
  change (∫ z, ∫ p, originalCanonicalOrientedReflectedKernel b R z p.1 ∂σ ∂μ) = _
  rw [integral_integral_swap hprod]
  have hone : (fun p ↦ ∫ z, originalCanonicalOrientedReflectedKernel b R z p.1 ∂μ) =ᵐ[σ]
      fun _ ↦ (1 : ℝ) := by
    filter_upwards [ae_restrict_of_ae hπ] with p hp
    exact integral_originalCanonicalOrientedReflectedKernel_eq_one b hR hp
  rw [integral_congr_ae hone]
  simp [σ, Measure.real]

end OTSelector.Reconstruction
