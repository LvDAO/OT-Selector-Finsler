import OTSelector.Reconstruction.OriginalFinslerRelativeFocalMobility
import OTSelector.Analysis.Calculus.ConeCurveKineticIntegral

/-!
# The actual physical focal velocities lie in a uniform cone

The original smooth-pole geometry supplies the relative mobility estimate.
An explicit positive relative window turns it into the quarter-cone estimate
for every actual original momentum, without any anisotropic coordinate loss.
-/

open Set Filter Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Relative mobility acts on the actual reference velocity of the unchanged edge. -/
theorem relative_mobility_mulVec_sub_identity (A B : Matrix ι ι ℝ) (hB : IsUnit B.det)
    (p : ι → ℝ) : (A * B⁻¹ - 1) *ᵥ (B *ᵥ p) = A *ᵥ p - B *ᵥ p := by
  let _ := Matrix.invertibleOfIsUnitDet B hB
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.mul_one]

/-- The exact relative matrix bound gives a uniform cone for every actual momentum. -/
theorem norm_mobility_velocity_sub_le (A B : Matrix ι ι ℝ) (hB : IsUnit B.det)
    (p : ι → ℝ) {δ : ℝ} (hδ : ‖A * B⁻¹ - 1‖ ≤ δ) :
    ‖A *ᵥ p - B *ᵥ p‖ ≤ δ * ‖B *ᵥ p‖ := by
  rw [← relative_mobility_mulVec_sub_identity A B hB p]
  exact (Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul_of_nonneg_right hδ (norm_nonneg _))

/-- A strictly positive relative clock fraction producing the physical quarter cone. -/
def physicalConeWindowFraction (C : ℝ) : ℝ := min (1 / 2) (1 / (4 * (C + 1)))

theorem physicalConeWindowFraction_spec {C : ℝ} (hC : 0 ≤ C) :
    0 < physicalConeWindowFraction C ∧ physicalConeWindowFraction C ≤ 1 / 2 ∧
      C * physicalConeWindowFraction C ≤ 1 / 4 := by
  have hden : 0 < 4 * (C + 1) := by positivity
  have hpos : 0 < 1 / (4 * (C + 1)) := one_div_pos.mpr hden
  have hmul : (1 / (4 * (C + 1))) * (4 * (C + 1)) = 1 := by field_simp
  have hsmall : C * (1 / (4 * (C + 1))) ≤ 1 / 4 := by nlinarith
  exact ⟨lt_min (by norm_num) hpos, min_le_left _ _,
    (mul_le_mul_of_nonneg_left (min_le_right _ _) hC).trans hsmall⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- Actual original left focal velocities share a fixed physical cone on short relative bands. -/
theorem exists_original_left_focal_physicalVelocityCone
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ∃ η : ℝ, η > 0 ∧ η < D.hi - D.lo ∧ ∃ σ : ℝ, σ > 0 ∧ σ ≤ 1 / 2 ∧
      ∀ a ∈ Ioo (0 : ℝ) η, ∀ s : ℝ, |s - a| ≤ σ * a →
        ∀ p : Fin (finrank ℝ S.covector.ker) → ℝ,
          ‖originalSeedKernel S w (D.lo + s) *ᵥ p -
            originalSeedKernel S w (D.lo + a) *ᵥ p‖ ≤
              ‖originalSeedKernel S w (D.lo + a) *ᵥ p‖ / 4 := by
  obtain ⟨η,hη,hηspan,C,hC,hbound⟩ :=
    D.exists_original_left_focal_relative_mobility_bound hF hw
  let σ := physicalConeWindowFraction C
  have hσ := physicalConeWindowFraction_spec hC.le
  refine ⟨η,hη,hηspan,σ,hσ.1,hσ.2.1,?_⟩
  intro a ha s hs p
  have hunit := ((D.original_kernel_regular hF hw).2 (D.lo + a)
    (show D.lo + a ∈ Ioo D.lo D.hi from ⟨by linarith [ha.1],by linarith [ha.2]⟩)).isUnit
  have hh := norm_mobility_velocity_sub_le _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit) p
    (hbound a ha σ ⟨hσ.1.le,hσ.2.1⟩ s hs)
  apply hh.trans
  calc
    _ ≤ (1 / 4 : ℝ) * ‖originalSeedKernel S w (D.lo + a) *ᵥ p‖ :=
      mul_le_mul_of_nonneg_right hσ.2.2 (norm_nonneg _)
    _ = _ := by ring

/-- The same original physical cone is available at the right focal endpoint. -/
theorem exists_original_right_focal_physicalVelocityCone
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ∃ η : ℝ, η > 0 ∧ η < D.hi - D.lo ∧ ∃ σ : ℝ, σ > 0 ∧ σ ≤ 1 / 2 ∧
      ∀ a ∈ Ioo (0 : ℝ) η, ∀ s : ℝ, |s - a| ≤ σ * a →
        ∀ p : Fin (finrank ℝ S.covector.ker) → ℝ,
          ‖originalSeedKernel S w (D.hi - s) *ᵥ p -
            originalSeedKernel S w (D.hi - a) *ᵥ p‖ ≤
              ‖originalSeedKernel S w (D.hi - a) *ᵥ p‖ / 4 := by
  obtain ⟨η,hη,hηspan,C,hC,hbound⟩ :=
    D.exists_original_right_focal_relative_mobility_bound hF hw
  let σ := physicalConeWindowFraction C
  have hσ := physicalConeWindowFraction_spec hC.le
  refine ⟨η,hη,hηspan,σ,hσ.1,hσ.2.1,?_⟩
  intro a ha s hs p
  have hunit := ((D.original_kernel_regular hF hw).2 (D.hi - a)
    (show D.hi - a ∈ Ioo D.lo D.hi from ⟨by linarith [ha.2],by linarith [ha.1]⟩)).isUnit
  have hh := norm_mobility_velocity_sub_le _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit) p
    (hbound a ha σ ⟨hσ.1.le,hσ.2.1⟩ s hs)
  apply hh.trans
  calc
    _ ≤ (1 / 4 : ℝ) * ‖originalSeedKernel S w (D.hi - a) *ᵥ p‖ :=
      mul_le_mul_of_nonneg_right hσ.2.2 (norm_nonneg _)
    _ = _ := by ring

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
