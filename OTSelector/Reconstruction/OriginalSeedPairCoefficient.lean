import OTSelector.Reconstruction.OriginalSeedCompliance
import OTSelector.Geometry.Finsler.SeedKernelMeasurabilityIntegral
import OTSelector.Geometry.FinslerIntrinsicCostCoefficient

/-!
# The actual pair coefficient and its inverse moments

The original positive length kernel has positive definite compliance on every
strictly ordered interior pair. Its inverse is the actual quadratic-distance
coefficient, and inversion recovers exactly the compliance controlled by the
original conditional moment theorem.
-/

open Set Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Geometry ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

/-- Integrating a continuous positive definite matrix over a nonempty interval
gives a positive definite matrix, including in the zero-dimensional case. -/
theorem posDef_intervalIntegral {n : Type*} [Fintype n] [DecidableEq n]
    {K : ℝ → Matrix n n ℝ} {a b : ℝ} (hab : a < b)
    (hK : ContinuousOn K (Icc a b)) (hpos : ∀ t ∈ Icc a b, (K t).PosDef) :
    (∫ t in a..b, K t).PosDef := by
  have hsemi := posSemidef_intervalIntegral hab.le (fun t ht ↦ (hpos t ht).posSemidef)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hsemi.isHermitian
  intro v hv
  let L : Matrix n n ℝ →ₗ[ℝ] ℝ := {
    toFun := fun A ↦ star v ⬝ᵥ (A *ᵥ v)
    map_add' := fun A B ↦ by simp only [add_mulVec, dotProduct_add]
    map_smul' := fun c A ↦ by simp only [smul_mulVec, dotProduct_smul, RingHom.id_apply] }
  let Lc := L.toContinuousLinearMap
  change 0 < Lc (∫ t in a..b, K t)
  have hKi : IntervalIntegrable K volume a b :=
    (show ContinuousOn K (uIcc a b) by
      simpa only [uIcc_of_le hab.le] using hK).intervalIntegrable
  rw [← Lc.intervalIntegral_comp_comm hKi]
  exact intervalIntegral.integral_pos hab (Lc.continuous.comp_continuousOn hK)
    (fun t ht ↦ (hpos t (Ioc_subset_Icc_self ht)).dotProduct_mulVec_pos hv |>.le)
    ⟨a, left_mem_Icc.mpr hab.le, (hpos a (left_mem_Icc.mpr hab.le)).dotProduct_mulVec_pos hv⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual matrix coefficient of the original scalar pair in the fixed label basis. -/
def originalSeedPairCoefficient (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (p : ℝ × ℝ) :
    Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ :=
  (∫ t in (p.1 - S.level)..(p.2 - S.level), originalSeedKernel S w t)⁻¹

/-- The same scalar coefficient is Borel in both original potential times. -/
theorem measurable_originalSeedPairCoefficient (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex) {w : S.covector.ker} (hw : w ∈ S.labels) :
    Measurable (originalSeedPairCoefficient S w) :=
  S.measurable_familyLabelScalarCoefficient hF (Module.finBasis ℝ S.covector.ker)
    (w := fun _ : ℝ × ℝ ↦ (⟨w, hw⟩ : S.labels)) measurable_const measurable_fst measurable_snd

namespace OriginalSeedConditionalMoments

variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

omit [BorelSpace E] in
/-- Every legal interior pair has positive definite actual compliance and coefficient. -/
theorem pair_compliance_posDef (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {x y : ℝ} (hx : x - S.level ∈ Ioo D.lo D.hi)
    (hy : y - S.level ∈ Ioo D.lo D.hi) (hxy : x < y) :
    (∫ t in (x - S.level)..(y - S.level), originalSeedKernel S w t).PosDef ∧
      (originalSeedPairCoefficient S w (x, y)).PosDef := by
  have hsub : Icc (x - S.level) (y - S.level) ⊆ Ioo D.lo D.hi :=
    Icc_subset_Ioo hx.1 hy.2
  have hK := D.original_kernel_regular hF hw
  have hp := posDef_intervalIntegral (sub_lt_sub_right hxy _) (hK.1.mono hsub)
    (fun t ht ↦ hK.2 t (hsub ht))
  exact ⟨hp, hp.inv⟩

omit [BorelSpace E] in
/-- The inverse of the true quadratic coefficient is exactly the original pair compliance. -/
theorem inverse_pair_coefficient_eq (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {x y : ℝ} (hx : x - S.level ∈ Ioo D.lo D.hi)
    (hy : y - S.level ∈ Ioo D.lo D.hi) (hxy : x < y) :
    (originalSeedPairCoefficient S w (x, y))⁻¹ =
      ∫ t in (x - S.level)..(y - S.level), originalSeedKernel S w t := by
  let := (D.pair_compliance_posDef hF hw hx hy hxy).1.isUnit.invertible
  exact Matrix.inv_inv_of_invertible _

omit [BorelSpace E] in
/-- Inverse coefficients have the same finite moment bound for every legal paired law. -/
theorem paired_inverse_coefficient_moments
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {root : ℝ} (hroot : root ∈ Ioo D.lo D.hi)
    {π : Measure (ℝ × ℝ)} (hπ : Vlasov.IsCoupling π μ ν)
    (hforward : ∀ᵐ p ∂π, p.1 < p.2)
    {r : ℝ} (hr0 : 0 < r) (hr2 : r < 2) :
    Integrable (fun p ↦ ‖(originalSeedPairCoefficient S w p)⁻¹‖ ^ r) π ∧
      (∫ p, ‖(originalSeedPairCoefficient S w p)⁻¹‖ ^ r ∂π) ≤
        (2 : ℝ) ^ max (r - 1) 0 *
          ((∫ x, ‖∫ t in root..(x - S.level), originalSeedKernel S w t‖ ^ r ∂μ) +
            ∫ y, ‖∫ t in root..(y - S.level), originalSeedKernel S w t‖ ^ r ∂ν) := by
  have ha : ∀ᵐ p ∂π, p.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
    apply (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_Ioo.preimage (measurable_id.sub_const _))).mp
    rw [hπ.1]
    exact D.support.source.ae_open
  have hb : ∀ᵐ p ∂π, p.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
    apply (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_Ioo.preimage (measurable_id.sub_const _))).mp
    rw [hπ.2]
    exact D.support.target.ae_open
  have heq : (fun p : ℝ × ℝ ↦ ‖(originalSeedPairCoefficient S w p)⁻¹‖ ^ r) =ᵐ[π]
      (fun p ↦ ‖∫ t in (p.1 - S.level)..(p.2 - S.level), originalSeedKernel S w t‖ ^ r) := by
    filter_upwards [ha, hb, hforward] with p ha hb hp
    rw [D.inverse_pair_coefficient_eq hF hw ha hb hp]
  have hm := D.paired_original_compliance_moments hF hw hroot hπ hr0 hr2
  exact ⟨hm.1.congr heq.symm, (integral_congr_ae heq).symm ▸ hm.2⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
