import OTSelector.Reconstruction.BirthOppositeLegComparison

/-!
# Original physical source and target legs in their actual birth frame

The same actual endpoint residue is retained. The short source leg at a left
birth, or short target leg at a right death, has both normalized bounds. The
unchanged long opposite leg inherits a positive bound in this same birth frame.
-/
open Set Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Actual short source compliance and full opposite target compliance use the
same canonical birth matrix and unchanged original physical endpoints. -/
theorem original_left_birth_normalizedLegs_of_comparison
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef) {ε c C t s a r b α β : ℝ}
    (hεspan : ε < D.hi - D.lo) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hcomp : ∀ v ∈ Ioo 0 ε,
      (originalSeedKernel S w (D.lo + v) - c • ((v ^ 2)⁻¹ • G + 1)).PosSemidef ∧
      (C • ((v ^ 2)⁻¹ • G + 1) - originalSeedKernel S w (D.lo + v)).PosSemidef)
    (ht : 0 < t) (hs : 0 < s) (hst : s ≤ t) (htε : 8 * t < ε)
    (ha : t / 2 ≤ a) (har : a ≤ r) (hr : r ≤ 4 * t)
    (hlenL : α * s ≤ r - a) (hlenU : r - a ≤ β * s)
    (hb : b - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hfar : (S.level : ℝ) + D.lo + 8 * t ≤ b) :
    let T := positiveMatrixNormalizer (birthResidueScale G t s)
    IsUnit T.det ∧
      (T * originalSeedClockCompliance S w ((S.level : ℝ) + D.lo + a)
        ((S.level : ℝ) + D.lo + r) * Tᵀ - (c * α / 16) • 1).PosSemidef ∧
      ((4 * C * β) • 1 - T * originalSeedClockCompliance S w
        ((S.level : ℝ) + D.lo + a) ((S.level : ℝ) + D.lo + r) * Tᵀ).PosSemidef ∧
      (T * originalSeedClockCompliance S w ((S.level : ℝ) + D.lo + r) b * Tᵀ -
        (c / 8) • 1).PosSemidef := by
  have hW : ContinuousOn (fun v ↦ originalSeedKernel S w (D.lo + v)) (Ioo 0 ε) :=
    (D.original_kernel_regular hF hw).1.comp (continuousOn_const.add continuousOn_id)
      (fun v hv ↦ ⟨by linarith [hv.1], by linarith [hv.2]⟩)
  have hband : Icc (t / 2) (4 * t) ⊆ Ioo 0 ε := by
    intro v hv
    exact ⟨lt_of_lt_of_le (half_pos ht) hv.1, by linarith [hv.2]⟩
  have hshort := birth_normalized_shortLeg_bounds hG ht hs har ha hr hc hC hlenL hlenU
    (hW.mono hband) (fun v hv ↦ (hcomp v (hband hv)).1)
    (fun v hv ↦ (hcomp v (hband hv)).2)
  rw [originalSeedClockCompliance_leftFocal_integral] at hshort
  have hlong := positivePole_opposite_segment_lower hc ht htε hW
    (fun v hv ↦ (hcomp v hv).1)
  rw [originalSeedClockCompliance_leftFocal_integral] at hlong
  have hcut : ((S.level : ℝ) + D.lo + r) - (S.level : ℝ) ∈ Ioo D.lo D.hi :=
    ⟨by linarith, by linarith⟩
  have hdiff := D.original_compliance_subsegment_posSemidef hF hw hcut hb
    (show (S.level : ℝ) + D.lo + r ≤ (S.level : ℝ) + D.lo + 4 * t by linarith)
    (show (S.level : ℝ) + D.lo + 4 * t ≤ (S.level : ℝ) + D.lo + 8 * t by linarith) hfar
  have hfull : (originalSeedClockCompliance S w ((S.level : ℝ) + D.lo + r) b -
      (c / 8) • focalResidueScale G t).PosSemidef := by
    convert hdiff.add hlong using 1
    abel_nf
  exact ⟨(positiveMatrixNormalizer_spec (birthResidueScale_posDef (t := t) hG hs)).1,
    hshort.1, hshort.2, birth_normalized_longLeg_lower hG ht hs hst
      (div_nonneg hc (by norm_num)) hfull⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
