import OTSelector.LinearAlgebra.Matrix.ResidueQuadraticEnergy
import OTSelector.Reconstruction.OriginalFocalFullLegScale

/-! Actual focal residue energies and local compliance domination. The residue is
the same original kernel residue, and all integration uses the physical clock. -/
open Set Function Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The actual left endpoint residue energy of the full original momentum. -/
def originalSeedLeftPoleEnergy (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (lo : ℝ) (G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) : ℝ :=
  (originalSeedPairMomentum S w m ⬝ᵥ (G *ᵥ originalSeedPairMomentum S w m)) /
    (m.1.1 - (S.level : ℝ) - lo)

/-- The actual right endpoint residue energy uses the original target clock. -/
def originalSeedRightPoleEnergy (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (hi : ℝ) (G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) : ℝ :=
  (originalSeedPairMomentum S w m ⬝ᵥ (G *ᵥ originalSeedPairMomentum S w m)) /
    (hi - (m.1.2 - (S.level : ℝ)))

/-- Original left residue energy is a Borel observable of the actual Palm mark. -/
theorem measurable_originalSeedLeftPoleEnergy (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (lo : ℝ) (G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ) :
    Measurable (originalSeedLeftPoleEnergy S w lo G) := by
  have hquad : Continuous (fun p : Fin (finrank ℝ S.covector.ker) → ℝ ↦ p ⬝ᵥ (G *ᵥ p)) := by
    unfold dotProduct Matrix.mulVec
    fun_prop
  exact (hquad.measurable.comp (measurable_originalSeedPairMomentum S hF hw)).div (by fun_prop)

/-- Original right residue energy is Borel with no truncation of the momentum. -/
theorem measurable_originalSeedRightPoleEnergy (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hi : ℝ) (G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ) :
    Measurable (originalSeedRightPoleEnergy S w hi G) := by
  have hquad : Continuous (fun p : Fin (finrank ℝ S.covector.ker) → ℝ ↦ p ⬝ᵥ (G *ᵥ p)) := by
    unfold dotProduct Matrix.mulVec
    fun_prop
  exact (hquad.measurable.comp (measurable_originalSeedPairMomentum S hF hw)).div (by fun_prop)

/-- Integrating the same original left pole on `[r,2r]` and adjoining the actual
remaining matching leg gives its residue compliance lower bound. -/
theorem OriginalSeedConditionalMoments.original_left_focal_pair_residue_lower
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {ε c : ℝ} (hεh : ε < D.hi - D.lo) (hc : 0 < c)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    (hlower : ∀ s ∈ Ioo 0 ε,
      (originalSeedKernel S w (D.lo + s) - c • ((s ^ 2)⁻¹ • G + 1)).PosSemidef)
    {r b : ℝ} (hr : 0 < r) (hrε : 2 * r < ε)
    (hb : b - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (h2r : (S.level : ℝ) + D.lo + 2 * r ≤ b) :
    (originalSeedClockCompliance S w ((S.level : ℝ) + D.lo + r) b -
      ((c / 2) * r⁻¹) • G).PosSemidef := by
  have hW : ContinuousOn (fun s ↦ originalSeedKernel S w (D.lo + s)) (Ioo 0 ε) :=
    (D.original_kernel_regular hF hw).1.comp (continuousOn_const.add continuousOn_id)
      (fun s hs ↦ ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  have hshort := (focal_positivePole_two_shortLeg_lower hc hG hr hrε hW hlower).2
  rw [originalSeedClockCompliance_leftFocal_integral] at hshort
  have ha : ((S.level : ℝ) + D.lo + r) - (S.level : ℝ) ∈ Ioo D.lo D.hi :=
    ⟨by linarith, by linarith⟩
  have hdiff := D.original_compliance_subsegment_posSemidef hF hw ha hb le_rfl
    (show (S.level : ℝ) + D.lo + r ≤ (S.level : ℝ) + D.lo + 2 * r by linarith) h2r
  have hpos : (((c / 2) * r) •
      (1 : Matrix (Fin (finrank ℝ S.covector.ker)) _ ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (show 0 ≤ (c / 2) * r by positivity)
  convert (hdiff.add hshort).add hpos using 1
  module

/-- The inward right pole controls the same original full forward compliance,
with the physical source and target unchanged. -/
theorem OriginalSeedConditionalMoments.original_right_focal_pair_residue_lower
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {ε c : ℝ} (hεh : ε < D.hi - D.lo) (hc : 0 < c)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    (hlower : ∀ s ∈ Ioo 0 ε,
      (originalSeedKernel S w (D.hi - s) - c • ((s ^ 2)⁻¹ • G + 1)).PosSemidef)
    {r a : ℝ} (hr : 0 < r) (hrε : 2 * r < ε)
    (ha : a - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (h2r : a ≤ (S.level : ℝ) + D.hi - 2 * r) :
    (originalSeedClockCompliance S w a ((S.level : ℝ) + D.hi - r) -
      ((c / 2) * r⁻¹) • G).PosSemidef := by
  have hW : ContinuousOn (fun s ↦ originalSeedKernel S w (D.hi - s)) (Ioo 0 ε) :=
    (D.original_kernel_regular hF hw).1.comp (continuousOn_const.sub continuousOn_id)
      (fun s hs ↦ ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  have hshort := (focal_positivePole_two_shortLeg_lower hc hG hr hrε hW hlower).2
  rw [originalSeedClockCompliance_rightFocal_integral] at hshort
  have hb : ((S.level : ℝ) + D.hi - r) - (S.level : ℝ) ∈ Ioo D.lo D.hi :=
    ⟨by linarith, by linarith⟩
  have hdiff := D.original_compliance_subsegment_posSemidef hF hw ha hb h2r
    (show (S.level : ℝ) + D.hi - 2 * r ≤ (S.level : ℝ) + D.hi - r by linarith) le_rfl
  have hpos : (((c / 2) * r) •
      (1 : Matrix (Fin (finrank ℝ S.covector.ker)) _ ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (show 0 ≤ (c / 2) * r by positivity)
  convert (hdiff.add hshort).add hpos using 1
  module

end OTSelector.Reconstruction
