import OTSelector.Reconstruction.DoublePoleFieldComparison
import OTSelector.Reconstruction.OriginalFinslerKernelRightDoublePole

/-!
# Both original Finsler endpoint kernels have internal anisotropic comparison

The same actual fixed positive residue, actual smooth remainder and exact original kernel
are retained while deriving the two-sided Loewner comparison with `I+s⁻²G`. All constants
come from the original conditional geometry. No commuting remainder, projection choice,
endpoint rank oracle or additional normalized-leg assumption is supplied.
-/

open Set Filter Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The original left kernel is internally comparable to its same actual positive pole
plus identity. The exact pole and smooth remainder remain coherent with this comparison. -/
theorem exists_original_kernel_left_pole_loewner_comparison
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) :
    ∃ ε : ℝ, ε>0 ∧ ε<D.hi-D.lo ∧
      ∃ (G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
        (R : ℝ→Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ),
      G.PosSemidef ∧ ContDiffOn ℝ ∞ R (Ioo (-ε) ε) ∧
      (∀s∈Ioo 0 ε, originalSeedKernel S w (D.lo+s)=(s^2)⁻¹•G+R s) ∧
      ∃ c : ℝ, c>0 ∧ ∃ C : ℝ, C>0 ∧ ∀s∈Ioo 0 ε,
        (originalSeedKernel S w (D.lo+s)-c•((s^2)⁻¹•G+1)).PosSemidef ∧
        (C•((s^2)⁻¹•G+1)-originalSeedKernel S w (D.lo+s)).PosSemidef := by
  obtain ⟨ε,hε,hεh,G,R,hG,hR,hpole⟩ := D.exists_original_kernel_left_positive_double_pole hF hw
  obtain ⟨κ,hκ,hK⟩ := D.exists_original_kernel_wholeSpan_uniform_lower hF hw
  have hW : ∀s∈Ioo 0 ε, (originalSeedKernel S w (D.lo+s)-κ•1).PosSemidef := by
    intro s hs
    exact hK (D.lo+s) ⟨by linarith [hs.1],by linarith [hs.2]⟩
  obtain ⟨δ,hδ,hδε,c,hc,C,hC,hcomp⟩ := exists_doublePole_field_comparison
    (W:=fun s ↦ originalSeedKernel S w (D.lo+s)) hε hκ hG hR.continuousOn hW hpole
  refine ⟨δ,hδ,hδε.trans hεh,G,R,hG,hR.mono (Ioo_subset_Ioo (by linarith) hδε.le),?_,
    c,hc,C,hC,hcomp⟩
  intro s hs
  exact hpole s ⟨hs.1,hs.2.trans hδε⟩

/-- The same internally produced comparison holds at the actual right endpoint, in its
actual inward-distance clock, with its own unchanged original positive residue. -/
theorem exists_original_kernel_right_pole_loewner_comparison
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) :
    ∃ ε : ℝ, ε>0 ∧ ε<D.hi-D.lo ∧
      ∃ (G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
        (R : ℝ→Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ),
      G.PosSemidef ∧ ContDiffOn ℝ ∞ R (Ioo (-ε) ε) ∧
      (∀s∈Ioo 0 ε, originalSeedKernel S w (D.hi-s)=(s^2)⁻¹•G+R s) ∧
      ∃ c : ℝ, c>0 ∧ ∃ C : ℝ, C>0 ∧ ∀s∈Ioo 0 ε,
        (originalSeedKernel S w (D.hi-s)-c•((s^2)⁻¹•G+1)).PosSemidef ∧
        (C•((s^2)⁻¹•G+1)-originalSeedKernel S w (D.hi-s)).PosSemidef := by
  obtain ⟨ε,hε,hεh,G,R,hG,hR,hpole⟩ := D.exists_original_kernel_right_positive_double_pole hF hw
  obtain ⟨κ,hκ,hK⟩ := D.exists_original_kernel_wholeSpan_uniform_lower hF hw
  have hW : ∀s∈Ioo 0 ε, (originalSeedKernel S w (D.hi-s)-κ•1).PosSemidef := by
    intro s hs
    exact hK (D.hi-s) ⟨by linarith [hs.2],by linarith [hs.1]⟩
  obtain ⟨δ,hδ,hδε,c,hc,C,hC,hcomp⟩ := exists_doublePole_field_comparison
    (W:=fun s ↦ originalSeedKernel S w (D.hi-s)) hε hκ hG hR.continuousOn hW hpole
  refine ⟨δ,hδ,hδε.trans hεh,G,R,hG,hR.mono (Ioo_subset_Ioo (by linarith) hδε.le),?_,
    c,hc,C,hC,hcomp⟩
  intro s hs
  exact hpole s ⟨hs.1,hs.2.trans hδε⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
