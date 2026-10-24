import OTSelector.Reconstruction.OriginalFinslerKernelLeftDoublePole
import Mathlib.Analysis.Matrix.Order

/-!
# Positivity of the actual original focal mobility residue

The fixed residue is the right-side limit of the same positive original mobility after
multiplication by the square of the actual endpoint distance. Closedness of the positive
matrix cone proves its positivity; this is not an additional focal-residue assumption.
-/

open Set Filter Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

/-- Positivity of a genuine double-pole field forces its fixed leading residue positive
semidefinite, by taking the same actual squared-distance rescaling limit. -/
theorem posSemidef_of_positive_doublePole
    {ι : Type*} [Fintype ι] [DecidableEq ι] {ε : ℝ} (hε : 0<ε)
    {W R : ℝ→Matrix ι ι ℝ} {G : Matrix ι ι ℝ} (hR : ContinuousAt R 0)
    (hW : ∀ s∈Ioo 0 ε, (W s).PosSemidef)
    (hpole : ∀ s∈Ioo 0 ε, W s=(s^2)⁻¹•G+R s) : G.PosSemidef := by
  have hlim : Tendsto (fun s : ℝ ↦ G+s^2•R s) (𝓝[>] 0) (𝓝 G) := by
    have hcont : ContinuousAt (fun s : ℝ ↦ G+s^2•R s) 0 :=
      continuousAt_const.add ((continuousAt_id.pow 2).smul hR)
    simpa only [zero_pow (by decide : 2≠0),zero_smul,add_zero] using
      hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply Matrix.posSemidef_is_closed.mem_of_tendsto hlim
  have hupper : ∀ᶠ s in 𝓝[>] (0:ℝ), s<ε :=
    nhdsWithin_le_nhds (Iio_mem_nhds hε)
  filter_upwards [self_mem_nhdsWithin,hupper] with s hs hsε
  have hsI : s∈Ioo 0 ε := ⟨hs,hsε⟩
  have hp := (hW s hsI).smul (sq_nonneg s)
  rw [hpole s hsI,smul_add,smul_smul,mul_inv_cancel₀ (pow_ne_zero 2 (ne_of_gt hs)),one_smul] at hp
  exact hp

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The actual original fixed double-pole residue is positive semidefinite, derived from
the original kernel itself. Every original graph and endpoint regularity input is internal. -/
theorem exists_original_kernel_left_positive_double_pole
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) :
    ∃ ε : ℝ, ε>0 ∧ ε<D.hi-D.lo ∧
      ∃ (G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
        (R : ℝ→Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ),
      G.PosSemidef ∧ ContDiffOn ℝ ∞ R (Ioo (-ε) ε) ∧ ∀ s∈Ioo 0 ε,
        originalSeedKernel S w (D.lo+s)=(s^2)⁻¹•G+R s := by
  obtain ⟨ε,hε,hεh,G,R,hR,hpole⟩ := D.exists_original_kernel_left_double_pole hF hw
  refine ⟨ε,hε,hεh,G,R,?_,hR,hpole⟩
  apply posSemidef_of_positive_doublePole hε
    (hR.continuousOn.continuousAt (Ioo_mem_nhds (by linarith) hε))
    (W := fun s ↦ originalSeedKernel S w (D.lo+s)) ?_ hpole
  intro s hs
  exact ((D.original_kernel_regular hF hw).2 (D.lo+s)
    ⟨by linarith [hs.1],by linarith [hs.2]⟩).posSemidef

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
