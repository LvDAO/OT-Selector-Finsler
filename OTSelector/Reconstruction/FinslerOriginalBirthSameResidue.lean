import OTSelector.Reconstruction.FinslerOriginalBirthNormalizedGeometry

/-! # Birth comparison preserves the residue already used by original energy and density -/
open Set Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Any same actual left residue already obtained from the genuine physical pole
has its birth comparison produced internally; no re-selection of G is needed. -/
theorem exists_original_left_birth_comparison_sameResidue
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : ℝ} (hη : 0 < η) (hηspan : η < D.hi - D.lo)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-η) η))
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε : ℝ, 0 < ε ∧ ε < η ∧ ε < D.hi - D.lo ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ r ∈ Ioo 0 ε,
        (originalSeedKernel S w (D.lo + r) - c • ((r ^ 2)⁻¹ • G + 1)).PosSemidef ∧
        (C • ((r ^ 2)⁻¹ • G + 1) - originalSeedKernel S w (D.lo + r)).PosSemidef := by
  obtain ⟨κ, hκ, hK⟩ := D.exists_original_kernel_wholeSpan_uniform_lower hF hw
  have hW : ∀ r ∈ Ioo 0 η, (originalSeedKernel S w (D.lo + r) - κ • 1).PosSemidef := by
    intro r hr
    exact hK _ ⟨by linarith [hr.1], by linarith [hr.2]⟩
  obtain ⟨ε, hε, hεη, c, hc, C, hC, hcomp⟩ :=
    exists_doublePole_field_comparison hη hκ hG hRem hW hpole
  exact ⟨ε, hε, hεη, hεη.trans hηspan, c, C, hc, hC, hcomp⟩

/-- The same preservation holds at the actual right endpoint and keeps the original
energy, density, and short-leg geometry attached to one unchanged matrix G. -/
theorem exists_original_right_birth_comparison_sameResidue
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : ℝ} (hη : 0 < η) (hηspan : η < D.hi - D.lo)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-η) η))
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε : ℝ, 0 < ε ∧ ε < η ∧ ε < D.hi - D.lo ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ r ∈ Ioo 0 ε,
        (originalSeedKernel S w (D.hi - r) - c • ((r ^ 2)⁻¹ • G + 1)).PosSemidef ∧
        (C • ((r ^ 2)⁻¹ • G + 1) - originalSeedKernel S w (D.hi - r)).PosSemidef := by
  obtain ⟨κ, hκ, hK⟩ := D.exists_original_kernel_wholeSpan_uniform_lower hF hw
  have hW : ∀ r ∈ Ioo 0 η, (originalSeedKernel S w (D.hi - r) - κ • 1).PosSemidef := by
    intro r hr
    exact hK _ ⟨by linarith [hr.2], by linarith [hr.1]⟩
  obtain ⟨ε, hε, hεη, c, hc, C, hC, hcomp⟩ :=
    exists_doublePole_field_comparison hη hκ hG hRem hW hpole
  exact ⟨ε, hε, hεη, hεη.trans hηspan, c, C, hc, hC, hcomp⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
