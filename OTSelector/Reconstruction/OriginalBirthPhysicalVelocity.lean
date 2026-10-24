import OTSelector.Reconstruction.BirthPhysicalVelocityBound
import OTSelector.Reconstruction.OriginalFocalVelocityEnergy

/-! # Original left and right physical speed in their same birth momentum -/
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

/-- The same actual left residue produces its physical speed bound in the exact
canonical birth momentum, including zero momentum and singular residues. -/
theorem exists_original_left_birth_velocity_canonicalMomentum_bound
    {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ η ∧ 0 < C ∧
      ∀ {t s r : ℝ}, 0 < t → t ≤ 1 → 0 < s → 4 * t < ε →
        r ∈ Icc (t / 2) (4 * t) → ∀ p : Fin (finrank ℝ S.covector.ker) → ℝ,
      ‖originalSeedKernel S w (D.lo + r) *ᵥ p‖ ≤
        (C / (t * Real.sqrt s)) *
          ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ p‖ := by
  obtain ⟨L, hL, hGn⟩ := exists_positiveResidue_mulVec_sqrt_energy_bound hG
  obtain ⟨δ, M₀, hδ, hM, hRn⟩ := exists_matrix_remainder_norm_bound_near_zero hRem
  let C := (4 * L + M₀) * Real.sqrt (finrank ℝ S.covector.ker : ℝ) + 1
  refine ⟨min η δ, C, lt_min hη hδ, min_le_left _ _, by dsimp [C]; positivity, ?_⟩
  intro t s r ht ht1 hs htε hr p
  have hr0 : 0 < r := lt_of_lt_of_le (half_pos ht) hr.1
  have hrη : r < η := (hr.2.trans_lt htε).trans_le (min_le_left _ _)
  have hrδ : r < δ := (hr.2.trans_lt htε).trans_le (min_le_right _ _)
  rw [hpole r ⟨hr0, hrη⟩]
  apply (birthPole_velocity_le_canonicalMomentum hG ht ht1 hs hr.1 hL.le hM.le hGn
    (hRn r ⟨hr0, hrδ⟩) p).trans
  simp only [Fintype.card_fin]
  gcongr
  dsimp [C]
  linarith

/-- The corresponding actual right physical speed uses its unchanged residue and
canonical birth momentum, in the original forward physical clock. -/
theorem exists_original_right_birth_velocity_canonicalMomentum_bound
    {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ η ∧ 0 < C ∧
      ∀ {t s r : ℝ}, 0 < t → t ≤ 1 → 0 < s → 4 * t < ε →
        r ∈ Icc (t / 2) (4 * t) → ∀ p : Fin (finrank ℝ S.covector.ker) → ℝ,
      ‖originalSeedKernel S w (D.hi - r) *ᵥ p‖ ≤
        (C / (t * Real.sqrt s)) *
          ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ p‖ := by
  obtain ⟨L, hL, hGn⟩ := exists_positiveResidue_mulVec_sqrt_energy_bound hG
  obtain ⟨δ, M₀, hδ, hM, hRn⟩ := exists_matrix_remainder_norm_bound_near_zero hRem
  let C := (4 * L + M₀) * Real.sqrt (finrank ℝ S.covector.ker : ℝ) + 1
  refine ⟨min η δ, C, lt_min hη hδ, min_le_left _ _, by dsimp [C]; positivity, ?_⟩
  intro t s r ht ht1 hs htε hr p
  have hr0 : 0 < r := lt_of_lt_of_le (half_pos ht) hr.1
  have hrη : r < η := (hr.2.trans_lt htε).trans_le (min_le_left _ _)
  have hrδ : r < δ := (hr.2.trans_lt htε).trans_le (min_le_right _ _)
  rw [hpole r ⟨hr0, hrη⟩]
  apply (birthPole_velocity_le_canonicalMomentum hG ht ht1 hs hr.1 hL.le hM.le hGn
    (hRn r ⟨hr0, hrδ⟩) p).trans
  simp only [Fintype.card_fin]
  gcongr
  dsimp [C]
  linarith

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
