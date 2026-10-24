import OTSelector.Reconstruction.OriginalFocalVelocityEnergy
import OTSelector.Reconstruction.BirthResidueNormalizedMomentum
import Mathlib.LinearAlgebra.Matrix.Rank

/-! The rank-zero branch of the same original pole has no singular velocity
or focal energy. It must keep its sharper full-momentum decay in birth sums. -/
open Set Function Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false

/-- Zero finite matrix rank forces the actual residue itself to vanish. -/
theorem matrix_eq_zero_of_rank_zero {ι : Type*} [Fintype ι]
    {G : Matrix ι ι ℝ} (h : G.rank = 0) : G = 0 := by
  classical
  have hr : LinearMap.range G.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h
  have hl : G.mulVecLin = 0 := LinearMap.range_eq_bot.mp hr
  ext i j
  have hj := congrArg (fun f : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) ↦ f (Pi.single j 1) i) hl
  simpa using hj

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {w : S.covector.ker} {μ ν : Measure ℝ}

omit [BorelSpace E] in
/-- The actual left pole with zero residue rank has an internally bounded
physical kernel on a full endpoint collar. -/
theorem OriginalSeedConditionalMoments.exists_original_left_rankZero_kernel_bound
    (D : OriginalSeedConditionalMoments S w μ ν) {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hrank : G.rank = 0)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ η ∧ 0 < C ∧
      ∀ r ∈ Ioo 0 ε, ‖originalSeedKernel S w (D.lo + r)‖ ≤ C := by
  obtain ⟨δ, C, hδ, hC, hR⟩ := exists_matrix_remainder_norm_bound_near_zero hRem
  refine ⟨min η δ, C, lt_min hη hδ, min_le_left _ _, hC, fun r hr ↦ ?_⟩
  rw [hpole r ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩,
    matrix_eq_zero_of_rank_zero hrank, smul_zero, zero_add]
  exact hR r ⟨hr.1, hr.2.trans_le (min_le_right _ _)⟩

omit [BorelSpace E] in
/-- The actual right pole with zero residue rank has the same genuine regular
endpoint kernel bound, with no positive-rank assumption. -/
theorem OriginalSeedConditionalMoments.exists_original_right_rankZero_kernel_bound
    (D : OriginalSeedConditionalMoments S w μ ν) {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hrank : G.rank = 0)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ η ∧ 0 < C ∧
      ∀ r ∈ Ioo 0 ε, ‖originalSeedKernel S w (D.hi - r)‖ ≤ C := by
  obtain ⟨δ, C, hδ, hC, hR⟩ := exists_matrix_remainder_norm_bound_near_zero hRem
  refine ⟨min η δ, C, lt_min hη hδ, min_le_left _ _, hC, fun r hr ↦ ?_⟩
  rw [hpole r ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩,
    matrix_eq_zero_of_rank_zero hrank, smul_zero, zero_add]
  exact hR r ⟨hr.1, hr.2.trans_le (min_le_right _ _)⟩

omit [BorelSpace E] in
/-- The actual rank-zero original left focal energy vanishes identically. -/
theorem original_leftPoleEnergy_eq_zero_of_rank_zero
    (D : OriginalSeedConditionalMoments S w μ ν)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hrank : G.rank = 0) (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) :
    originalSeedLeftPoleEnergy S w D.lo G m = 0 := by
  simp only [originalSeedLeftPoleEnergy, matrix_eq_zero_of_rank_zero hrank,
    Matrix.zero_mulVec, dotProduct_zero, zero_div]

omit [BorelSpace E] in
/-- The actual rank-zero original right focal energy vanishes identically. -/
theorem original_rightPoleEnergy_eq_zero_of_rank_zero
    (D : OriginalSeedConditionalMoments S w μ ν)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hrank : G.rank = 0) (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) :
    originalSeedRightPoleEnergy S w D.hi G m = 0 := by
  simp only [originalSeedRightPoleEnergy, matrix_eq_zero_of_rank_zero hrank,
    Matrix.zero_mulVec, dotProduct_zero, zero_div]

end OTSelector.Reconstruction
