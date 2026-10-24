import OTSelector.LinearAlgebra.Matrix.PositiveResidueVelocity
import OTSelector.Reconstruction.OriginalFocalResidueLocalEnergy

/-! Actual original focal velocities are controlled by the same residue energy
on every physical dyadic shell. All remainder constants are produced internally. -/
open Set Function Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false

/-- A continuous actual matrix remainder has an internal finite norm bound on
one endpoint collar. -/
theorem exists_matrix_remainder_norm_bound_near_zero
    {ι : Type*} [Fintype ι] {Rem : ℝ → Matrix ι ι ℝ} (hRem : ContinuousAt Rem 0) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧ ∀ r ∈ Ioo 0 δ, ‖Rem r‖ ≤ M := by
  have hnear : ∀ᶠ r in 𝓝 (0 : ℝ), ‖Rem r‖ < ‖Rem 0‖ + 1 :=
    hRem.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨δ, ‖Rem 0‖ + 1, hδ, by positivity, fun r hr ↦ ?_⟩
  exact (hbound (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hr.1] using hr.2)).le

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {w : S.covector.ker} {μ ν : Measure ℝ}

omit [BorelSpace E] in
/-- Every actual left focal shell has physical velocity bounded by the square
root of its own same-residue energy and its unchanged full original momentum. -/
theorem OriginalSeedConditionalMoments.exists_original_left_velocity_focalEnergy_bound
    (D : OriginalSeedConditionalMoments S w μ ν)
    {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ η ∧ 0 < C ∧ ∀ {t : ℝ}, 0 < t → 2 * t < ε →
      ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
        m.1.1 - (S.level : ℝ) - D.lo ∈ Icc t (2 * t) →
        ∀ r ∈ Icc t (2 * t),
          ‖originalSeedKernel S w (D.lo + r) *ᵥ originalSeedPairMomentum S w m‖ ≤
            C * (t ^ (-3 / 2 : ℝ) * Real.sqrt (originalSeedLeftPoleEnergy S w D.lo G m) +
              ‖originalSeedPairMomentum S w m‖) := by
  obtain ⟨L, hL, hGnorm⟩ := exists_positiveResidue_mulVec_sqrt_energy_bound hG
  obtain ⟨δ, M₀, hδ, hM, hR⟩ := exists_matrix_remainder_norm_bound_near_zero hRem
  refine ⟨min η δ, L * Real.sqrt 2 + M₀, lt_min hη hδ, min_le_left _ _, by positivity, ?_⟩
  intro t ht htε m ha r hr
  have hr0 : 0 < r := ht.trans_le hr.1
  have hrη : r < η := (hr.2.trans_lt htε).trans_le (min_le_left _ _)
  have hrδ : r < δ := (hr.2.trans_lt htε).trans_le (min_le_right _ _)
  rw [hpole r ⟨hr0, hrη⟩]
  exact pole_velocity_le_source_energy_scale hG hL.le hM.le ht hr.1
    (ht.trans_le ha.1) ha.2 hGnorm (hR r ⟨hr0, hrδ⟩) (originalSeedPairMomentum S w m)

omit [BorelSpace E] in
/-- Every actual right focal shell has physical velocity bounded by the square
root of its own same-residue energy and its unchanged full original momentum. -/
theorem OriginalSeedConditionalMoments.exists_original_right_velocity_focalEnergy_bound
    (D : OriginalSeedConditionalMoments S w μ ν)
    {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ η ∧ 0 < C ∧ ∀ {t : ℝ}, 0 < t → 2 * t < ε →
      ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
        D.hi - (m.1.2 - (S.level : ℝ)) ∈ Icc t (2 * t) →
        ∀ r ∈ Icc t (2 * t),
          ‖originalSeedKernel S w (D.hi - r) *ᵥ originalSeedPairMomentum S w m‖ ≤
            C * (t ^ (-3 / 2 : ℝ) * Real.sqrt (originalSeedRightPoleEnergy S w D.hi G m) +
              ‖originalSeedPairMomentum S w m‖) := by
  obtain ⟨L, hL, hGnorm⟩ := exists_positiveResidue_mulVec_sqrt_energy_bound hG
  obtain ⟨δ, M₀, hδ, hM, hR⟩ := exists_matrix_remainder_norm_bound_near_zero hRem
  refine ⟨min η δ, L * Real.sqrt 2 + M₀, lt_min hη hδ, min_le_left _ _, by positivity, ?_⟩
  intro t ht htε m ha r hr
  have hr0 : 0 < r := ht.trans_le hr.1
  have hrη : r < η := (hr.2.trans_lt htε).trans_le (min_le_left _ _)
  have hrδ : r < δ := (hr.2.trans_lt htε).trans_le (min_le_right _ _)
  rw [hpole r ⟨hr0, hrη⟩]
  exact pole_velocity_le_source_energy_scale hG hL.le hM.le ht hr.1
    (ht.trans_le ha.1) ha.2 hGnorm (hR r ⟨hr0, hrδ⟩) (originalSeedPairMomentum S w m)

end OTSelector.Reconstruction
