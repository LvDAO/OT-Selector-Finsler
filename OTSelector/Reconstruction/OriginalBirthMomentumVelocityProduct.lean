import OTSelector.Reconstruction.BirthMomentumVelocityProduct
import OTSelector.Reconstruction.OriginalFocalVelocityEnergy
import OTSelector.Reconstruction.OriginalMaskedOneEdgeTraffic

/-! The same actual original focal residue gives a quantitative product bound
for canonical birth momentum and literal half-open physical clock occupation. -/
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

/-- The same original left focal product holds for every strictly positive
endpoint distance up to twice the clock scale, including old-shell endpoints. -/
theorem OriginalSeedConditionalMoments.exists_original_left_focalMomentum_occupation_bound
    (D : OriginalSeedConditionalMoments S w μ ν)
    {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ η ∧ 0 < C ∧
      ∀ {t s : ℝ}, 0 < t → t ≤ 1 → 0 < s → 4 * t < ε →
      ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
        m.1.1 - (S.level : ℝ) - D.lo ∈ Ioc 0 (2 * t) →
      ∀ c : ℝ, c - (S.level : ℝ) - D.lo ∈ Icc t (4 * t) →
        ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
            originalSeedPairMomentum S w m‖ * ‖originalSeedClockOccupation S w c m‖ ≤
          C * Real.sqrt s * (originalSeedLeftPoleEnergy S w D.lo G m / t ^ 2 +
            ‖originalSeedPairMomentum S w m‖ ^ 2 / t) := by
  obtain ⟨L, hL, hGn⟩ := exists_positiveResidue_mulVec_sqrt_energy_bound hG
  obtain ⟨δ, M₀, hδ, hM, hRn⟩ := exists_matrix_remainder_norm_bound_near_zero hRem
  let A : ℝ := Real.sqrt (finrank ℝ S.covector.ker : ℝ) + Real.sqrt 2
  let Cv : ℝ := L * Real.sqrt 2 + M₀
  refine ⟨min η δ, 2 * A * Cv, lt_min hη hδ, min_le_left _ _, by dsimp [A, Cv]; positivity, ?_⟩
  intro t s ht ht1 hs htε m ha c hc
  let r : ℝ := c - (S.level : ℝ) - D.lo
  have hr0 : 0 < r := ht.trans_le hc.1
  have hrη : r < η := (hc.2.trans_lt htε).trans_le (min_le_left _ _)
  have hrδ : r < δ := (hc.2.trans_lt htε).trans_le (min_le_right _ _)
  have hvel : ‖originalSeedClockOccupation S w c m‖ ≤ Cv *
      (t ^ (-3 / 2 : ℝ) * Real.sqrt (originalSeedLeftPoleEnergy S w D.lo G m) +
        ‖originalSeedPairMomentum S w m‖) := by
    apply (norm_originalSeedClockOccupation_le_velocity S w m c).trans
    have hc_eq : c - (S.level : ℝ) = D.lo + r := by dsimp [r]; ring
    rw [hc_eq, hpole r ⟨hr0, hrη⟩]
    exact pole_velocity_le_source_energy_scale hG hL.le hM.le ht hc.1
      ha.1 ha.2 hGn (hRn r ⟨hr0, hrδ⟩) (originalSeedPairMomentum S w m)
  simpa only [A, Fintype.card_fin, originalSeedLeftPoleEnergy, originalSeedRightPoleEnergy] using
    birthNormalizer_momentum_mul_velocity_le hG ht ht1 hs
    ha.1 ha.2 (by dsimp [Cv]; positivity) (norm_nonneg _)
    (originalSeedPairMomentum S w m) hvel

/-- The actual left birth shell has its original physical momentum-occupation
product bounded by its own same-residue focal energy and unchanged full momentum. -/
theorem OriginalSeedConditionalMoments.exists_original_left_birthMomentum_occupation_bound
    (D : OriginalSeedConditionalMoments S w μ ν)
    {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ η ∧ 0 < C ∧
      ∀ {t s : ℝ}, 0 < t → t ≤ 1 → 0 < s → 4 * t < ε →
      ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
        m.1.1 - (S.level : ℝ) - D.lo ∈ Icc t (2 * t) →
      ∀ c : ℝ, c - (S.level : ℝ) - D.lo ∈ Icc t (4 * t) →
        ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
            originalSeedPairMomentum S w m‖ * ‖originalSeedClockOccupation S w c m‖ ≤
          C * Real.sqrt s * (originalSeedLeftPoleEnergy S w D.lo G m / t ^ 2 +
            ‖originalSeedPairMomentum S w m‖ ^ 2 / t) := by
  obtain ⟨ε, C, hε, hεη, hC, hbound⟩ :=
    D.exists_original_left_focalMomentum_occupation_bound hη hG hRem hpole
  refine ⟨ε, C, hε, hεη, hC, ?_⟩
  intro t s ht ht1 hs htε m ha c hc
  exact hbound ht ht1 hs htε m ⟨ht.trans_le ha.1, ha.2⟩ c hc

/-- The same original right focal product holds for every strictly positive
endpoint distance up to twice the clock scale, including old-shell endpoints. -/
theorem OriginalSeedConditionalMoments.exists_original_right_focalMomentum_occupation_bound
    (D : OriginalSeedConditionalMoments S w μ ν)
    {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ η ∧ 0 < C ∧
      ∀ {t s : ℝ}, 0 < t → t ≤ 1 → 0 < s → 4 * t < ε →
      ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
        D.hi - (m.1.2 - (S.level : ℝ)) ∈ Ioc 0 (2 * t) →
      ∀ c : ℝ, D.hi - (c - (S.level : ℝ)) ∈ Icc t (4 * t) →
        ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
            originalSeedPairMomentum S w m‖ * ‖originalSeedClockOccupation S w c m‖ ≤
          C * Real.sqrt s * (originalSeedRightPoleEnergy S w D.hi G m / t ^ 2 +
            ‖originalSeedPairMomentum S w m‖ ^ 2 / t) := by
  obtain ⟨L, hL, hGn⟩ := exists_positiveResidue_mulVec_sqrt_energy_bound hG
  obtain ⟨δ, M₀, hδ, hM, hRn⟩ := exists_matrix_remainder_norm_bound_near_zero hRem
  let A : ℝ := Real.sqrt (finrank ℝ S.covector.ker : ℝ) + Real.sqrt 2
  let Cv : ℝ := L * Real.sqrt 2 + M₀
  refine ⟨min η δ, 2 * A * Cv, lt_min hη hδ, min_le_left _ _, by dsimp [A, Cv]; positivity, ?_⟩
  intro t s ht ht1 hs htε m ha c hc
  let r : ℝ := D.hi - (c - (S.level : ℝ))
  have hr0 : 0 < r := ht.trans_le hc.1
  have hrη : r < η := (hc.2.trans_lt htε).trans_le (min_le_left _ _)
  have hrδ : r < δ := (hc.2.trans_lt htε).trans_le (min_le_right _ _)
  have hvel : ‖originalSeedClockOccupation S w c m‖ ≤ Cv *
      (t ^ (-3 / 2 : ℝ) * Real.sqrt (originalSeedRightPoleEnergy S w D.hi G m) +
        ‖originalSeedPairMomentum S w m‖) := by
    apply (norm_originalSeedClockOccupation_le_velocity S w m c).trans
    have hc_eq : c - (S.level : ℝ) = D.hi - r := by dsimp [r]; ring
    rw [hc_eq, hpole r ⟨hr0, hrη⟩]
    exact pole_velocity_le_source_energy_scale hG hL.le hM.le ht hc.1
      ha.1 ha.2 hGn (hRn r ⟨hr0, hrδ⟩) (originalSeedPairMomentum S w m)
  simpa only [A, Fintype.card_fin, originalSeedLeftPoleEnergy, originalSeedRightPoleEnergy] using
    birthNormalizer_momentum_mul_velocity_le hG ht ht1 hs
    ha.1 ha.2 (by dsimp [Cv]; positivity) (norm_nonneg _)
    (originalSeedPairMomentum S w m) hvel

/-- The actual right birth shell has the same quantitative physical product
bound with its own same-residue target energy, retaining original clock colors. -/
theorem OriginalSeedConditionalMoments.exists_original_right_birthMomentum_occupation_bound
    (D : OriginalSeedConditionalMoments S w μ ν)
    {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ η ∧ 0 < C ∧
      ∀ {t s : ℝ}, 0 < t → t ≤ 1 → 0 < s → 4 * t < ε →
      ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
        D.hi - (m.1.2 - (S.level : ℝ)) ∈ Icc t (2 * t) →
      ∀ c : ℝ, D.hi - (c - (S.level : ℝ)) ∈ Icc t (4 * t) →
        ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
            originalSeedPairMomentum S w m‖ * ‖originalSeedClockOccupation S w c m‖ ≤
          C * Real.sqrt s * (originalSeedRightPoleEnergy S w D.hi G m / t ^ 2 +
            ‖originalSeedPairMomentum S w m‖ ^ 2 / t) := by
  obtain ⟨ε, C, hε, hεη, hC, hbound⟩ :=
    D.exists_original_right_focalMomentum_occupation_bound hη hG hRem hpole
  refine ⟨ε, C, hε, hεη, hC, ?_⟩
  intro t s ht ht1 hs htε m ha c hc
  exact hbound ht ht1 hs htε m ⟨ht.trans_le ha.1, ha.2⟩ c hc
end OTSelector.Reconstruction
