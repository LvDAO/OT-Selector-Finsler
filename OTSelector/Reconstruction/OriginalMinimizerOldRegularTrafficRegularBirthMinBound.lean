import OTSelector.Reconstruction.OriginalMinimizerOldRegularTrafficRegularBirthBounded

/-! Bounded actual regular birth phases retain original source confinement and count domination. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
local notation "qdim" => finrank ℝ S.covector.ker
local notation "MarkClock" => PhysicalPairPalmMark (Fin qdim) × ℝ

/-- An actual compact regular strip provides the full-clock one-edge bound
with the precise sqrt(s) canonical-momentum coefficient, for arbitrary original masks. -/
theorem exists_original_regularBirth_fullClock_min_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {a b A : ℝ} (hA : 0 ≤ A)
    (ha : a-(S.level:ℝ) ∈ Ioo D.lo D.hi)
    (hb : b-(S.level:ℝ) ∈ Ioo D.lo D.hi) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ c ∈ Icc a b,
      ∀ {l r s R M₀ : ℝ}, l ≤ r → 0 < s → r-l ≤ A*s →
        (∀ v ∈ Icc l r, |v-c| ≤ δ) → 0 ≤ R → 0 ≤ M₀ →
      ∀ η : (Fin qdim → ℝ) → ℝ, (∀ x,0 ≤ η x) → (∀ x,η x ≤ M₀) →
        (∀ x,R < ‖x‖ → η x = 0) →
      ∀ mask : PhysicalPairPalmMark (Fin qdim) × ℝ → ℝ≥0∞,
        (∀ z,mask z ≤ 1) → (∀ m v,v ∉ Icc l r → mask (m,v) = 0) →
        (∀ m v,mask (m,v) ≠ 0 → m.1.1-(S.level:ℝ) ∈ Ioo D.lo D.hi) →
      ∀ x : Fin qdim → ℝ, ∀ m : PhysicalPairPalmMark (Fin qdim),
        (∫⁻ v : ℝ, ENNReal.ofReal (η (x+originalSeedPathOffset S w v m)) *
          (ENNReal.ofReal ‖originalSeedClockOccupation S w v m‖ * mask (m,v))) ≤
        ENNReal.ofReal ((4*M₀*(R+1))*min 1 ((C*Real.sqrt s)*
          ‖((positiveMatrixNormalizer (s • (1:Matrix (Fin qdim) (Fin qdim) ℝ)))ᵀ)⁻¹ *ᵥ
            originalSeedPairMomentum S w m‖)) := by
  obtain ⟨C,δ,hC,hδ,hbound⟩ := D.exists_original_regular_birth_maskedTraffic hF hw hA ha hb
  refine ⟨C,δ,hC,hδ,?_⟩
  intro c hc l r s R M₀ hlr hs hlen hwin hR hM η hη0 hηM hηR mask hm hz hsource x m
  by_cases hmI : m.1.1-(S.level:ℝ) ∈ Ioo D.lo D.hi
  · have hloc := hbound c hc hlr hs hlen hwin hR hM x m hmI η hη0 hηM hηR
      (fun v ↦ mask (m,v)) (fun v _ ↦ hm (m,v))
    have heq := setLIntegral_eq_of_ae_zero_outside (μ := (volume:Measure ℝ)) measurableSet_Icc
      (u := fun v : ℝ ↦ ENNReal.ofReal (η (x+originalSeedPathOffset S w v m)) *
        (ENNReal.ofReal ‖originalSeedClockOccupation S w v m‖ * mask (m,v)))
      (ae_of_all _ (fun v hv ↦ by rw [hz m v hv,mul_zero,mul_zero]))
    rw [← heq]
    have hloc' : (∫⁻ v in Icc l r, ENNReal.ofReal (η (x+originalSeedPathOffset S w v m)) *
        (ENNReal.ofReal ‖originalSeedClockOccupation S w v m‖ * mask (m,v))) ≤
      ENNReal.ofReal ((4*M₀*(R+1))*min 1 ((C*Real.sqrt s)*
        ‖((positiveMatrixNormalizer (s • (1:Matrix (Fin qdim) (Fin qdim) ℝ)))ᵀ)⁻¹ *ᵥ
          originalSeedPairMomentum S w m‖)) := by
      simpa only [originalSeedCompletePath_eq_anchor_add_offset,mul_assoc] using hloc
    exact hloc'
  · have hzero : ∀ v,mask (m,v) = 0 := by
      intro v
      by_contra hn
      exact hmI (hsource m v hn)
    simp only [hzero,mul_zero,lintegral_zero]
    exact zero_le


end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
