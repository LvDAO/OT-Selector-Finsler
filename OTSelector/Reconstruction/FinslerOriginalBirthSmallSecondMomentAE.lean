import OTSelector.Reconstruction.FinslerOriginalBirthConfinedTrafficAELtwo
import OTSelector.Reconstruction.OriginalBirthNormalizerQuadraticMomentReal
import OTSelector.Probability.BirthConfinedQuadraticPower

/-! The literal actual bounded-phase birth traffic has its exact dyadic
second small-phase energy powers, after true-Palm finiteness, canonical moment
and physical Haar volume are all produced for the same fixed residue. -/
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

/-- The actual left bounded-phase birth traffic has its literal L2 bound;
the physical `sqrt s/t` one-edge coefficient and true momentum moment are internal. -/
theorem OriginalSeedConditionalMoments.exists_original_left_birthBand_smallSecondMoment_bound_ae
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 0 < finrank ℝ S.covector.ker) (R : ℝ)
    {η : ℝ} (hη : 0 < η) (hηspan : η < D.hi - D.lo)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-η) η))
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ η ∧ 0 < C ∧
    ∀ {gap diameter : ℝ}, 0 < gap → ConditionalClockSupportBounds μ ν gap diameter →
    ∀ {g : ℝ → ℝ → ℝ},
    ∀ (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g),
    ∀ {t s A M₀ K : ℝ}, 0 < t → t ≤ 1 → 0 < s → 4 * t < ε →
      0 ≤ A → 0 ≤ M₀ → 0 ≤ K →
    ∀ {J : Set ℝ}, MeasurableSet J → volume J ≤ ENNReal.ofReal (A * s) →
      (∀ c ∈ J, c - (S.level : ℝ) - D.lo ∈ Icc (t / 2) (4 * t)) →
    ∀ {h : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞}, Measurable h →
      (∀ x, h x ≤ ENNReal.ofReal M₀) →
    ∀ (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞),
      Measurable mask → (∀ z, mask z ≤ 1) → (∀ m c, c ∉ J → mask (m, c) = 0) →
    ∀ {Bad : Set (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))}, MeasurableSet Bad →
    ∀ {B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))}, MeasurableSet B →
      (∀ m ∈ B, m.1.1 - (S.level : ℝ) - D.lo ∈ Icc t (2 * t)) →
    ∀ (V : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) →
      Set ((Fin (finrank ℝ S.covector.ker) → ℝ) × PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))),
      (∀ z, MeasurableSet (V z)) →
    let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      originalSeedPathOffset S w z.2 z.1
    let f := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z
    (∀ᵐ z ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))), z ∉ Bad →
      (∀ a ∈ V z, a.1 ∈ birthTrafficSpatialWindow G t s R ∧ a.2 ∈ B) ∧
      physicalScenePairKernel z.1 (V z) ≤ ENNReal.ofReal K ∧
      (∀ᵐ a ∂physicalScenePairKernel z.1, a ∉ V z →
        (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) = 0)) →
    MemLp (Badᶜ.indicator (fun z ↦
      (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker) d h f z).toReal)) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
    (∫ z, (Badᶜ.indicator (fun y ↦
      (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker) d h f y).toReal) z) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
      (K * (M₀ * A) ^ 2 * C) * s ^ 2 *
        (t ^ (-(G.rank : ℝ) - 4) *
          (∫⁻ m in B, ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal +
        t ^ (-(G.rank : ℝ) - 3) *
          (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal) := by
  have hRem0 : ContinuousAt Rem 0 :=
    hRem.continuousAt (Ioo_mem_nhds (by linarith) hη)
  obtain ⟨ε, C₀, hε, hεη, hC₀, hbound⟩ :=
    D.exists_original_left_birthConfinedTraffic_memLp_two_ae hF hw hη hG hRem0 hpole
  obtain ⟨Cv, hCv, hvolbound⟩ := exists_birthTrafficSpatialWindow_volume_bound hG
    (by simpa using hq) R
  refine ⟨ε, C₀ ^ 2 * Cv * ((finrank ℝ S.covector.ker : ℝ) + 2), hε, hεη,
    by positivity, fun {gap diameter} hgap hbounds {g} Q {t s A M₀ K}
    ht ht1 hs htε hA hM hK {J} hJ hvol hclock {h} hh hhM mask hm hm1 hz
    {Bad} hBad {B} hB ha V hV ↦ ?_⟩
  dsimp only
  intro hdata
  obtain ⟨hLp, hmean⟩ := hbound hgap hbounds Q ht ht1 hs htε hA hM hK hJ hvol
    hclock hh hhM mask hm hm1 hz hBad hB V hV hdata
  have hwreal : (volume (birthTrafficSpatialWindow G t s R)).toReal ≤
      Cv * (t ^ (G.rank + 1))⁻¹ := by
    have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hvolbound ht ht1 hs)
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ Cv * (t ^ (G.rank + 1))⁻¹ by positivity)] using hb
  have hzreal := D.original_left_birthNormalizer_quadraticMoment_toReal_le hF hw hη hηspan
    hG hRem hpole hgap hbounds Q ht hs hB ha
  have hp := OTSelector.Probability.birthConfined_quadratic_power_bound
    (C := M₀ * A * C₀) ht hs hCv.le hK ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg hwreal hzreal
  refine ⟨hLp, hmean.trans (hp.trans_eq ?_)⟩
  ring

/-- The actual right bounded-phase birth traffic has its literal L2 bound;
the physical `sqrt s/t` one-edge coefficient and true momentum moment are internal. -/
theorem OriginalSeedConditionalMoments.exists_original_right_birthBand_smallSecondMoment_bound_ae
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 0 < finrank ℝ S.covector.ker) (R : ℝ)
    {η : ℝ} (hη : 0 < η) (hηspan : η < D.hi - D.lo)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-η) η))
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ η ∧ 0 < C ∧
    ∀ {gap diameter : ℝ}, 0 < gap → ConditionalClockSupportBounds μ ν gap diameter →
    ∀ {g : ℝ → ℝ → ℝ},
    ∀ (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g),
    ∀ {t s A M₀ K : ℝ}, 0 < t → t ≤ 1 → 0 < s → 4 * t < ε →
      0 ≤ A → 0 ≤ M₀ → 0 ≤ K →
    ∀ {J : Set ℝ}, MeasurableSet J → volume J ≤ ENNReal.ofReal (A * s) →
      (∀ c ∈ J, D.hi - (c - (S.level : ℝ)) ∈ Icc (t / 2) (4 * t)) →
    ∀ {h : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞}, Measurable h →
      (∀ x, h x ≤ ENNReal.ofReal M₀) →
    ∀ (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞),
      Measurable mask → (∀ z, mask z ≤ 1) → (∀ m c, c ∉ J → mask (m, c) = 0) →
    ∀ {Bad : Set (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))}, MeasurableSet Bad →
    ∀ {B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))}, MeasurableSet B →
      (∀ m ∈ B, D.hi - (m.1.2 - (S.level : ℝ)) ∈ Icc t (2 * t)) →
    ∀ (V : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) →
      Set ((Fin (finrank ℝ S.covector.ker) → ℝ) × PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))),
      (∀ z, MeasurableSet (V z)) →
    let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      originalSeedPathOffset S w z.2 z.1
    let f := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z
    (∀ᵐ z ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))), z ∉ Bad →
      (∀ a ∈ V z, a.1 + a.2.2 ∈ birthTrafficSpatialWindow G t s R ∧ a.2 ∈ B) ∧
      physicalScenePairKernel z.1 (V z) ≤ ENNReal.ofReal K ∧
      (∀ᵐ a ∂physicalScenePairKernel z.1, a ∉ V z →
        (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) = 0)) →
    MemLp (Badᶜ.indicator (fun z ↦
      (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker) d h f z).toReal)) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
    (∫ z, (Badᶜ.indicator (fun y ↦
      (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker) d h f y).toReal) z) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
      (K * (M₀ * A) ^ 2 * C) * s ^ 2 *
        (t ^ (-(G.rank : ℝ) - 4) *
          (∫⁻ m in B, ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal +
        t ^ (-(G.rank : ℝ) - 3) *
          (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal) := by
  have hRem0 : ContinuousAt Rem 0 :=
    hRem.continuousAt (Ioo_mem_nhds (by linarith) hη)
  obtain ⟨ε, C₀, hε, hεη, hC₀, hbound⟩ :=
    D.exists_original_right_birthConfinedTraffic_memLp_two_ae hF hw hη hG hRem0 hpole
  obtain ⟨Cv, hCv, hvolbound⟩ := exists_birthTrafficSpatialWindow_volume_bound hG
    (by simpa using hq) R
  refine ⟨ε, C₀ ^ 2 * Cv * ((finrank ℝ S.covector.ker : ℝ) + 2), hε, hεη,
    by positivity, fun {gap diameter} hgap hbounds {g} Q {t s A M₀ K}
    ht ht1 hs htε hA hM hK {J} hJ hvol hclock {h} hh hhM mask hm hm1 hz
    {Bad} hBad {B} hB ha V hV ↦ ?_⟩
  dsimp only
  intro hdata
  obtain ⟨hLp, hmean⟩ := hbound hgap hbounds Q ht ht1 hs htε hA hM hK hJ hvol
    hclock hh hhM mask hm hm1 hz hBad hB V hV hdata
  have hwreal : (volume (birthTrafficSpatialWindow G t s R)).toReal ≤
      Cv * (t ^ (G.rank + 1))⁻¹ := by
    have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hvolbound ht ht1 hs)
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ Cv * (t ^ (G.rank + 1))⁻¹ by positivity)] using hb
  have hzreal := D.original_right_birthNormalizer_quadraticMoment_toReal_le hF hw hη hηspan
    hG hRem hpole hgap hbounds Q ht hs hB ha
  have hp := OTSelector.Probability.birthConfined_quadratic_power_bound
    (C := M₀ * A * C₀) ht hs hCv.le hK ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg hwreal hzreal
  refine ⟨hLp, hmean.trans (hp.trans_eq ?_)⟩
  ring

end OTSelector.Reconstruction
