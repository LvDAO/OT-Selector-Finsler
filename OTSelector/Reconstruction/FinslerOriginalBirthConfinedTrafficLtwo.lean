import OTSelector.Reconstruction.FinslerOriginalSourceConfinedTrafficLtwo
import OTSelector.Reconstruction.BirthTrafficSourceWindowVolume
import OTSelector.Reconstruction.FinslerOriginalBirthMaskedTraffic

/-! The actual same-residue physical one-edge occupation bound is composed with
source-confined traffic L2. Its velocity coefficient and moment are produced internally. -/
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
theorem OriginalSeedConditionalMoments.exists_original_left_birthConfinedTraffic_memLp_two
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ η ∧ 0 < C ∧
    ∀ {gap diameter : ℝ}, 0 < gap → ConditionalClockSupportBounds μ ν gap diameter →
    ∀ {g : ℝ → ℝ → ℝ},
    ∀ (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g),
    ∀ {t s A M₀ K R : ℝ}, 0 < t → t ≤ 1 → 0 < s → 4 * t < ε →
      0 ≤ A → 0 ≤ M₀ → 0 ≤ K →
    ∀ {J : Set ℝ}, MeasurableSet J → volume J ≤ ENNReal.ofReal (A * s) →
      (∀ c ∈ J, c - (S.level : ℝ) - D.lo ∈ Icc (t / 2) (4 * t)) →
    ∀ {h : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞}, Measurable h →
      (∀ x, h x ≤ ENNReal.ofReal M₀) →
    ∀ (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞),
      Measurable mask → (∀ z, mask z ≤ 1) → (∀ m c, c ∉ J → mask (m, c) = 0) →
    ∀ {Bad : Set (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))}, MeasurableSet Bad →
    ∀ {B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))}, MeasurableSet B →
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
      (fun a : (Fin (finrank ℝ S.covector.ker) → ℝ) × PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
        ∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume).support ⊆ V z) →
    MemLp (Badᶜ.indicator (fun z ↦
      (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker) d h f z).toReal)) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
    (∫ z, (Badᶜ.indicator (fun y ↦
      (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker) d h f y).toReal) z) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
      K * (M₀ * A * C * Real.sqrt s / t) ^ 2 * (volume (birthTrafficSpatialWindow G t s R)).toReal *
        (∫⁻ m in B, ENNReal.ofReal (‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
            originalSeedPairMomentum S w m‖ ^ 2)
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal := by
  obtain ⟨ε, C, hε, hεη, hC, hbound⟩ :=
    D.exists_original_left_birth_maskedTraffic_canonicalMomentum_bound hη hG hRem hpole
  refine ⟨ε, C, hε, hεη, hC, fun {gap diameter} hgap hbounds {g} Q {t s A M₀ K R}
    ht ht1 hs htε hA hM hK {J} hJ hvol hclock {h} hh hhM mask hm hm1 hz
    {Bad} hBad {B} hB V hV ↦ ?_⟩
  dsimp only
  intro hdata
  apply D.goodEvent_original_sourceConfined_traffic_memLp_two hF hw hgap hbounds Q
    ((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ hh mask hm hBad
    (isCompact_birthTrafficSpatialWindow G t s R).measurableSet
    (isCompact_birthTrafficSpatialWindow G t s R).measure_ne_top hB V hV hK
    (show 0 ≤ M₀ * A * C * Real.sqrt s / t by positivity)
  filter_upwards [hdata] with z hgeom
  intro hzBad
  obtain ⟨hsource, hcount, hsupp⟩ := hgeom hzBad
  refine ⟨hsource, hcount, hsupp, Filter.Eventually.of_forall (fun a ↦ ?_)⟩
  apply hbound ht ht1 hs htε hA hM a.1 a.2 J hJ hvol hclock h hhM
    (fun c ↦ mask (a.2, c)) (fun c _ ↦ hm1 (a.2, c))
  intro c hc
  by_contra hnot
  exact hc (hz a.2 c hnot)

/-- The actual right bounded-phase birth traffic has its literal L2 bound;
the physical `sqrt s/t` one-edge coefficient and true momentum moment are internal. -/
theorem OriginalSeedConditionalMoments.exists_original_right_birthConfinedTraffic_memLp_two
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ η ∧ 0 < C ∧
    ∀ {gap diameter : ℝ}, 0 < gap → ConditionalClockSupportBounds μ ν gap diameter →
    ∀ {g : ℝ → ℝ → ℝ},
    ∀ (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g),
    ∀ {t s A M₀ K R : ℝ}, 0 < t → t ≤ 1 → 0 < s → 4 * t < ε →
      0 ≤ A → 0 ≤ M₀ → 0 ≤ K →
    ∀ {J : Set ℝ}, MeasurableSet J → volume J ≤ ENNReal.ofReal (A * s) →
      (∀ c ∈ J, D.hi - (c - (S.level : ℝ)) ∈ Icc (t / 2) (4 * t)) →
    ∀ {h : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞}, Measurable h →
      (∀ x, h x ≤ ENNReal.ofReal M₀) →
    ∀ (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞),
      Measurable mask → (∀ z, mask z ≤ 1) → (∀ m c, c ∉ J → mask (m, c) = 0) →
    ∀ {Bad : Set (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))}, MeasurableSet Bad →
    ∀ {B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))}, MeasurableSet B →
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
      (fun a : (Fin (finrank ℝ S.covector.ker) → ℝ) × PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
        ∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume).support ⊆ V z) →
    MemLp (Badᶜ.indicator (fun z ↦
      (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker) d h f z).toReal)) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
    (∫ z, (Badᶜ.indicator (fun y ↦
      (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker) d h f y).toReal) z) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
      K * (M₀ * A * C * Real.sqrt s / t) ^ 2 * (volume (birthTrafficSpatialWindow G t s R)).toReal *
        (∫⁻ m in B, ENNReal.ofReal (‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
            originalSeedPairMomentum S w m‖ ^ 2)
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal := by
  obtain ⟨ε, C, hε, hεη, hC, hbound⟩ :=
    D.exists_original_right_birth_maskedTraffic_canonicalMomentum_bound hη hG hRem hpole
  refine ⟨ε, C, hε, hεη, hC, fun {gap diameter} hgap hbounds {g} Q {t s A M₀ K R}
    ht ht1 hs htε hA hM hK {J} hJ hvol hclock {h} hh hhM mask hm hm1 hz
    {Bad} hBad {B} hB V hV ↦ ?_⟩
  dsimp only
  intro hdata
  apply D.goodEvent_original_sourceConfined_traffic_memLp_two hF hw hgap hbounds Q
    ((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ hh mask hm hBad
    (isCompact_birthTrafficSpatialWindow G t s R).measurableSet
    (isCompact_birthTrafficSpatialWindow G t s R).measure_ne_top hB V hV hK
    (show 0 ≤ M₀ * A * C * Real.sqrt s / t by positivity)
  filter_upwards [hdata] with z hgeom
  intro hzBad
  obtain ⟨hsource, hcount, hsupp⟩ := hgeom hzBad
  refine ⟨hsource, hcount, hsupp, Filter.Eventually.of_forall (fun a ↦ ?_)⟩
  apply hbound ht ht1 hs htε hA hM a.1 a.2 J hJ hvol hclock h hhM
    (fun c ↦ mask (a.2, c)) (fun c _ ↦ hm1 (a.2, c))
  intro c hc
  by_contra hnot
  exact hc (hz a.2 c hnot)

end OTSelector.Reconstruction
