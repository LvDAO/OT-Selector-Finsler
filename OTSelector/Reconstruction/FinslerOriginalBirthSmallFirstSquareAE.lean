import OTSelector.Reconstruction.OriginalCountTrafficGoodEventAELtwo
import OTSelector.Reconstruction.OriginalSameResiduePalmEnergy
import OTSelector.Analysis.ENNRealSquareRootReadout
import OTSelector.Reconstruction.OriginalBirthBandSmallFirstMoment
import OTSelector.Reconstruction.OriginalCompletePathAbsoluteTraffic

/-! The same literal actual count-good birth traffic has its first square-root
energy bound. Original Campbell, original clock mass and true same-residue Palm
energy finiteness are produced before taking the real-valued traffic readout. -/
open Set Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The actual left birth traffic on its count-good event has the first
small-phase square estimate, retaining the same original band energies. -/
theorem OriginalSeedConditionalMoments.exists_original_left_birthBand_smallFirstSquare_bound_ae
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
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
      ∀ {t s : ℝ}, 0 < t → 0 < s → 4 * t < ε →
      ∀ {B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))}, MeasurableSet B →
      (∀ m ∈ B, m.1.1 - (S.level : ℝ) - D.lo ∈ Icc t (2 * t)) →
      ∀ {I : Set ℝ}, MeasurableSet I →
      (∀ c ∈ I, c - (S.level : ℝ) - D.lo ∈ Icc t (4 * t)) →
      ∀ {A Kmass : ℝ}, 0 ≤ A → 0 ≤ Kmass → volume I ≤ ENNReal.ofReal (A * s) →
      ∀ {J : Set ℝ}, MeasurableSet J →
      (∀ m ∈ B, m.1.1 - (S.level : ℝ) ∈ J) →
      (μ.map (fun a : ℝ ↦ a - (S.level : ℝ))) J ≤
        ENNReal.ofReal (Kmass * t ^ G.rank * s) →
      ∀ (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞),
      Measurable mask → (∀ z, mask z ≤ 1) →
      (∀ m c, m ∉ B ∨ c ∉ I → mask (m, c) = 0) →
      ∀ {h : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞}, Measurable h →
      (∫⁻ x, h x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) ≠ (∞ : ℝ≥0∞) →
      ∀ {Bad : Set (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))}, MeasurableSet Bad →
      ∀ (V : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) →
        Set ((Fin (finrank ℝ S.covector.ker) → ℝ) × PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))),
      (∀ z, MeasurableSet (V z)) → ∀ {B₀ K : ℝ}, 0 ≤ B₀ → 0 ≤ K →
      let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
        originalSeedPathOffset S w z.2 z.1
      let f := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
        ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z
      (∀ᵐ z ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))), z ∉ Bad →
        (∀ᵐ a ∂physicalScenePairKernel z.1, a ∉ V z →
          (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) = 0) ∧
        (∀ᵐ a ∂(physicalScenePairKernel z.1).restrict (V z),
          (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) ≤ ENNReal.ofReal B₀) ∧
        physicalScenePairKernel z.1 (V z) ≤ ENNReal.ofReal K) →
      MemLp (Badᶜ.indicator (fun z ↦ (legalMarkedCompletePathTraffic
        (finrank ℝ S.covector.ker) d h f z).toReal)) 2
          (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (∫ z, (Badᶜ.indicator (fun y ↦ (legalMarkedCompletePathTraffic
        (finrank ℝ S.covector.ker) d h f y).toReal) z) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
      (B₀ * K * (∫⁻ x, h x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))).toReal *
        A * C * Real.sqrt Kmass) * s ^ (3 / 2 : ℝ) *
        (t ^ (((G.rank : ℝ) - 3) / 2) * Real.sqrt
          (∫⁻ m in B, ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal +
        t ^ ((G.rank : ℝ) / 2) * Real.sqrt
          (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal) := by
  have hRem0 : ContinuousAt Rem 0 := hRem.continuousAt (Ioo_mem_nhds (by linarith) hη)
  obtain ⟨ε, C, hε, hεη, hC, hfirst⟩ :=
    D.exists_original_left_birthBand_smallFirstMoment_bound hF hw hη hG hRem0 hpole
  refine ⟨ε, C, hε, hεη, hC, fun {gap diameter} hgap hbounds {g} Q {t s} ht hs htε
    {B} hB ha {I} hI hc {A Kmass} hA hKmass hlen {J} hJ hBJ hmass mask hm hm1 hz
    {h} hh hspace {Bad} hBad V hV {B₀ K} hB₀ hK ↦ ?_⟩
  dsimp only
  intro hdata
  have hIE := (D.original_left_sameResidue_focalEnergy_integrable hF hw hη hηspan
    hG hRem hpole hgap hbounds Q).2.1
  have hIV := (D.integrable_original_pair_momentum_of_weighted_stationary hF hw hgap hbounds Q).2
  have he : (∫⁻ m in B, ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (∞ : ℝ≥0∞) :=
    ne_top_of_le_ne_top ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hIE.2).ne
      (setLIntegral_le_lintegral _ _)
  have hv : (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (∞ : ℝ≥0∞) :=
    ne_top_of_le_ne_top ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hIV.2).ne
      (setLIntegral_le_lintegral _ _)
  have hb := hfirst Q ht hs htε hB ha hI hc hA hKmass hlen hJ hBJ hmass mask hm1 hz
  obtain ⟨hocc, hreal⟩ := firstMoment_energy_toReal_bound he hv
    (show 0 ≤ A * C * Real.sqrt Kmass by positivity)
    (show 0 ≤ s ^ (3 / 2 : ℝ) * t ^ (((G.rank : ℝ) - 3) / 2) by positivity)
    (show 0 ≤ s ^ (3 / 2 : ℝ) * t ^ ((G.rank : ℝ) / 2) by positivity) hb
  have hf : Measurable (fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z) :=
    (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul hm
  obtain ⟨hLp, hmean⟩ := Q.goodEvent_completePath_traffic_memLp_two_of_count_ae
    _ (measurable_originalSeedPathOffset_joint S hF hw) hh hf
    (ENNReal.mul_ne_top hspace hocc) hBad V hV hB₀ hK hdata
  refine ⟨hLp, hmean.trans ?_⟩
  rw [ENNReal.toReal_mul]
  calc
    _ ≤ (B₀ * K) * (∫⁻ x, h x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))).toReal *
        ((A * C * Real.sqrt Kmass) *
          ((s ^ (3 / 2 : ℝ) * t ^ (((G.rank : ℝ) - 3) / 2)) * Real.sqrt
            (∫⁻ m in B, ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
              ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal +
          (s ^ (3 / 2 : ℝ) * t ^ ((G.rank : ℝ) / 2)) * Real.sqrt
            (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
              ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal)) := by
      calc
        _ = ((B₀ * K) * (∫⁻ x, h x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))).toReal) *
          (∫⁻ m, ∫⁻ c : ℝ, ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c)
            ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hreal (by positivity)
    _ = _ := by ring

/-- The actual right birth traffic on its count-good event has the first
small-phase square estimate, retaining the same original band energies. -/
theorem OriginalSeedConditionalMoments.exists_original_right_birthBand_smallFirstSquare_bound_ae
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
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
      ∀ {t s : ℝ}, 0 < t → 0 < s → 4 * t < ε →
      ∀ {B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))}, MeasurableSet B →
      (∀ m ∈ B, D.hi - (m.1.2 - (S.level : ℝ)) ∈ Icc t (2 * t)) →
      ∀ {I : Set ℝ}, MeasurableSet I →
      (∀ c ∈ I, D.hi - (c - (S.level : ℝ)) ∈ Icc t (4 * t)) →
      ∀ {A Kmass : ℝ}, 0 ≤ A → 0 ≤ Kmass → volume I ≤ ENNReal.ofReal (A * s) →
      ∀ {J : Set ℝ}, MeasurableSet J →
      (∀ m ∈ B, m.1.2 - (S.level : ℝ) ∈ J) →
      (ν.map (fun a : ℝ ↦ a - (S.level : ℝ))) J ≤
        ENNReal.ofReal (Kmass * t ^ G.rank * s) →
      ∀ (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞),
      Measurable mask → (∀ z, mask z ≤ 1) →
      (∀ m c, m ∉ B ∨ c ∉ I → mask (m, c) = 0) →
      ∀ {h : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞}, Measurable h →
      (∫⁻ x, h x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) ≠ (∞ : ℝ≥0∞) →
      ∀ {Bad : Set (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))}, MeasurableSet Bad →
      ∀ (V : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) →
        Set ((Fin (finrank ℝ S.covector.ker) → ℝ) × PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))),
      (∀ z, MeasurableSet (V z)) → ∀ {B₀ K : ℝ}, 0 ≤ B₀ → 0 ≤ K →
      let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
        originalSeedPathOffset S w z.2 z.1
      let f := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
        ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z
      (∀ᵐ z ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))), z ∉ Bad →
        (∀ᵐ a ∂physicalScenePairKernel z.1, a ∉ V z →
          (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) = 0) ∧
        (∀ᵐ a ∂(physicalScenePairKernel z.1).restrict (V z),
          (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) ≤ ENNReal.ofReal B₀) ∧
        physicalScenePairKernel z.1 (V z) ≤ ENNReal.ofReal K) →
      MemLp (Badᶜ.indicator (fun z ↦ (legalMarkedCompletePathTraffic
        (finrank ℝ S.covector.ker) d h f z).toReal)) 2
          (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (∫ z, (Badᶜ.indicator (fun y ↦ (legalMarkedCompletePathTraffic
        (finrank ℝ S.covector.ker) d h f y).toReal) z) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
      (B₀ * K * (∫⁻ x, h x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))).toReal *
        A * C * Real.sqrt Kmass) * s ^ (3 / 2 : ℝ) *
        (t ^ (((G.rank : ℝ) - 3) / 2) * Real.sqrt
          (∫⁻ m in B, ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal +
        t ^ ((G.rank : ℝ) / 2) * Real.sqrt
          (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal) := by
  have hRem0 : ContinuousAt Rem 0 := hRem.continuousAt (Ioo_mem_nhds (by linarith) hη)
  obtain ⟨ε, C, hε, hεη, hC, hfirst⟩ :=
    D.exists_original_right_birthBand_smallFirstMoment_bound hF hw hη hG hRem0 hpole
  refine ⟨ε, C, hε, hεη, hC, fun {gap diameter} hgap hbounds {g} Q {t s} ht hs htε
    {B} hB ha {I} hI hc {A Kmass} hA hKmass hlen {J} hJ hBJ hmass mask hm hm1 hz
    {h} hh hspace {Bad} hBad V hV {B₀ K} hB₀ hK ↦ ?_⟩
  dsimp only
  intro hdata
  have hIE := (D.original_right_sameResidue_focalEnergy_integrable hF hw hη hηspan
    hG hRem hpole hgap hbounds Q).2.1
  have hIV := (D.integrable_original_pair_momentum_of_weighted_stationary hF hw hgap hbounds Q).2
  have he : (∫⁻ m in B, ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (∞ : ℝ≥0∞) :=
    ne_top_of_le_ne_top ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hIE.2).ne
      (setLIntegral_le_lintegral _ _)
  have hv : (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (∞ : ℝ≥0∞) :=
    ne_top_of_le_ne_top ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hIV.2).ne
      (setLIntegral_le_lintegral _ _)
  have hb := hfirst Q ht hs htε hB ha hI hc hA hKmass hlen hJ hBJ hmass mask hm1 hz
  obtain ⟨hocc, hreal⟩ := firstMoment_energy_toReal_bound he hv
    (show 0 ≤ A * C * Real.sqrt Kmass by positivity)
    (show 0 ≤ s ^ (3 / 2 : ℝ) * t ^ (((G.rank : ℝ) - 3) / 2) by positivity)
    (show 0 ≤ s ^ (3 / 2 : ℝ) * t ^ ((G.rank : ℝ) / 2) by positivity) hb
  have hf : Measurable (fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z) :=
    (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul hm
  obtain ⟨hLp, hmean⟩ := Q.goodEvent_completePath_traffic_memLp_two_of_count_ae
    _ (measurable_originalSeedPathOffset_joint S hF hw) hh hf
    (ENNReal.mul_ne_top hspace hocc) hBad V hV hB₀ hK hdata
  refine ⟨hLp, hmean.trans ?_⟩
  rw [ENNReal.toReal_mul]
  calc
    _ ≤ (B₀ * K) * (∫⁻ x, h x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))).toReal *
        ((A * C * Real.sqrt Kmass) *
          ((s ^ (3 / 2 : ℝ) * t ^ (((G.rank : ℝ) - 3) / 2)) * Real.sqrt
            (∫⁻ m in B, ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
              ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal +
          (s ^ (3 / 2 : ℝ) * t ^ ((G.rank : ℝ) / 2)) * Real.sqrt
            (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
              ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal)) := by
      calc
        _ = ((B₀ * K) * (∫⁻ x, h x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))).toReal) *
          (∫⁻ m, ∫⁻ c : ℝ, ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c)
            ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hreal (by positivity)
    _ = _ := by ring

end OTSelector.Reconstruction
