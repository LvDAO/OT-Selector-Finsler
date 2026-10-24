import OTSelector.Reconstruction.OriginalOccupiedTrafficInputCounts
import OTSelector.Reconstruction.OriginalCountTrafficGoodEventAELtwo
import OTSelector.Reconstruction.OriginalCompletePathAbsoluteTraffic
import OTSelector.Reconstruction.FinslerOriginalCommonScaleWholePathAssembly

/-!
# L2/Palm-square bound for the common-scale whole-path assembly

The literal complete-path traffic readout is squared against its own actual Palm
first moment. Support containment is the actual occupied pair-contributor set
(the anchor image of the occupied contributors of the finite integer phase
cover); the cover count bound is transferred from the actual edge measure to the
physical pair kernel through the physical pair anchor homeomorphism. The finite
cover and its uniform edge mass are the only counting input.
-/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The whole-path square of the literal complete-path traffic is controlled by
the actual occupied contributor count and the original single-edge bound. The
pair-space contributors are the anchor image of the actual occupied edge set; the
kernel count bound is the edge mass transferred through the anchor homeomorphism. -/
theorem ae_wholePath_memLp_two_of_finiteEdgeCover {q : ℕ}
    {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {η : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hη : Measurable η) (hf : Measurable f)
    (hfinite : (∫⁻ x, η x ∂(volume : Measure (Fin q → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
        ∂legalMarkedJointPalm q Q.law) ≠ (⊤ : ℝ≥0∞))
    {Bad : Set (LegalMarkedOptimalInputScene q)} (hBad : MeasurableSet Bad)
    {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbound : ∀ e ∈ legalMarkedCompletePathContributors q d η f,
      legalMarkedCompletePathEdgeTraffic q d η f e ≤ ENNReal.ofReal B)
    (hcover : ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)), s ∉ Bad →
      ∃ U : Set (LegalMarkedPhysicalEdge q),
        occupiedCompletePathTrafficContributors q d η f s ⊆ U ∧
          (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) U ≤ ENNReal.ofReal K) :
    MemLp (Badᶜ.indicator
      (fun s ↦ (legalMarkedCompletePathTraffic q d η f s).toReal)) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫ s, (Badᶜ.indicator
      (fun z ↦ (legalMarkedCompletePathTraffic q d η f z).toReal) s) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤ (B * K) *
      ((∫⁻ x, η x ∂(volume : Measure (Fin q → ℝ))) *
        (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
          ∂legalMarkedJointPalm q Q.law)).toReal := by
  have hV : ∀ s, MeasurableSet (occupiedPairTrafficContributors q d η f s) :=
    fun s ↦ measurableSet_occupiedPairTrafficContributors d hd hη hf s
  refine Q.goodEvent_completePath_traffic_memLp_two_of_count_ae d hd hη hf hfinite hBad
    (fun s ↦ occupiedPairTrafficContributors q d η f s) hV hB hK ?_
  filter_upwards [hcover] with s hs
  intro hsnot
  obtain ⟨U, hsub, hmass⟩ := hs hsnot
  have hocc : (s.1.1 : Measure (LegalMarkedPhysicalEdge q))
      (occupiedCompletePathTrafficContributors q d η f s) ≤ ENNReal.ofReal K :=
    (measure_mono hsub).trans hmass
  refine ⟨ae_occupiedPairTrafficContributors_outside_zero d η f s, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem (hV s)] with a ha
    let e := (physicalPairAnchorHomeomorph q).symm a
    have hae : e ∈ occupiedCompletePathTrafficContributors q d η f s := ha
    have hG : (∫⁻ r : ℝ, η (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) =
        legalMarkedCompletePathEdgeTraffic q d η f e := by
      rw [← (physicalPairAnchorHomeomorph q).apply_symm_apply a]
      rfl
    rw [hG]
    exact hbound e hae.2
  · rw [physicalScenePairKernel_apply, Measure.map_apply measurable_physicalPairAnchor (hV s)]
    have hpre : physicalPairAnchor ⁻¹' occupiedPairTrafficContributors q d η f s =
        occupiedCompletePathTrafficContributors q d η f s := by
      ext e
      change (physicalPairAnchorHomeomorph q).symm ((physicalPairAnchorHomeomorph q) e) ∈
          occupiedCompletePathTrafficContributors q d η f s ↔
        e ∈ occupiedCompletePathTrafficContributors q d η f s
      rw [Homeomorph.symm_apply_apply]
    rw [hpre]
    exact hocc

/-- The same whole-path L2/Palm-square bound from a uniform actual occupied
contributor count, with no cover set retained. -/
theorem ae_wholePath_memLp_two_of_uniformOccupiedCount {q : ℕ}
    {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {η : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hη : Measurable η) (hf : Measurable f)
    (hfinite : (∫⁻ x, η x ∂(volume : Measure (Fin q → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
        ∂legalMarkedJointPalm q Q.law) ≠ (⊤ : ℝ≥0∞))
    {Bad : Set (LegalMarkedOptimalInputScene q)} (hBad : MeasurableSet Bad)
    {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbound : ∀ e ∈ legalMarkedCompletePathContributors q d η f,
      legalMarkedCompletePathEdgeTraffic q d η f e ≤ ENNReal.ofReal B)
    (hcount : ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)), s ∉ Bad →
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q))
        (occupiedCompletePathTrafficContributors q d η f s) ≤ ENNReal.ofReal K) :
    MemLp (Badᶜ.indicator
      (fun s ↦ (legalMarkedCompletePathTraffic q d η f s).toReal)) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫ s, (Badᶜ.indicator
      (fun z ↦ (legalMarkedCompletePathTraffic q d η f z).toReal) s) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤ (B * K) *
      ((∫⁻ x, η x ∂(volume : Measure (Fin q → ℝ))) *
        (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
          ∂legalMarkedJointPalm q Q.law)).toReal := by
  exact ae_wholePath_memLp_two_of_finiteEdgeCover Q d hd hη hf hfinite hBad hB hK hbound
    (by filter_upwards [hcount] with s hs; intro hsnot
        exact ⟨_, subset_rfl, hs hsnot⟩)

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The common-scale field-amplitude event at which the divided amplitude is too
small to select a genuine integer phase scale. It is Borel. -/
def commonScaleAmplitudeBelowEvent
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut h : ℝ) (L : ℝ≥0) (δ : ℝ) :
    Set (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :=
  {s | ‖D.normalizedMomentumPhaseField T cut h L s 0‖ < δ}

theorem measurableSet_commonScaleAmplitudeBelowEvent
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0) (δ : ℝ) :
    MeasurableSet (D.commonScaleAmplitudeBelowEvent T cut h L δ) := by
  apply measurableSet_lt
  · exact ((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm
  · exact measurable_const

/-- L2/Palm-square bound for the whole path from the common-scale finite integer
phase cover. Off the divided-amplitude event the actual occupied contributors are
carried by the finite phase cover with uniform actual edge mass K; the original
single-edge bound B then gives the literal whole-path traffic square bound against
its own actual Palm first moment. -/
theorem ae_original_minimizer_commonScale_wholePath_memLp_two
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {δ : ℝ} (hδ : 0 < δ)
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value t ≤ P.value t)
    {cut h : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (hh : 0 < h)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞}
    {f : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞}
    (hη : Measurable η) (hf : Measurable f)
    (hfinite : (∫⁻ x, η x ∂(volume : Measure
        (Fin (finrank ℝ S.covector.ker) → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞))
    {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbound : ∀ e ∈ legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f,
      legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f e ≤ ENNReal.ofReal B)
    (hcount : ∀ᵐ s ∂(Q.law : Measure
        (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
        δ ≤ ‖D.normalizedMomentumPhaseField T cut h
          ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩ s 0‖ →
        (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
          (occupiedCompletePathTrafficContributors (finrank ℝ S.covector.ker)
            (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s) ≤ ENNReal.ofReal K) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let Bad := {s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) |
      ‖D.normalizedMomentumPhaseField T cut h L s 0‖ < δ}
    MemLp (Badᶜ.indicator (fun s ↦ (legalMarkedCompletePathTraffic
        (finrank ℝ S.covector.ker) (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s).toReal)) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
    (∫ s, (Badᶜ.indicator (fun z ↦ (legalMarkedCompletePathTraffic
        (finrank ℝ S.covector.ker) (fun z' ↦ originalSeedPathOffset S w z'.2 z'.1) η f z).toReal) s) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤ (B * K) *
      ((∫⁻ x, η x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) *
        (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  have hBad : MeasurableSet (D.commonScaleAmplitudeBelowEvent T cut h L δ) :=
    D.measurableSet_commonScaleAmplitudeBelowEvent hF hw T hcut h L δ
  refine ae_wholePath_memLp_two_of_finiteEdgeCover Q d
    (measurable_originalSeedPathOffset_joint S hF hw) hη hf hfinite hBad hB hK hbound ?_
  filter_upwards [hcount] with s hs
  intro hsnot
  have hamp : δ ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ := not_lt.mp hsnot
  exact ⟨_, subset_rfl, hs hamp⟩

end OriginalSeedConditionalMoments
