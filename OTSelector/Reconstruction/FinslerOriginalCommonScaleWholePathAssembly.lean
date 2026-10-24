import OTSelector.Reconstruction.FinslerOriginalCommonScaleContributors
import OTSelector.Reconstruction.FinslerOriginalCommonScaleIntegerCover
import OTSelector.Reconstruction.PositiveCompletePathContributors
import OTSelector.Reconstruction.FinslerOriginalCanonicalPositiveTrafficTube
import OTSelector.Finite.SampledLipschitzCurveCover
import OTSelector.Reconstruction.OriginalCompletePathCountableWeights

/-!
# Whole-path assembly from the common-scale normalized momentum field

The actual complete-path traffic readout is assembled over a finite phase cover of
the common-scale normalized momentum curve. The cover scale is the integer scale
selected from the genuinely divided field amplitude; the single-edge and count
bounds remain the original ones. The assembly identity is proved for an arbitrary
finite measurable partition, then applied to the actual integer phase cover.
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

/-- Whole-path assembly identity: the literal complete-path traffic equals the
finite sum of the complete-path cell readouts over any finite measurable partition
of the actual edge carrier that carries all nonzero edge traffic. -/
theorem legalMarkedCompletePathTraffic_eq_finset_sum_cells {q : ℕ} {ι : Type*} [Fintype ι]
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {η : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hη : Measurable η) (hf : Measurable f) (s : LegalMarkedOptimalInputScene q)
    (cells : ι → Set (LegalMarkedPhysicalEdge q))
    (hcells : ∀ i, MeasurableSet (cells i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (cells i) (cells j))
    (hzero : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)),
      (∀ i, e ∉ cells i) → legalMarkedCompletePathEdgeTraffic q d η f e = 0) :
    legalMarkedCompletePathTraffic q d η f s =
      ∑ i, ∫⁻ e, (cells i).indicator (legalMarkedCompletePathEdgeTraffic q d η f) e
        ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)) := by
  have hg : Measurable (legalMarkedCompletePathEdgeTraffic q d η f) :=
    measurable_legalMarkedCompletePathEdgeTraffic d hd hη hf
  rw [legalMarkedCompletePathTraffic_eq_lintegral_edges d hd hη hf s]
  have hpoint : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)),
      legalMarkedCompletePathEdgeTraffic q d η f e =
        ∑ i, (cells i).indicator (legalMarkedCompletePathEdgeTraffic q d η f) e := by
    filter_upwards [hzero] with e he
    by_cases hin : ∃ i, e ∈ cells i
    · obtain ⟨i₀, hi₀⟩ := hin
      have hsingle : ∀ i, e ∈ cells i → i = i₀ := by
        intro i hi
        by_contra hne
        exact (Set.disjoint_left.mp (hdisj i i₀ hne) hi) hi₀
      rw [Finset.sum_eq_single i₀]
      · exact (Set.indicator_of_mem hi₀ _).symm
      · intro i _ hne
        rw [Set.indicator_of_notMem (fun hi => hne (hsingle i hi))]
      · intro hnot
        exact absurd (Finset.mem_univ i₀) hnot
    · have hnin : ∀ i, e ∉ cells i := fun i hi => hin ⟨i, hi⟩
      rw [he hnin]
      exact (Finset.sum_eq_zero fun i _ => by
        rw [Set.indicator_of_notMem (hnin i)]).symm
  rw [lintegral_congr_ae hpoint]
  exact lintegral_finsetSum _ (fun i _ => hg.indicator (hcells i))

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The actual occupied positive contributors of the common-scale chain are
contained in the finite integer phase cover of the same common-scale normalized
momentum curve: there is one integer cover scale selected from the genuinely
divided field amplitude and one finite lattice code whose vertices cover every
actual contributor's common-scale phase pair at the fixed original radius. -/
theorem ae_original_minimizer_commonScale_integerPhaseCover
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {δ : ℝ} (hδ : 1 ≤ δ)
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value t ≤ P.value t)
    {cut h ell a : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (hh : 0 < h) (ha : 0 ≤ a)
    (hclockRange : ∀ r ∈ Icc (0 : ℝ) 1, cut + ell * r ∈ Ioo D.lo D.hi)
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r‖ *
        Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2) ≤ (1 / 2 : ℝ))
    {ρ A : ℝ} (hA : 0 ≤ A)
    (hR : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r‖ ≤ ρ)
    (hRLip : ∀ r ∈ Icc (0 : ℝ) 1, ∀ r' ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r -
        originalNormalizedClockMobility S w T (cut + S.level) ell r'‖ ≤ A * |r - r'|)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞}
    {f : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞}
    (hclock : ∀ m c, f (m, c) ≠ 0 →
      ∃ r ∈ Icc (0 : ℝ) 1, c = cut + S.level + ell * r)
    (hηwindow : ∀ x, η x ≠ 0 → ‖T *ᵥ x‖ ≤ a)
    (hmask : ∀ e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker), ∀ c,
      f ((physicalPairAnchor e).2, c) ≠ 0 →
        e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      originalSeedPathOffset S w z.2 z.1
    let radius := max (2 * (a / δ + ρ * (b / δ)))
      (b / δ + 2 * (L : ℝ) * (a / δ + ρ * (b / δ)))
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      δ ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ →
        ∃ k : ℕ, 1 ≤ k ∧ ∃ code : PhaseWalkCode (2 * finrank ℝ S.covector.ker) k,
          ∀ e ∈ occupiedCompletePathTrafficContributors (finrank ℝ S.covector.ker) d η f s,
            ∃ j : Fin (k + 1),
              ‖phasePairVector
                  (commonScaleNormalizedMomentumNodePosition S w T δ (cut + S.level) e)
                  (commonScaleNormalizedMomentumNodeValue S w T δ e) -
                phaseWalkVertex code (j : ℕ)‖ ≤ radius + 2 := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8 * |t| * G / h)
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  let radius := max (2 * (a / δ + ρ * (b / δ)))
    (b / δ + 2 * (L : ℝ) * (a / δ + ρ * (b / δ)))
  let R := originalNormalizedClockMobility S w T (cut + S.level) ell
  have hδpos : 0 < δ := by linarith
  have htube := D.ae_original_minimizer_commonScale_phase_contributors hF hw hgap hbounds T
    hδpos hg hgb t Q hmin hcut hh R hsmall hR
  have hfield := D.original_minimizer_canonical_normalized_momentum_field hF hw hgap hbounds
    T hg hgb t Q hmin hcut hh
  filter_upwards [htube, hfield.2.2, Q.full_matching] with s hsTube herror hsFull
  intro hamp
  have hamp' : (1 : ℝ) ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ / δ :=
    (one_le_div hδpos).mpr hamp
  have hspec := commonScaleNormalizedCanonicalCurveIntegerScale_spec D T cut h L ρ A δ
    (N := 1) (le_refl 1) s (by simpa only [Nat.cast_one] using hamp')
  dsimp only at hspec
  let k := D.commonScaleNormalizedCanonicalCurveIntegerScale T cut h L ρ A δ s
  have hk1 : 1 ≤ k := hspec.1
  have hρ : 0 ≤ ρ := (norm_nonneg (R 0)).trans (hR 0 (by norm_num))
  have hcov : (∀ r ∈ Icc (0 : ℝ) 1,
        ‖D.commonScaleNormalizedMomentumPhaseCurvePair T cut h L R hsmall δ s r‖ ≤ (k : ℝ)) ∧
      ∀ r ∈ Icc (0 : ℝ) 1, ∀ r' ∈ Icc (0 : ℝ) 1,
        ‖D.commonScaleNormalizedMomentumPhaseCurvePair T cut h L R hsmall δ s r -
          D.commonScaleNormalizedMomentumPhaseCurvePair T cut h L R hsmall δ s r'‖ ≤
            (k : ℝ) * |r - r'| := by
    simpa only [k] using commonScaleNormalizedCanonicalCurveIntegerScale_covers
      D T cut h L R hsmall hδpos hρ hA hR hRLip s
  obtain ⟨code, hcode⟩ := exists_phaseWalkCode_cover_of_curve
    (d := 2 * finrank ℝ S.covector.ker) (m := k) hk1
    (fun r ↦ D.commonScaleNormalizedMomentumPhaseCurvePair T cut h L R hsmall δ s r)
    (hcov.1 0 (by norm_num)) (fun r hr r' hr' => hcov.2 r hr r' hr')
  refine ⟨k, hk1, code, ?_⟩
  intro e he
  obtain ⟨r, hr, hηne, hfne, hpath⟩ :=
    original_completePathEdgeTraffic_ne_zero_exists_affineWindow_contributor S w η f T
      (cut + S.level) ell e he.2 hclock hηwindow
  have heE := hmask e _ hfne
  have hcount := ((isLegalSimpleCountingMeasure_iff _ _).mp hsFull.simple_edges).1
  have heN := (mem_support_originalCountingNodeRestriction_iff
    (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) s.1.1 hcount
    (D.normalizedMomentumPhaseEligibleEdges T cut h) e).mpr ⟨he.1, heE⟩
  have hphys : ‖normalizedMomentumNodePosition S w T (cut + S.level) e +
      R r (normalizedMomentumNodeValue S w T e)‖ ≤ a := by
    rw [D.normalizedMomentumNode_completePath_identity hF hw T e
      ⟨heE.1.1, heE.1.2.trans hcut.2⟩ hcut (hclockRange r hr)]
    exact hpath
  have hphysS : ‖commonScaleNormalizedMomentumNodePosition S w T δ (cut + S.level) e +
      R r (commonScaleNormalizedMomentumNodeValue S w T δ e)‖ ≤ a / δ := by
    simpa only [commonScaleNormalizedMomentumNodePosition, commonScaleNormalizedMomentumNodeValue,
      _root_.map_smul, ← smul_add, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδpos),
      div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left hphys (inv_nonneg.mpr hδpos.le)
  have htube_e := hsTube r hr e heN (a / δ) hphysS
  obtain ⟨j, hj⟩ := hcode r hr
  refine ⟨j, ?_⟩
  calc
    ‖phasePairVector (commonScaleNormalizedMomentumNodePosition S w T δ (cut + S.level) e)
        (commonScaleNormalizedMomentumNodeValue S w T δ e) -
        phaseWalkVertex code (j : ℕ)‖
        ≤ ‖phasePairVector (commonScaleNormalizedMomentumNodePosition S w T δ (cut + S.level) e)
              (commonScaleNormalizedMomentumNodeValue S w T δ e) -
            D.commonScaleNormalizedMomentumPhaseCurvePair T cut h L R hsmall δ s r‖ +
          ‖D.commonScaleNormalizedMomentumPhaseCurvePair T cut h L R hsmall δ s r -
            phaseWalkVertex code (j : ℕ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ radius + 2 := add_le_add htube_e hj



end OriginalSeedConditionalMoments

/-- Whole-path L1 assembly over a finite phase cover. The literal complete-path
traffic readout is the original edge integral of the same edge traffic; a finite
cover carrying every actual occupied positive contributor bounds the whole readout
by the original single-edge bound times the total mass of the finitely many cells. -/
theorem ae_wholePath_l1_finiteEdgeCover {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {η : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hη : Measurable η) (hf : Measurable f) (s : LegalMarkedOptimalInputScene q)
    {k : ℕ} (cell : Fin (k + 1) → Set (LegalMarkedPhysicalEdge q))
    {B : ℝ}
    (hbound : ∀ e ∈ legalMarkedCompletePathContributors q d η f,
      legalMarkedCompletePathEdgeTraffic q d η f e ≤ ENNReal.ofReal B)
    (hcover : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)),
      e ∈ occupiedCompletePathTrafficContributors q d η f s → ∃ j, e ∈ cell j) :
    legalMarkedCompletePathTraffic q d η f s ≤
      ENNReal.ofReal B * ∑ j : Fin (k + 1),
        (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (cell j) := by
  have hzero : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)),
      e ∉ occupiedCompletePathTrafficContributors q d η f s →
      legalMarkedCompletePathEdgeTraffic q d η f e = 0 := by
    filter_upwards [(s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support_mem_ae]
      with e hsupp hnot
    by_contra hne
    exact hnot ⟨hsupp, hne⟩
  rw [legalMarkedCompletePathTraffic_eq_lintegral_edges d hd hη hf s]
  calc
    ∫⁻ e, legalMarkedCompletePathEdgeTraffic q d η f e
        ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q))
        ≤ ∫⁻ e, (⋃ j, cell j).indicator (fun _ ↦ ENNReal.ofReal B) e
            ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)) := by
          apply lintegral_mono_ae
          filter_upwards [hzero, hcover] with e he hcovE
          by_cases hin : e ∈ occupiedCompletePathTrafficContributors q d η f s
          · obtain ⟨j, hj⟩ := hcovE hin
            rw [Set.indicator_of_mem (Set.mem_iUnion.mpr ⟨j, hj⟩)]
            exact hbound e hin.2
          · rw [he hin]
            exact zero_le
    _ ≤ ENNReal.ofReal B * (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (⋃ j, cell j) :=
          lintegral_indicator_const_le _ _
    _ ≤ ENNReal.ofReal B * ∑ j : Fin (k + 1),
          (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (cell j) := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          calc (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (⋃ j, cell j)
              ≤ ∑' j : Fin (k + 1), (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (cell j) :=
                measure_iUnion_le cell
            _ = ∑ j : Fin (k + 1),
                  (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (cell j) := tsum_fintype _

end OTSelector.Reconstruction
