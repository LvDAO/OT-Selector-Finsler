import OTSelector.Reconstruction.OriginalPairClockSupportMask
import OTSelector.Reconstruction.FinslerOriginalClockPiecePartition
import OTSelector.Reconstruction.FinslerOriginalClockRegionTraffic
import OTSelector.Reconstruction.OriginalCompletePathCountableWeights
import OTSelector.Reconstruction.OriginalCompletePathAbsoluteTraffic

/-! Actual original source/target birth and old clock pieces reconstruct the
same original complete path. All Palm/clock and scene identities are proved
internally before the summable level estimates are used for L2 assembly. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Topology BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The literal actual clock-piece occupation, retaining the unchanged
original clock supports required by the same minimizer's node eligibility. -/
def originalClockPieceSupportedWeight (ε : ℝ) (piece : OriginalClockTrafficPieceIndex)
    (z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ) : ℝ≥0∞ :=
  originalPairClockSupportMask (finrank ℝ S.covector.ker) μ ν z *
    D.originalClockTrafficPieceWeight ε piece z

theorem measurable_originalClockPieceSupportedWeight
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (ε : ℝ)
    (piece : OriginalClockTrafficPieceIndex) : Measurable (D.originalClockPieceSupportedWeight ε piece) :=
  (measurable_originalPairClockSupportMask _ μ ν).mul
    (D.measurable_originalClockTrafficPieceWeight hF hw ε piece)

/-- The actual complete-clock pieces cover the unchanged occupation on the
original true Palm; no covering or support property is assumed. -/
theorem ae_tsum_originalClockPieceSupportedWeight
    {gap : ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law,
      ∀ᵐ c : ℝ ∂volume, (∑' piece, D.originalClockPieceSupportedWeight ε piece (m, c)) =
        ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ := by
  filter_upwards [D.ae_originalClockRegionWeight_sum Q ε,
    Q.ae_originalPairClockSupportMask_eq_one] with m hm hs
  filter_upwards [hm] with c hc
  calc
    _ = originalPairClockSupportMask (finrank ℝ S.covector.ker) μ ν (m, c) *
        ∑' piece, D.originalClockTrafficPieceWeight ε piece (m, c) := ENNReal.tsum_mul_left
    _ = ∑' piece, D.originalClockTrafficPieceWeight ε piece (m, c) := by rw [hs c, one_mul]
    _ = ∑ i : Fin 8, D.originalClockRegionWeight ε i (m, c) :=
      D.tsum_originalClockTrafficPieceWeight hε (m, c)
    _ = _ := hc

/-- Literal original-scene traffic in one internally defined actual clock piece. -/
def originalClockPieceAbsoluteTraffic
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ)
    (ε : ℝ) (piece : OriginalClockTrafficPieceIndex)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ≥0∞ :=
  legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
    (fun z ↦ originalSeedPathOffset S w z.2 z.1) (fun x ↦ ENNReal.ofReal (η x))
    (D.originalClockPieceSupportedWeight ε piece) s

theorem measurable_originalClockPieceAbsoluteTraffic
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    (ε : ℝ) (piece : OriginalClockTrafficPieceIndex) :
    Measurable (D.originalClockPieceAbsoluteTraffic η ε piece) :=
  measurable_legalMarkedCompletePathTraffic _ (measurable_originalSeedPathOffset_joint S hF hw)
    hη.ennreal_ofReal (D.measurable_originalClockPieceSupportedWeight hF hw ε piece)

/-- The exact complete-path countable decomposition is an internally proved
statement about the actual original scene and actual original matching. -/
theorem ae_original_completePathAbsoluteTraffic_eq_tsum_clockPieces
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    (hηI : Integrable η (volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      originalSeedCompletePathAbsoluteTraffic S w η s =
        ∑' piece, D.originalClockPieceAbsoluteTraffic η ε piece s := by
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  have hd := measurable_originalSeedPathOffset_joint S hF hw
  have hf := (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal
  have hp := D.measurable_originalClockPieceSupportedWeight hF hw ε
  have hηfinite : (∫⁻ x, ENNReal.ofReal (η x)
      ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) ≠ (⊤ : ℝ≥0∞) :=
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hηI.2).ne
  have hfinite : (∫⁻ x, ENNReal.ofReal (η x)
      ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ, ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖
        ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞) := by
    rw [D.lintegral_original_clockOccupation_norm_eq_pathLength hF hw hbounds Q]
    exact ENNReal.mul_ne_top hηfinite ENNReal.ofReal_ne_top
  have heq := Q.ae_completePathTraffic_congr_weights d hd hη.ennreal_ofReal
    (Measurable.tsum hp) hf (D.ae_tsum_originalClockPieceSupportedWeight Q hε) hfinite
  filter_upwards [heq] with s hs
  change legalMarkedCompletePathTraffic _ d _ _ s = _
  rw [← hs, legalMarkedCompletePathTraffic_tsum_weights d hd hη.ennreal_ofReal _ hp s]
  rfl

/-- The literal real-valued countable decomposition has no hidden infinite
summands: finiteness is produced from the original kinetic first moment. -/
theorem ae_toReal_original_completePathAbsoluteTraffic_eq_tsum_clockPieces
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    (hηI : Integrable η (volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      (originalSeedCompletePathAbsoluteTraffic S w η s).toReal =
        ∑' piece, (D.originalClockPieceAbsoluteTraffic η ε piece s).toReal := by
  filter_upwards [D.ae_original_completePathAbsoluteTraffic_eq_tsum_clockPieces hF hw hbounds Q hη hηI hε,
    D.ae_original_completePathAbsoluteTraffic_lt_top hF hw hbounds Q hη hηI] with s hs hf
  have hfinite : (∑' piece, D.originalClockPieceAbsoluteTraffic η ε piece s) ≠ (⊤ : ℝ≥0∞) := by
    rw [← hs]
    exact hf.ne
  rw [hs, ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hfinite)]

/-- Summable norm bounds for these actual, internally covering clock pieces
produce L2 of the literal full original path traffic and its exact norm bound. -/
theorem memLp_original_completePathAbsoluteTraffic_of_clockPieces
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    (hηI : Integrable η (volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)))
    {ε : ℝ} (hε : 0 < ε)
    (hLtwo : ∀ piece, MemLp (fun s ↦ (D.originalClockPieceAbsoluteTraffic η ε piece s).toReal) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
    (A : OriginalClockTrafficPieceIndex → ℝ) (hA : Summable A) (hA0 : ∀ piece, 0 ≤ A piece)
    (hbound : ∀ piece, eLpNorm (fun s ↦ (D.originalClockPieceAbsoluteTraffic η ε piece s).toReal) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ≤ ENNReal.ofReal (A piece)) :
    MemLp (fun s ↦ (originalSeedCompletePathAbsoluteTraffic S w η s).toReal) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
    (eLpNorm (fun s ↦ (originalSeedCompletePathAbsoluteTraffic S w η s).toReal) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))).toReal ≤ ∑' piece, A piece ∧
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      Summable (fun piece ↦ ‖(D.originalClockPieceAbsoluteTraffic η ε piece s).toReal‖) := by
  have hreal := D.ae_toReal_original_completePathAbsoluteTraffic_eq_tsum_clockPieces
    hF hw hbounds Q hη hηI hε
  have hLp := memLp_tsum_of_summable_level_bound
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
    (fun piece s ↦ (D.originalClockPieceAbsoluteTraffic η ε piece s).toReal) hLtwo A hA hA0 hbound
  refine ⟨hLp.1.ae_eq (Filter.EventuallyEq.symm hreal), ?_, hLp.2.2⟩
  rw [eLpNorm_congr_ae hreal]
  exact hLp.2.1

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
