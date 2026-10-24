import OTSelector.Reconstruction.FinslerOriginalCompletePathClockPieces
import OTSelector.Reconstruction.FinslerOriginalSupportedBirthWindowWeights

/-! Exact scene readouts identify the actual full birth windows and old shells
with their original eight clock regions, before any real-valued L2 assembly. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Topology BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "qdim" => finrank ℝ S.covector.ker
local notation "MarkClock" => PhysicalPairPalmMark (Fin qdim) × ℝ

/-- The unchanged occupation in one original region, with the two original
endpoint supports retained exactly as in the actual countable clock pieces. -/
def originalSupportedClockRegionAbsoluteTraffic
    (η : (Fin qdim→ℝ)→ℝ) (ε : ℝ) (i : Fin 8)
    (scene : LegalMarkedOptimalInputScene qdim) : ℝ≥0∞ :=
  legalMarkedCompletePathTraffic qdim (fun z↦originalSeedPathOffset S w z.2 z.1)
    (fun x↦ENNReal.ofReal (η x))
    (fun z↦originalPairClockSupportMask qdim μ ν z * D.originalClockRegionWeight ε i z) scene

theorem measurable_originalSupportedClockRegionAbsoluteTraffic
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {η : (Fin qdim→ℝ)→ℝ} (hη : Measurable η) (ε : ℝ) (i : Fin 8) :
    Measurable (D.originalSupportedClockRegionAbsoluteTraffic η ε i) :=
  measurable_legalMarkedCompletePathTraffic _ (measurable_originalSeedPathOffset_joint S hF hw)
    hη.ennreal_ofReal ((measurable_originalPairClockSupportMask _ μ ν).mul
      (D.measurable_originalClockRegionWeight hF hw ε i))

/-- The actual nonnegative birth pieces sum to their same supported original
region for every scene; no finiteness or probabilistic input is required. -/
theorem tsum_originalFocalBirthPieceAbsoluteTraffic_eq_region
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {η : (Fin qdim→ℝ)→ℝ} (hη : Measurable η)
    {ε : ℝ} (hε : 0<ε) (side : Fin 2) (scene : LegalMarkedOptimalInputScene qdim) :
    (∑' nj : ℕ×ℕ,D.originalClockPieceAbsoluteTraffic η ε
      (.inl (.inl (side,nj.1,nj.2))) scene) =
      D.originalSupportedClockRegionAbsoluteTraffic η ε (originalFocalBirthRegionIndex side) scene := by
  let pieces := fun nj : ℕ×ℕ↦D.originalClockPieceSupportedWeight ε
    (.inl (.inl (side,nj.1,nj.2)))
  have hp : ∀ nj,Measurable (pieces nj) := fun nj↦
    D.measurable_originalClockPieceSupportedWeight hF hw ε _
  have hs := legalMarkedCompletePathTraffic_tsum_weights
    (fun z : MarkClock↦originalSeedPathOffset S w z.2 z.1)
    (measurable_originalSeedPathOffset_joint S hF hw) hη.ennreal_ofReal pieces hp scene
  change (∑' nj : ℕ×ℕ,legalMarkedCompletePathTraffic _ _ _ (pieces nj) scene) = _
  rw [←hs]
  congr 1
  funext z
  simp only [pieces,originalClockPieceSupportedWeight,originalClockTrafficPieceWeight,
    originalClockTrafficPieceMask,ENNReal.tsum_prod',←mul_assoc,ENNReal.tsum_mul_left]
  rw [D.tsum_originalFocalBirthPieceMask hε]
  simp only [originalClockRegionWeight,mul_assoc]

/-- The actual old shell readout is exactly its same supported original region. -/
theorem tsum_originalFocalOldPieceAbsoluteTraffic_eq_region
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {η : (Fin qdim→ℝ)→ℝ} (hη : Measurable η)
    {ε : ℝ} (hε : 0<ε) (side : Fin 2) (scene : LegalMarkedOptimalInputScene qdim) :
    (∑' n : ℕ,D.originalClockPieceAbsoluteTraffic η ε (.inl (.inr (side,n))) scene) =
      D.originalSupportedClockRegionAbsoluteTraffic η ε (originalFocalOldRegionIndex side) scene := by
  let pieces := fun n : ℕ↦D.originalClockPieceSupportedWeight ε (.inl (.inr (side,n)))
  have hp : ∀ n,Measurable (pieces n) := fun n↦
    D.measurable_originalClockPieceSupportedWeight hF hw ε _
  have hs := legalMarkedCompletePathTraffic_tsum_weights
    (fun z : MarkClock↦originalSeedPathOffset S w z.2 z.1)
    (measurable_originalSeedPathOffset_joint S hF hw) hη.ennreal_ofReal pieces hp scene
  change (∑' n : ℕ,legalMarkedCompletePathTraffic _ _ _ (pieces n) scene) = _
  rw [←hs]
  congr 1
  funext z
  simp only [pieces,originalClockPieceSupportedWeight,originalClockTrafficPieceWeight,
    originalClockTrafficPieceMask,←mul_assoc,ENNReal.tsum_mul_left]
  rw [D.tsum_originalFocalOldPieceMask hε]
  simp only [originalClockRegionWeight,mul_assoc]

/-- A finite physical-clock cover and the unchanged narrow-band partition
are precisely one actual birth piece, pointwise in the original paired mark. -/
theorem sum_originalSupportedBirthPhysicalClockWeight_eq_piece
    {ε cap : ℝ} (hε : 0<ε) (hcap : 0<cap) (side : Fin 2) (n j : ℕ) (z : MarkClock) :
    (∑ell : Fin (birthPhysicalClockWindowCount cap),∑i : Fin (dyadicBirthBandCount j),
      (if side=0 then D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell z
        else D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell z)) =
      D.originalClockPieceSupportedWeight ε (.inl (.inl (side,n,j))) z := by
  fin_cases side
  · change (∑ell : Fin (birthPhysicalClockWindowCount cap),∑i : Fin (dyadicBirthBandCount j),
        D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell z) =
        D.originalClockPieceSupportedWeight ε (.inl (.inl ((0:Fin 2),n,j))) z
    let coeff := originalPairClockSupportMask qdim μ ν z *
      ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ *
        originalClockTrafficRegionMask (D.lo+S.level) (D.hi+S.level) ε 0 z
    have hweight (i ell : ℕ) : D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell z =
        coeff*D.originalLeftBirthPhysicalClockMask ε cap n j i ell z := by
      dsimp [coeff,originalSupportedLeftBirthPhysicalClockWeight,
        originalSupportedLeftBirthPhysicalClockMask]
      ac_rfl
    have hwindow (i : ℕ) : (∑ell : Fin (birthPhysicalClockWindowCount cap),
        D.originalLeftBirthPhysicalClockMask ε cap n j i ell z) =
        D.originalLeftBirthClockMask ε n j i z := by
      exact (Fin.sum_univ_eq_sum_range (fun ell : ℕ↦
        D.originalLeftBirthPhysicalClockMask ε cap n j i ell z) _).trans
          (D.sum_originalLeftBirthPhysicalClockMask hε hcap n j i z)
    rw [Finset.sum_comm]
    simp_rw [hweight,←Finset.mul_sum,hwindow]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ↦D.originalLeftBirthClockMask ε n j i z) _]
    dsimp [coeff,originalClockPieceSupportedWeight,originalClockTrafficPieceWeight,
      originalClockTrafficPieceMask,originalFocalBirthPieceMask,originalFocalBirthRegionIndex,
      originalSidedBirthClockMask]
    ac_rfl
  · change (∑ell : Fin (birthPhysicalClockWindowCount cap),∑i : Fin (dyadicBirthBandCount j),
        D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell z) =
        D.originalClockPieceSupportedWeight ε (.inl (.inl ((1:Fin 2),n,j))) z
    let coeff := originalPairClockSupportMask qdim μ ν z *
      ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ *
        originalClockTrafficRegionMask (D.lo+S.level) (D.hi+S.level) ε 4 z
    have hweight (i ell : ℕ) : D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell z =
        coeff*D.originalRightBirthPhysicalClockMask ε cap n j i ell z := by
      dsimp [coeff,originalSupportedRightBirthPhysicalClockWeight,
        originalSupportedRightBirthPhysicalClockMask]
      ac_rfl
    have hwindow (i : ℕ) : (∑ell : Fin (birthPhysicalClockWindowCount cap),
        D.originalRightBirthPhysicalClockMask ε cap n j i ell z) =
        D.originalRightBirthClockMask ε n j i z := by
      exact (Fin.sum_univ_eq_sum_range (fun ell : ℕ↦
        D.originalRightBirthPhysicalClockMask ε cap n j i ell z) _).trans
          (D.sum_originalRightBirthPhysicalClockMask hε hcap n j i z)
    rw [Finset.sum_comm]
    simp_rw [hweight,←Finset.mul_sum,hwindow]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ↦D.originalRightBirthClockMask ε n j i z) _]
    dsimp [coeff,originalClockPieceSupportedWeight,originalClockTrafficPieceWeight,
      originalClockTrafficPieceMask,originalFocalBirthPieceMask,originalFocalBirthRegionIndex,
      originalSidedBirthClockMask]
    ac_rfl

/-- The finite window/band traffic is one literal birth piece in every scene. -/
theorem sum_originalSupportedBirthWindowTraffic_eq_piece
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {η : (Fin qdim→ℝ)→ℝ} (hη : Measurable η)
    {ε cap : ℝ} (hε : 0<ε) (hcap : 0<cap) (side : Fin 2) (n j : ℕ)
    (scene : LegalMarkedOptimalInputScene qdim) :
    (∑ell : Fin (birthPhysicalClockWindowCount cap),∑i∈Finset.range (dyadicBirthBandCount j),
      legalMarkedCompletePathTraffic qdim (fun z↦originalSeedPathOffset S w z.2 z.1)
        (fun x↦ENNReal.ofReal (η x))
        (if side=0 then D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell
          else D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell) scene) =
      D.originalClockPieceAbsoluteTraffic η ε (.inl (.inl (side,n,j))) scene := by
  let W := fun p : Fin (birthPhysicalClockWindowCount cap) × Fin (dyadicBirthBandCount j)↦
    if side=0 then D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j p.2 p.1
      else D.originalSupportedRightBirthPhysicalClockWeight ε cap n j p.2 p.1
  have hW : ∀p,Measurable (W p) := by
    intro p
    dsimp [W]
    split_ifs
    · exact D.measurable_originalSupportedLeftBirthPhysicalClockWeight hF hw ε cap n j p.2 p.1
    · exact D.measurable_originalSupportedRightBirthPhysicalClockWeight hF hw ε cap n j p.2 p.1
  have hsum (z : MarkClock) : (∑'p,W p z) =
      D.originalClockPieceSupportedWeight ε (.inl (.inl (side,n,j))) z := by
    rw [tsum_fintype,Fintype.sum_prod_type]
    simpa only [W,ite_apply] using
      D.sum_originalSupportedBirthPhysicalClockWeight_eq_piece hε hcap side n j z
  have hs := legalMarkedCompletePathTraffic_tsum_weights
    (fun z : MarkClock↦originalSeedPathOffset S w z.2 z.1)
    (measurable_originalSeedPathOffset_joint S hF hw) hη.ennreal_ofReal W hW scene
  simp only [hsum,tsum_fintype,Fintype.sum_prod_type] at hs
  have hFin (ell : Fin (birthPhysicalClockWindowCount cap)) :
      (∑i : Fin (dyadicBirthBandCount j),legalMarkedCompletePathTraffic qdim
        (fun z↦originalSeedPathOffset S w z.2 z.1) (fun x↦ENNReal.ofReal (η x)) (W (ell,i)) scene) =
      ∑i∈Finset.range (dyadicBirthBandCount j),legalMarkedCompletePathTraffic qdim
        (fun z↦originalSeedPathOffset S w z.2 z.1) (fun x↦ENNReal.ofReal (η x))
        (if side=0 then D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell
          else D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell) scene := by
    exact Fin.sum_univ_eq_sum_range (fun i : ℕ↦legalMarkedCompletePathTraffic qdim
      (fun z↦originalSeedPathOffset S w z.2 z.1) (fun x↦ENNReal.ofReal (η x))
      (if side=0 then D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell
        else D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell) scene) _
  simp_rw [hFin] at hs
  exact hs.symm

/-- The actual full birth-window ENNReal sum used by both focal estimates is
exactly the corresponding supported original region, for every original scene. -/
theorem sum_tsum_originalSupportedBirthWindowTraffic_eq_region
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {η : (Fin qdim→ℝ)→ℝ} (hη : Measurable η)
    {ε cap : ℝ} (hε : 0<ε) (hcap : 0<cap) (side : Fin 2)
    (scene : LegalMarkedOptimalInputScene qdim) :
    (∑ell : Fin (birthPhysicalClockWindowCount cap),∑'nj : ℕ×ℕ,
      ∑i∈Finset.range (dyadicBirthBandCount nj.2),
        legalMarkedCompletePathTraffic qdim (fun z↦originalSeedPathOffset S w z.2 z.1)
          (fun x↦ENNReal.ofReal (η x))
          (if side=0 then D.originalSupportedLeftBirthPhysicalClockWeight ε cap nj.1 nj.2 i ell
            else D.originalSupportedRightBirthPhysicalClockWeight ε cap nj.1 nj.2 i ell) scene) =
      D.originalSupportedClockRegionAbsoluteTraffic η ε (originalFocalBirthRegionIndex side) scene := by
  let traffic := fun (ell : Fin (birthPhysicalClockWindowCount cap)) (nj : ℕ×ℕ)↦
    ∑i∈Finset.range (dyadicBirthBandCount nj.2),
      legalMarkedCompletePathTraffic qdim (fun z↦originalSeedPathOffset S w z.2 z.1)
        (fun x↦ENNReal.ofReal (η x))
        (if side=0 then D.originalSupportedLeftBirthPhysicalClockWeight ε cap nj.1 nj.2 i ell
          else D.originalSupportedRightBirthPhysicalClockWeight ε cap nj.1 nj.2 i ell) scene
  change (∑ell,∑'nj : ℕ×ℕ,traffic ell nj) = _
  calc
    _ = ∑'ell : Fin (birthPhysicalClockWindowCount cap),∑'nj : ℕ×ℕ,traffic ell nj := by
      rw [tsum_fintype]
    _ = ∑'nj : ℕ×ℕ,∑'ell : Fin (birthPhysicalClockWindowCount cap),traffic ell nj := ENNReal.tsum_comm
    _ = ∑'nj : ℕ×ℕ,D.originalClockPieceAbsoluteTraffic η ε (.inl (.inl (side,nj.1,nj.2))) scene := by
      apply tsum_congr
      intro nj
      rw [tsum_fintype]
      exact D.sum_originalSupportedBirthWindowTraffic_eq_piece hF hw hη hε hcap side nj.1 nj.2 scene
    _ = _ := D.tsum_originalFocalBirthPieceAbsoluteTraffic_eq_region hF hw hη hε side scene

/-- The regular piece already is the corresponding supported original region. -/
theorem originalRegularPieceAbsoluteTraffic_eq_region
    (η : (Fin qdim→ℝ)→ℝ) (ε : ℝ) (i : Fin 4)
    (scene : LegalMarkedOptimalInputScene qdim) :
    D.originalClockPieceAbsoluteTraffic η ε (.inr i) scene =
      D.originalSupportedClockRegionAbsoluteTraffic η ε (originalRegularRegionIndex i) scene := rfl

/-- The actual original path is the finite sum of its eight supported region
readouts. The true original Palm law supplies the support and clock identities. -/
theorem ae_original_completePathAbsoluteTraffic_eq_sum_supportedRegions
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ→ℝ→ℝ}
    (Q : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g)
    {η : (Fin qdim→ℝ)→ℝ} (hη : Measurable η) (hηI : Integrable η volume)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᵐ scene∂(Q.law : Measure (LegalMarkedOptimalInputScene qdim)),
      originalSeedCompletePathAbsoluteTraffic S w η scene =
        ∑i : Fin 8,D.originalSupportedClockRegionAbsoluteTraffic η ε i scene := by
  filter_upwards [D.ae_original_completePathAbsoluteTraffic_eq_tsum_clockPieces
    hF hw hbounds Q hη hηI hε] with scene hs
  rw [hs]
  have hsplit : (∑' piece : OriginalClockTrafficPieceIndex,
      D.originalClockPieceAbsoluteTraffic η ε piece scene) =
      (∑side : Fin 2,∑'n : ℕ,∑'j : ℕ,D.originalClockPieceAbsoluteTraffic η ε
        (.inl (.inl (side,n,j))) scene) +
      (∑side : Fin 2,∑'n : ℕ,D.originalClockPieceAbsoluteTraffic η ε
        (.inl (.inr (side,n))) scene) +
      (∑i : Fin 4,D.originalClockPieceAbsoluteTraffic η ε (.inr i) scene) := by
    rw [ENNReal.summable.tsum_sum ENNReal.summable,
      ENNReal.summable.tsum_sum ENNReal.summable]
    simp only [ENNReal.tsum_prod',tsum_fintype]
  rw [hsplit]
  have hbirth (side : Fin 2) : (∑'n : ℕ,∑'j : ℕ,
      D.originalClockPieceAbsoluteTraffic η ε (.inl (.inl (side,n,j))) scene) =
      D.originalSupportedClockRegionAbsoluteTraffic η ε (originalFocalBirthRegionIndex side) scene := by
    simpa only [ENNReal.tsum_prod'] using
      D.tsum_originalFocalBirthPieceAbsoluteTraffic_eq_region hF hw hη hε side scene
  simp_rw [hbirth,D.tsum_originalFocalOldPieceAbsoluteTraffic_eq_region hF hw hη hε,
    D.originalRegularPieceAbsoluteTraffic_eq_region]
  exact sum_originalClockRegionIndex_partition
    (fun i↦D.originalSupportedClockRegionAbsoluteTraffic η ε i scene)

/-- The real-valued eight-region sum is exact: original kinetic finiteness
is established before converting any nonnegative traffic to a real number. -/
theorem ae_toReal_original_completePathAbsoluteTraffic_eq_sum_supportedRegions
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ→ℝ→ℝ}
    (Q : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g)
    {η : (Fin qdim→ℝ)→ℝ} (hη : Measurable η) (hηI : Integrable η volume)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᵐ scene∂(Q.law : Measure (LegalMarkedOptimalInputScene qdim)),
      (originalSeedCompletePathAbsoluteTraffic S w η scene).toReal =
        ∑i : Fin 8,(D.originalSupportedClockRegionAbsoluteTraffic η ε i scene).toReal := by
  filter_upwards [D.ae_original_completePathAbsoluteTraffic_eq_sum_supportedRegions
    hF hw hbounds Q hη hηI hε,
    D.ae_original_completePathAbsoluteTraffic_lt_top hF hw hbounds Q hη hηI] with scene hs hf
  have hfinite : (∑i : Fin 8,D.originalSupportedClockRegionAbsoluteTraffic η ε i scene) ≠ (∞ : ℝ≥0∞) := by
    rw [←hs]
    exact hf.ne
  rw [hs,ENNReal.toReal_sum (ENNReal.sum_ne_top.mp hfinite)]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
