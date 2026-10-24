import OTSelector.Reconstruction.FinslerOriginalBirthPhysicalClockMasks
import OTSelector.Reconstruction.OriginalCompletePathCountableWeights
import OTSelector.Reconstruction.OriginalCompletePathAbsoluteTraffic

/-! Literal original birth-band traffic equals the finite sum of its physical
clock-window pieces. The same correlated outer mask and original band energy
are retained in every piece and in the identity. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Topology BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "MarkClock" => PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ

/-- The actual original band traffic, retaining an arbitrary correlated outer mask. -/
def originalLeftBirthBandAbsoluteTraffic
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) (θ : MarkClock → ℝ≥0∞)
    (ε : ℝ) (n j i : ℕ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ≥0∞ :=
  legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
    (fun z ↦ originalSeedPathOffset S w z.2 z.1) (fun x ↦ ENNReal.ofReal (η x))
    (fun z ↦ ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * θ z *
      D.originalLeftBirthClockMask ε n j i z) s

/-- The actual traffic restricted to one unchanged physical clock subwindow. -/
def originalLeftBirthWindowAbsoluteTraffic
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) (θ : MarkClock → ℝ≥0∞)
    (ε cap : ℝ) (n j i ell : ℕ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ≥0∞ :=
  legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
    (fun z ↦ originalSeedPathOffset S w z.2 z.1) (fun x ↦ ENNReal.ofReal (η x))
    (fun z ↦ ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * θ z *
      D.originalLeftBirthPhysicalClockMask ε cap n j i ell z) s

theorem measurable_originalLeftBirthBandAbsoluteTraffic
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    {θ : MarkClock → ℝ≥0∞} (hθ : Measurable θ) (ε : ℝ) (n j i : ℕ) :
    Measurable (D.originalLeftBirthBandAbsoluteTraffic η θ ε n j i) :=
  measurable_legalMarkedCompletePathTraffic _ (measurable_originalSeedPathOffset_joint S hF hw)
    hη.ennreal_ofReal (((measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul hθ).mul
      (D.measurable_originalLeftBirthClockMask ε n j i))

theorem measurable_originalLeftBirthWindowAbsoluteTraffic
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    {θ : MarkClock → ℝ≥0∞} (hθ : Measurable θ) (ε cap : ℝ) (n j i ell : ℕ) :
    Measurable (D.originalLeftBirthWindowAbsoluteTraffic η θ ε cap n j i ell) :=
  measurable_legalMarkedCompletePathTraffic _ (measurable_originalSeedPathOffset_joint S hF hw)
    hη.ennreal_ofReal (((measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul hθ).mul
      (D.measurable_originalLeftBirthPhysicalClockMask ε cap n j i ell))

/-- The finite physical-window sum is literally the same original birth-band
traffic in every scene. No probability or independence assumption is used. -/
theorem sum_originalLeftBirthWindowAbsoluteTraffic
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    {θ : MarkClock → ℝ≥0∞} (hθ : Measurable θ)
    {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap) (n j i : ℕ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    (∑ ell : Fin (birthPhysicalClockWindowCount cap),
      D.originalLeftBirthWindowAbsoluteTraffic η θ ε cap n j i ell s) =
        D.originalLeftBirthBandAbsoluteTraffic η θ ε n j i s := by
  let d := fun z : MarkClock ↦ originalSeedPathOffset S w z.2 z.1
  let parts := fun ell : Fin (birthPhysicalClockWindowCount cap) ↦ fun z : MarkClock ↦
    ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * θ z *
      D.originalLeftBirthPhysicalClockMask ε cap n j i ell z
  have hp : ∀ ell, Measurable (parts ell) := fun ell ↦
    ((measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul hθ).mul
      (D.measurable_originalLeftBirthPhysicalClockMask ε cap n j i ell)
  have hweights (z : MarkClock) : (∑' ell, parts ell z) =
      ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * θ z *
        D.originalLeftBirthClockMask ε n j i z := by
    have hs : (∑ ell : Fin (birthPhysicalClockWindowCount cap),
        D.originalLeftBirthPhysicalClockMask ε cap n j i ell z) =
        D.originalLeftBirthClockMask ε n j i z := by
      have hFin := Fin.sum_univ_eq_sum_range (fun ell : ℕ ↦
        D.originalLeftBirthPhysicalClockMask ε cap n j i ell z) (birthPhysicalClockWindowCount cap)
      exact hFin.trans (D.sum_originalLeftBirthPhysicalClockMask hε hcap n j i z)
    rw [tsum_fintype]
    change (∑ ell : Fin (birthPhysicalClockWindowCount cap),
      (ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * θ z) *
        D.originalLeftBirthPhysicalClockMask ε cap n j i ell z) = _
    rw [← Finset.mul_sum, hs]
  have hreadout := legalMarkedCompletePathTraffic_tsum_weights d
    (measurable_originalSeedPathOffset_joint S hF hw) hη.ennreal_ofReal parts hp s
  rw [tsum_fintype] at hreadout
  change (∑ ell : Fin (birthPhysicalClockWindowCount cap),
    legalMarkedCompletePathTraffic _ d _ (parts ell) s) = _
  rw [← hreadout]
  apply congrArg (fun f ↦ legalMarkedCompletePathTraffic _ d (fun x ↦ ENNReal.ofReal (η x)) f s)
  exact funext hweights


/-- The actual original band traffic, retaining an arbitrary correlated outer mask. -/
def originalRightBirthBandAbsoluteTraffic
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) (θ : MarkClock → ℝ≥0∞)
    (ε : ℝ) (n j i : ℕ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ≥0∞ :=
  legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
    (fun z ↦ originalSeedPathOffset S w z.2 z.1) (fun x ↦ ENNReal.ofReal (η x))
    (fun z ↦ ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * θ z *
      D.originalRightBirthClockMask ε n j i z) s

/-- The actual traffic restricted to one unchanged physical clock subwindow. -/
def originalRightBirthWindowAbsoluteTraffic
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) (θ : MarkClock → ℝ≥0∞)
    (ε cap : ℝ) (n j i ell : ℕ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ≥0∞ :=
  legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
    (fun z ↦ originalSeedPathOffset S w z.2 z.1) (fun x ↦ ENNReal.ofReal (η x))
    (fun z ↦ ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * θ z *
      D.originalRightBirthPhysicalClockMask ε cap n j i ell z) s

theorem measurable_originalRightBirthBandAbsoluteTraffic
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    {θ : MarkClock → ℝ≥0∞} (hθ : Measurable θ) (ε : ℝ) (n j i : ℕ) :
    Measurable (D.originalRightBirthBandAbsoluteTraffic η θ ε n j i) :=
  measurable_legalMarkedCompletePathTraffic _ (measurable_originalSeedPathOffset_joint S hF hw)
    hη.ennreal_ofReal (((measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul hθ).mul
      (D.measurable_originalRightBirthClockMask ε n j i))

theorem measurable_originalRightBirthWindowAbsoluteTraffic
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    {θ : MarkClock → ℝ≥0∞} (hθ : Measurable θ) (ε cap : ℝ) (n j i ell : ℕ) :
    Measurable (D.originalRightBirthWindowAbsoluteTraffic η θ ε cap n j i ell) :=
  measurable_legalMarkedCompletePathTraffic _ (measurable_originalSeedPathOffset_joint S hF hw)
    hη.ennreal_ofReal (((measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul hθ).mul
      (D.measurable_originalRightBirthPhysicalClockMask ε cap n j i ell))

/-- The finite physical-window sum is literally the same original birth-band
traffic in every scene. No probability or independence assumption is used. -/
theorem sum_originalRightBirthWindowAbsoluteTraffic
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    {θ : MarkClock → ℝ≥0∞} (hθ : Measurable θ)
    {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap) (n j i : ℕ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    (∑ ell : Fin (birthPhysicalClockWindowCount cap),
      D.originalRightBirthWindowAbsoluteTraffic η θ ε cap n j i ell s) =
        D.originalRightBirthBandAbsoluteTraffic η θ ε n j i s := by
  let d := fun z : MarkClock ↦ originalSeedPathOffset S w z.2 z.1
  let parts := fun ell : Fin (birthPhysicalClockWindowCount cap) ↦ fun z : MarkClock ↦
    ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * θ z *
      D.originalRightBirthPhysicalClockMask ε cap n j i ell z
  have hp : ∀ ell, Measurable (parts ell) := fun ell ↦
    ((measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul hθ).mul
      (D.measurable_originalRightBirthPhysicalClockMask ε cap n j i ell)
  have hweights (z : MarkClock) : (∑' ell, parts ell z) =
      ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * θ z *
        D.originalRightBirthClockMask ε n j i z := by
    have hs : (∑ ell : Fin (birthPhysicalClockWindowCount cap),
        D.originalRightBirthPhysicalClockMask ε cap n j i ell z) =
        D.originalRightBirthClockMask ε n j i z := by
      have hFin := Fin.sum_univ_eq_sum_range (fun ell : ℕ ↦
        D.originalRightBirthPhysicalClockMask ε cap n j i ell z) (birthPhysicalClockWindowCount cap)
      exact hFin.trans (D.sum_originalRightBirthPhysicalClockMask hε hcap n j i z)
    rw [tsum_fintype]
    change (∑ ell : Fin (birthPhysicalClockWindowCount cap),
      (ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * θ z) *
        D.originalRightBirthPhysicalClockMask ε cap n j i ell z) = _
    rw [← Finset.mul_sum, hs]
  have hreadout := legalMarkedCompletePathTraffic_tsum_weights d
    (measurable_originalSeedPathOffset_joint S hF hw) hη.ennreal_ofReal parts hp s
  rw [tsum_fintype] at hreadout
  change (∑ ell : Fin (birthPhysicalClockWindowCount cap),
    legalMarkedCompletePathTraffic _ d _ (parts ell) s) = _
  rw [← hreadout]
  apply congrArg (fun f ↦ legalMarkedCompletePathTraffic _ d (fun x ↦ ENNReal.ofReal (η x)) f s)
  exact funext hweights

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
