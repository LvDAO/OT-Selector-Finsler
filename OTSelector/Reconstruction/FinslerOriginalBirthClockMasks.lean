import OTSelector.MeasureTheory.DyadicBirthClockMasks
import OTSelector.Reconstruction.FinslerOriginalConditionalMoments
import OTSelector.Reconstruction.MarkedStationaryValuePalmScene

/-! # Exact birth masks on the original paired-mark and physical-clock carrier -/
open Set Function MeasureTheory Module Manifold
open scoped ContDiff ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "MarkClock" => PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ

/-- Actual left inward and strictly positive elapsed coordinates. -/
def originalLeftBirthClockCoordinates (z : MarkClock) : ℝ × ℝ :=
  (z.1.1.1 - S.level - D.lo, z.2 - z.1.1.1)

def originalLeftBirthClockCell (ε : ℝ) (k : ℕ × ℕ × ℕ) : Set MarkClock :=
  D.originalLeftBirthClockCoordinates ⁻¹' dyadicBirthClockCell ε k

/-- The actual triple birth mask; invalid narrow-band indices vanish identically. -/
def originalLeftBirthClockMask (ε : ℝ) (n j i : ℕ) (z : MarkClock) : ℝ≥0∞ :=
  dyadicBirthClockMask ε (n, j, i) (D.originalLeftBirthClockCoordinates z)

def originalLeftBirthClockRegionMask (ε : ℝ) (z : MarkClock) : ℝ≥0∞ :=
  dyadicBirthClockRegionMask ε (D.originalLeftBirthClockCoordinates z)

theorem measurable_originalLeftBirthClockCoordinates :
    Measurable D.originalLeftBirthClockCoordinates :=
  ((measurable_fst.fst.fst.sub measurable_const).sub measurable_const).prodMk
    (measurable_snd.sub measurable_fst.fst.fst)

theorem measurableSet_originalLeftBirthClockCell (ε : ℝ) (k : ℕ × ℕ × ℕ) :
    MeasurableSet (D.originalLeftBirthClockCell ε k) :=
  (measurableSet_dyadicBirthClockCell ε k).preimage
    D.measurable_originalLeftBirthClockCoordinates

theorem measurable_originalLeftBirthClockMask (ε : ℝ) (n j i : ℕ) :
    Measurable (D.originalLeftBirthClockMask ε n j i) :=
  (measurable_dyadicBirthClockMask ε (n, j, i)).comp
    D.measurable_originalLeftBirthClockCoordinates

theorem measurable_originalLeftBirthClockRegionMask (ε : ℝ) :
    Measurable (D.originalLeftBirthClockRegionMask ε) :=
  (measurable_dyadicBirthClockRegionMask ε).comp
    D.measurable_originalLeftBirthClockCoordinates

theorem pairwise_disjoint_originalLeftBirthClockCell {ε : ℝ} (hε : 0 < ε) :
    Pairwise (fun k l : ℕ × ℕ × ℕ ↦
      Disjoint (D.originalLeftBirthClockCell ε k) (D.originalLeftBirthClockCell ε l)) := by
  intro k l hkl
  exact (pairwise_disjoint_dyadicBirthClockCell hε hkl).preimage _

theorem originalLeftBirthClockMask_ne_zero_iff_cell
    (ε : ℝ) (n j i : ℕ) (z : MarkClock) :
    D.originalLeftBirthClockMask ε n j i z ≠ 0 ↔
      z ∈ D.originalLeftBirthClockCell ε (n, j, i) :=
  dyadicBirthClockMask_ne_zero_iff ε (n, j, i) (D.originalLeftBirthClockCoordinates z)

theorem originalLeftBirthClockMask_eq_zero_of_invalid (ε : ℝ) (n j i : ℕ)
    (hi : dyadicBirthBandCount j ≤ i) (z : MarkClock) :
    D.originalLeftBirthClockMask ε n j i z = 0 :=
  dyadicBirthClockMask_eq_zero_of_invalid ε n j i hi (D.originalLeftBirthClockCoordinates z)

theorem originalLeftBirthClockMask_le_one (ε : ℝ) (n j i : ℕ) (z : MarkClock) :
    D.originalLeftBirthClockMask ε n j i z ≤ 1 :=
  dyadicBirthClockMask_le_one ε (n, j, i) (D.originalLeftBirthClockCoordinates z)

/-- The actual full birth region is exactly the countable sum of its triple masks. -/
theorem tsum_originalLeftBirthClockMask {ε : ℝ} (hε : 0 < ε) (z : MarkClock) :
    (∑' k : ℕ × ℕ × ℕ, D.originalLeftBirthClockMask ε k.1 k.2.1 k.2.2 z) =
      D.originalLeftBirthClockRegionMask ε z :=
  tsum_dyadicBirthClockMask hε (D.originalLeftBirthClockCoordinates z)

/-- The final index remains the actual finite family of original clock bands. -/
theorem tsum_finiteSum_originalLeftBirthClockMask {ε : ℝ} (hε : 0 < ε) (z : MarkClock) :
    (∑' n : ℕ, ∑' j : ℕ, ∑ i ∈ Finset.range (dyadicBirthBandCount j),
      D.originalLeftBirthClockMask ε n j i z) = D.originalLeftBirthClockRegionMask ε z :=
  tsum_finiteSum_dyadicBirthClockMask hε (D.originalLeftBirthClockCoordinates z)

/-- Arbitrary additional original-data masks are retained pointwise and exactly. -/
theorem tsum_weighted_originalLeftBirthClockMask {ε : ℝ} (hε : 0 < ε)
    (θ : MarkClock → ℝ≥0∞) (z : MarkClock) :
    (∑' k : ℕ × ℕ × ℕ, θ z * D.originalLeftBirthClockMask ε k.1 k.2.1 k.2.2 z) =
      θ z * D.originalLeftBirthClockRegionMask ε z := by
  rw [ENNReal.tsum_mul_left, D.tsum_originalLeftBirthClockMask hε]

theorem tsum_finiteSum_weighted_originalLeftBirthClockMask {ε : ℝ} (hε : 0 < ε)
    (θ : MarkClock → ℝ≥0∞) (z : MarkClock) :
    (∑' n : ℕ, ∑' j : ℕ, ∑ i ∈ Finset.range (dyadicBirthBandCount j),
      θ z * D.originalLeftBirthClockMask ε n j i z) =
        θ z * D.originalLeftBirthClockRegionMask ε z := by
  simp_rw [← Finset.mul_sum, ENNReal.tsum_mul_left]
  rw [D.tsum_finiteSum_originalLeftBirthClockMask hε]

/-- Actual right inward and strictly positive elapsed coordinates. -/
def originalRightBirthClockCoordinates (z : MarkClock) : ℝ × ℝ :=
  (D.hi - (z.1.1.2 - S.level), z.1.1.2 - z.2)

def originalRightBirthClockCell (ε : ℝ) (k : ℕ × ℕ × ℕ) : Set MarkClock :=
  D.originalRightBirthClockCoordinates ⁻¹' dyadicBirthClockCell ε k

/-- The actual triple birth mask; invalid narrow-band indices vanish identically. -/
def originalRightBirthClockMask (ε : ℝ) (n j i : ℕ) (z : MarkClock) : ℝ≥0∞ :=
  dyadicBirthClockMask ε (n, j, i) (D.originalRightBirthClockCoordinates z)

def originalRightBirthClockRegionMask (ε : ℝ) (z : MarkClock) : ℝ≥0∞ :=
  dyadicBirthClockRegionMask ε (D.originalRightBirthClockCoordinates z)

theorem measurable_originalRightBirthClockCoordinates :
    Measurable D.originalRightBirthClockCoordinates :=
  (measurable_const.sub (measurable_fst.fst.snd.sub measurable_const)).prodMk
    (measurable_fst.fst.snd.sub measurable_snd)

theorem measurableSet_originalRightBirthClockCell (ε : ℝ) (k : ℕ × ℕ × ℕ) :
    MeasurableSet (D.originalRightBirthClockCell ε k) :=
  (measurableSet_dyadicBirthClockCell ε k).preimage
    D.measurable_originalRightBirthClockCoordinates

theorem measurable_originalRightBirthClockMask (ε : ℝ) (n j i : ℕ) :
    Measurable (D.originalRightBirthClockMask ε n j i) :=
  (measurable_dyadicBirthClockMask ε (n, j, i)).comp
    D.measurable_originalRightBirthClockCoordinates

theorem measurable_originalRightBirthClockRegionMask (ε : ℝ) :
    Measurable (D.originalRightBirthClockRegionMask ε) :=
  (measurable_dyadicBirthClockRegionMask ε).comp
    D.measurable_originalRightBirthClockCoordinates

theorem pairwise_disjoint_originalRightBirthClockCell {ε : ℝ} (hε : 0 < ε) :
    Pairwise (fun k l : ℕ × ℕ × ℕ ↦
      Disjoint (D.originalRightBirthClockCell ε k) (D.originalRightBirthClockCell ε l)) := by
  intro k l hkl
  exact (pairwise_disjoint_dyadicBirthClockCell hε hkl).preimage _

theorem originalRightBirthClockMask_ne_zero_iff_cell
    (ε : ℝ) (n j i : ℕ) (z : MarkClock) :
    D.originalRightBirthClockMask ε n j i z ≠ 0 ↔
      z ∈ D.originalRightBirthClockCell ε (n, j, i) :=
  dyadicBirthClockMask_ne_zero_iff ε (n, j, i) (D.originalRightBirthClockCoordinates z)

theorem originalRightBirthClockMask_eq_zero_of_invalid (ε : ℝ) (n j i : ℕ)
    (hi : dyadicBirthBandCount j ≤ i) (z : MarkClock) :
    D.originalRightBirthClockMask ε n j i z = 0 :=
  dyadicBirthClockMask_eq_zero_of_invalid ε n j i hi (D.originalRightBirthClockCoordinates z)

theorem originalRightBirthClockMask_le_one (ε : ℝ) (n j i : ℕ) (z : MarkClock) :
    D.originalRightBirthClockMask ε n j i z ≤ 1 :=
  dyadicBirthClockMask_le_one ε (n, j, i) (D.originalRightBirthClockCoordinates z)

/-- The actual full birth region is exactly the countable sum of its triple masks. -/
theorem tsum_originalRightBirthClockMask {ε : ℝ} (hε : 0 < ε) (z : MarkClock) :
    (∑' k : ℕ × ℕ × ℕ, D.originalRightBirthClockMask ε k.1 k.2.1 k.2.2 z) =
      D.originalRightBirthClockRegionMask ε z :=
  tsum_dyadicBirthClockMask hε (D.originalRightBirthClockCoordinates z)

/-- The final index remains the actual finite family of original clock bands. -/
theorem tsum_finiteSum_originalRightBirthClockMask {ε : ℝ} (hε : 0 < ε) (z : MarkClock) :
    (∑' n : ℕ, ∑' j : ℕ, ∑ i ∈ Finset.range (dyadicBirthBandCount j),
      D.originalRightBirthClockMask ε n j i z) = D.originalRightBirthClockRegionMask ε z :=
  tsum_finiteSum_dyadicBirthClockMask hε (D.originalRightBirthClockCoordinates z)

/-- Arbitrary additional original-data masks are retained pointwise and exactly. -/
theorem tsum_weighted_originalRightBirthClockMask {ε : ℝ} (hε : 0 < ε)
    (θ : MarkClock → ℝ≥0∞) (z : MarkClock) :
    (∑' k : ℕ × ℕ × ℕ, θ z * D.originalRightBirthClockMask ε k.1 k.2.1 k.2.2 z) =
      θ z * D.originalRightBirthClockRegionMask ε z := by
  rw [ENNReal.tsum_mul_left, D.tsum_originalRightBirthClockMask hε]

theorem tsum_finiteSum_weighted_originalRightBirthClockMask {ε : ℝ} (hε : 0 < ε)
    (θ : MarkClock → ℝ≥0∞) (z : MarkClock) :
    (∑' n : ℕ, ∑' j : ℕ, ∑ i ∈ Finset.range (dyadicBirthBandCount j),
      θ z * D.originalRightBirthClockMask ε n j i z) =
        θ z * D.originalRightBirthClockRegionMask ε z := by
  simp_rw [← Finset.mul_sum, ENNReal.tsum_mul_left]
  rw [D.tsum_finiteSum_originalRightBirthClockMask hε]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
