import OTSelector.Probability.MarkedPressureScale
import OTSelector.Reconstruction.MarkedStationaryValueLegalSubcloudStability
import OTSelector.Reconstruction.MarkedStationaryValueLegalPressureRegularity
import OTSelector.Probability.MarkedCloudCarriers

/-! Shared-prefix intensity coupling for the original legal Poisson problem. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem map_preSmallCloud (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ δ : ℝ≥0) :
    (markedPreCouple q A B α β ρ δ).map (preSmallCloud (q := q)) =
      twoMarkedCloudLaw q A B α β ρ := by
  have h := Measure.map_map (μ := markedPreCouple q A B α β ρ δ)
    (measurable_smallPair (q := q) (A := A) (B := B))
    (measurable_preCoupleMap (q := q) (A := A) (B := B))
  rw [← twoCloudCouple_eq_map_markedPreCouple, twoCloudCouple_map_small] at h
  exact h.symm

theorem map_preLargeCloud (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ δ : ℝ≥0) :
    (markedPreCouple q A B α β ρ δ).map (preLargeCloud (q := q)) =
      twoMarkedCloudLaw q A B α β (ρ + δ) := by
  have h := Measure.map_map (μ := markedPreCouple q A B α β ρ δ)
    (measurable_largePair (q := q) (A := A) (B := B))
    (measurable_preCoupleMap (q := q) (A := A) (B := B))
  rw [← twoCloudCouple_eq_map_markedPreCouple, twoCloudCouple_map_large] at h
  exact h.symm

end OTSelector.Probability
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- A kinetic-scale change is paid by the actual legal rank, bounded here by the
original source count. The legal graph and probe stay literal. -/
theorem abs_legalMarkedTilted_scale_sub_le (q : ℕ)
    (source : A → ℝ) (target : B → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (kin : A → B → (Fin q → ℝ) → ℝ)
    (hkin : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (g : A → B → ℝ) (t r s : ℝ) (ω : TwoMarkedCloudSpace q A B) :
    |legalMarkedTilted q source target r kin g t ω -
      legalMarkedTilted q source target s kin g t ω| ≤
      (mSourceCount ω : ℝ) * (C * q * |r ^ (2 / (q : ℝ)) - s ^ (2 / (q : ℝ))|) := by
  let H := C * q * |r ^ (2 / (q : ℝ)) - s ^ (2 / (q : ℝ))|
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hentry (i : Fin (mSourceCount ω)) (j : Fin (mTargetCount ω)) :
      |(mKineticCost q r kin ω i j + t * mProbe g ω i j) -
        (mKineticCost q s kin ω i j + t * mProbe g ω i j)| ≤ H := by
    have hk : |kin (mSourceMark ω i) (mTargetMark ω j)
        (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j))| ≤ C * q :=
      (hkin _ _ _).trans (mul_le_mul_of_nonneg_left
        (mDisplacement_sq_sum_le q _ _) hC)
    have heq : (mKineticCost q r kin ω i j + t * mProbe g ω i j) -
        (mKineticCost q s kin ω i j + t * mProbe g ω i j) =
        (r ^ (2 / (q : ℝ)) - s ^ (2 / (q : ℝ))) *
          kin (mSourceMark ω i) (mTargetMark ω j)
            (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j)) := by
      unfold mKineticCost
      ring
    rw [heq, abs_mul]
    exact (mul_le_mul_of_nonneg_left hk (abs_nonneg _)).trans_eq (by dsimp [H]; ring)
  have h := PartialMatching.abs_legalMaximumValue_sub_le_of_allowed
    (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) source target ω)
    (fun i j ↦ mKineticCost q r kin ω i j + t * mProbe g ω i j)
    (fun i j ↦ mKineticCost q s kin ω i j + t * mProbe g ω i j)
    (fun i j _ ↦ hentry i j)
  exact h.trans (mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr ((PartialMatching.legalMaximumCard_le_min _).trans (min_le_left _ _))) hH)

/-- Actual shared-prefix vertex addition at a fixed kinetic scale. -/
theorem FiniteScalarBins.abs_legalMarkedTilted_preSmall_sub_preLarge
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (q : ℕ) (source : A → ℝ) (target : B → ℝ)
    {r C G : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (kin : A → B → (Fin q → ℝ) → ℝ)
    (hkin : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (g : A → B → ℝ) (hg : ∀ a b, |g a b| ≤ G) (t : ℝ)
    (z : MarkedPreCoupleSpace q A B)
    (hsource : ∀ i : ℕ, source (pcSourceMark z i) ∈ I)
    (hsep : ∀ i j : ℕ, gap ≤ |target (pcTargetMark z j) - source (pcSourceMark z i)|) :
    |legalMarkedTilted q source target r kin g t (preSmallCloud z) -
      legalMarkedTilted q source target r kin g t (preLargeCloud z)| ≤
      ((pcExtraSource z : ℝ) + (pcExtraTarget z : ℝ)) *
        (2 * ((D.count : ℝ) + 1) * (r ^ (2 / (q : ℝ)) * (C * q) + |t| * G)) := by
  let e := Fin.castAddEmb (n := pcSourceCount z) (pcExtraSource z)
  let f := Fin.castAddEmb (n := pcTargetCount z) (pcExtraTarget z)
  have hB : 0 ≤ r ^ (2 / (q : ℝ)) * (C * q) + |t| * G := by positivity
  have h := D.abs_legalMaximumValue_subcloud_sub_le hgap
    (fun i : Fin (pcSourceCount z + pcExtraSource z) ↦ source (pcSourceMark z i))
    (fun j : Fin (pcTargetCount z + pcExtraTarget z) ↦ target (pcTargetMark z j))
    (fun i ↦ hsource i) (fun i j ↦ hsep i j) e f
    (fun i j ↦ pcEntry q r kin g t z i j) hB
    (fun i j _ ↦ abs_pcEntry_le q hr hC hkin hg z i j)
  have hcounts : (pcSourceCount z + pcExtraSource z - pcSourceCount z) +
      (pcTargetCount z + pcExtraTarget z - pcTargetCount z) =
      pcExtraSource z + pcExtraTarget z := by omega
  simp only [hcounts, Nat.cast_add] at h
  change |legalMarkedTilted q source target r kin g t (preSmallCloud z) -
    legalMarkedTilted q source target r kin g t (preLargeCloud z)| ≤ _ at h
  exact h

end OTSelector.Reconstruction
