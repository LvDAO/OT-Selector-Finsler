import OTSelector.Reconstruction.OriginalScalarClockMarkChange
import OTSelector.Reconstruction.OriginalMarkedCloudMismatchCount
import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonMap

/-! Original coupled marks preserve positions and counts. Every pressure
change is charged to the actual changed prefix vertices, with fixed coarse
legal repair and the original quadratic edge bound. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Two original readings of one coupled marked cloud differ only at their
actual changed marks. The finite legal objective pays the original coarse
vertex-deletion bound for precisely those indices. -/
theorem abs_legalMarkedTilted_coupled_marks_sub_le
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] (q : ℕ) {range : Set ℝ} {gap : ℝ}
    (coarse : FiniteScalarBins range gap) (hgap : 0 < gap)
    (source : A → ℝ) (target : B → ℝ) (r C G t : ℝ)
    (hr : 0 ≤ r) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hpb : ∀ a b, |probe a b| ≤ G)
    (sample : TwoMarkedCloudSpace q (A × A) (B × B))
    (hS₀ : ∀ i : ℕ, source (mSourceMark sample i).1 ∈ range)
    (hS₁ : ∀ i : ℕ, source (mSourceMark sample i).2 ∈ range)
    (hsep₀ : ∀ i j : ℕ, gap ≤ |target (mTargetMark sample j).1 - source (mSourceMark sample i).1|)
    (hsep₁ : ∀ i j : ℕ, gap ≤ |target (mTargetMark sample j).2 - source (mSourceMark sample i).2|) :
    |legalMarkedTilted q (source ∘ Prod.fst) (target ∘ Prod.fst) r
        (fun a b ↦ kin a.1 b.1) (fun a b ↦ probe a.1 b.1) t sample -
      legalMarkedTilted q (source ∘ Prod.snd) (target ∘ Prod.snd) r
        (fun a b ↦ kin a.2 b.2) (fun a b ↦ probe a.2 b.2) t sample| ≤
      ((markedCloudMismatchCount q sample.1 : ℝ) + markedCloudMismatchCount q sample.2) *
        (4 * ((coarse.count : ℝ) + 1) * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G)) := by
  classical
  let S := Finset.univ.filter (fun i : Fin (mSourceCount sample) ↦
    (mSourceMark sample i).1 ≠ (mSourceMark sample i).2)
  let T := Finset.univ.filter (fun j : Fin (mTargetCount sample) ↦
    (mTargetMark sample j).1 ≠ (mTargetMark sample j).2)
  have hS i (hi : i ∉ S) : (mSourceMark sample i).1 = (mSourceMark sample i).2 := by
    by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  have hT j (hj : j ∉ T) : (mTargetMark sample j).1 = (mTargetMark sample j).2 := by
    by_contra h
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  have hScard : S.card = markedCloudMismatchCount q sample.1 := by
    simp only [S,markedCloudMismatchCount,poissonPrefixCount,mSourceCount,mSourceMark,mem_ofPred_eq]
  have hTcard : T.card = markedCloudMismatchCount q sample.2 := by
    simp only [T,markedCloudMismatchCount,poissonPrefixCount,mTargetCount,mTargetMark,mem_ofPred_eq]
  let c₀ := fun i : Fin (mSourceCount sample) ↦ fun j : Fin (mTargetCount sample) ↦
    mKineticCost q r (fun a b ↦ kin a.1 b.1) sample i j + t * mProbe (fun a b ↦ probe a.1 b.1) sample i j
  let c₁ := fun i : Fin (mSourceCount sample) ↦ fun j : Fin (mTargetCount sample) ↦
    mKineticCost q r (fun a b ↦ kin a.2 b.2) sample i j + t * mProbe (fun a b ↦ probe a.2 b.2) sample i j
  have hcost i j (hi : i ∉ S) (hj : j ∉ T) : c₀ i j = c₁ i j := by
    simp only [c₀,c₁,mKineticCost,mProbe,hS i hi,hT j hj]
  have hB : 0 ≤ r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G := by positivity
  have hb₀ i j : |c₀ i j| ≤ r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G := by
    calc
      _ ≤ |mKineticCost q r (fun a b ↦ kin a.1 b.1) sample i j| +
          |t| * |mProbe (fun a b ↦ probe a.1 b.1) sample i j| := by
        simpa only [c₀,abs_mul] using abs_add_le
          (mKineticCost q r (fun a b ↦ kin a.1 b.1) sample i j)
          (t * mProbe (fun a b ↦ probe a.1 b.1) sample i j)
      _ ≤ _ := add_le_add (abs_mKineticCost_le q hr hC (fun a b v ↦ hkb a.1 b.1 v) sample i j)
        (mul_le_mul_of_nonneg_left (hpb _ _) (abs_nonneg t))
  have hb₁ i j : |c₁ i j| ≤ r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G := by
    calc
      _ ≤ |mKineticCost q r (fun a b ↦ kin a.2 b.2) sample i j| +
          |t| * |mProbe (fun a b ↦ probe a.2 b.2) sample i j| := by
        simpa only [c₁,abs_mul] using abs_add_le
          (mKineticCost q r (fun a b ↦ kin a.2 b.2) sample i j)
          (t * mProbe (fun a b ↦ probe a.2 b.2) sample i j)
      _ ≤ _ := add_le_add (abs_mKineticCost_le q hr hC (fun a b v ↦ hkb a.2 b.2 v) sample i j)
        (mul_le_mul_of_nonneg_left (hpb _ _) (abs_nonneg t))
  have hb := coarse.abs_legalMaximumValue_mark_change_le hgap
    (fun i ↦ source (mSourceMark sample i).1) (fun i ↦ source (mSourceMark sample i).2)
    (fun j ↦ target (mTargetMark sample j).1) (fun j ↦ target (mTargetMark sample j).2)
    (fun i ↦ hS₀ i) (fun i ↦ hS₁ i) (fun i j ↦ hsep₀ i j) (fun i j ↦ hsep₁ i j)
    S T (fun i hi ↦ congrArg source (hS i hi)) (fun j hj ↦ congrArg target (hT j hj))
    c₀ c₁ hcost hB (fun i j _ ↦ hb₀ i j) (fun i j _ ↦ hb₁ i j)
  change |PartialMatching.legalMaximumValue
      (scalarClockLegalGraph (fun i : Fin (mSourceCount sample) ↦ source (mSourceMark sample i).1)
        (fun j : Fin (mTargetCount sample) ↦ target (mTargetMark sample j).1)) c₀ -
    PartialMatching.legalMaximumValue
      (scalarClockLegalGraph (fun i : Fin (mSourceCount sample) ↦ source (mSourceMark sample i).2)
        (fun j : Fin (mTargetCount sample) ↦ target (mTargetMark sample j).2)) c₁| ≤ _
  simpa only [hScard,hTcard,Nat.cast_add] using hb

end OTSelector.Reconstruction
