import OTSelector.Reconstruction.MarkedStationaryValueLegalSpatialTypesOriginal
import OTSelector.Reconstruction.MarkedStationaryValueLegalDyadicComparison
import OTSelector.Probability.MarkedGridBlockComparison

/-! Actual forward legal pressure comparison for every natural cube block count. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- A realized child cell determines its spatial parent. -/
def legalGridParent (q m J k : ℕ) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (b : Fin q → Fin (2 ^ (k + 1) + 1)) : Fin q → Fin (2 ^ k + 1) :=
  if h : ∃ x : Fin q → ℝ, gridCellLabel q m J (k + 1) hm hJ x = b then
    gridCellLabel q m J k hm hJ (Classical.choose h)
  else fun _ ↦ 0

theorem legalGridParent_cell (q m J k : ℕ) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (hk : k + 1 ≤ J) (x : Fin q → ℝ) :
    legalGridParent q m J k hm hJ (gridCellLabel q m J (k + 1) hm hJ x) =
      gridCellLabel q m J k hm hJ x := by
  unfold legalGridParent
  split
  · rename_i h
    exact gridCellLabel_nested hm hJ (Nat.le_succ k) hk (Classical.choose_spec h)
  · rename_i h
    exact False.elim (h ⟨x, rfl⟩)

/-- Absolute parent edge budget for the padded uniform grid. -/
def legalGridEdgeBound (q : ℕ) (r C G t : ℝ) (k : ℕ) : ℝ :=
  16 * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ k + |t| * G

theorem legalGridEdgeBound_nonneg (q k : ℕ) {r C G t : ℝ}
    (hr : 0 ≤ r) (hC : 0 ≤ C) (hG : 0 ≤ G) :
    0 ≤ legalGridEdgeBound q r C G t k := by
  unfold legalGridEdgeBound
  positivity

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- Actual allowed edges sharing a dyadic parent satisfy its quadratic budget. -/
theorem abs_legalMarkedEdge_le_same_grid (q m J k : ℕ)
    (hm : 0 < m) (hJ : m ≤ 2 ^ J) (hJ2 : 2 ^ J ≤ 2 * m) (hk : k ≤ J)
    (source : A → ℝ) (target : B → ℝ) {r C G : ℝ}
    (hr : 0 ≤ r) (hC : 0 ≤ C)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkb : ∀ a b, source a < target b → ∀ v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hpb : ∀ a b, source a < target b → |probe a b| ≤ G)
    (t : ℝ) (ω : TwoMarkedCloudSpace q A B) (i j : ℕ)
    (hS : mSourcePoint ω i ∈ unitCube q) (hT : mTargetPoint ω j ∈ unitCube q)
    (hforward : source (mSourceMark ω i) < target (mTargetMark ω j))
    (hcell : gridCellLabel q m J k hm hJ (mSourcePoint ω i) =
      gridCellLabel q m J k hm hJ (mTargetPoint ω j)) :
    |mKineticCost q r kin ω i j + t * mProbe probe ω i j| ≤
      legalGridEdgeBound q r C G t k := by
  have hcoordS (l) : 0 ≤ mSourcePoint ω i l ∧ mSourcePoint ω i l < 1 := by
    have h := Set.mem_pi.mp hS l (mem_univ l)
    exact ⟨h.1.le, h.2⟩
  have hcoordT (l) : 0 ≤ mTargetPoint ω j l ∧ mTargetPoint ω j l < 1 := by
    have h := Set.mem_pi.mp hT l (mem_univ l)
    exact ⟨h.1.le, h.2⟩
  have hsum : ∑ l, (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j) l) ^ 2 ≤
      16 * (q : ℝ) * (1 / 4 : ℝ) ^ k := by
    rw [mDisplacement_eq_sub_of_mem hS hT]
    have heq : (∑ l, (mTargetPoint ω j l - mSourcePoint ω i l) ^ 2) =
        ∑ l, (mSourcePoint ω i l - mTargetPoint ω j l) ^ 2 := by
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [heq]
    exact gridCellLabel_sqDist_le hm hJ hJ2 hk hcoordS hcoordT hcell
  have hkin : |mKineticCost q r kin ω i j| ≤
      16 * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ k := by
    rw [mKineticCost, abs_mul, abs_of_nonneg (Real.rpow_nonneg hr _)]
    calc
      _ ≤ r ^ (2 / (q : ℝ)) * (C * ∑ l,
          (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j) l) ^ 2) :=
        mul_le_mul_of_nonneg_left (hkb _ _ hforward _) (Real.rpow_nonneg hr _)
      _ ≤ r ^ (2 / (q : ℝ)) * (C * (16 * (q : ℝ) * (1 / 4 : ℝ) ^ k)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hC)
          (Real.rpow_nonneg hr _)
      _ = _ := by ring
  have hprobe : |t * mProbe probe ω i j| ≤ |t| * G := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hpb _ _ hforward) (abs_nonneg t)
  exact (abs_add_le _ _).trans (add_le_add hkin hprobe)


/-- The actual original-index legal minimum inside one padded grid cell. -/
def gridLegalValue (q m J k : ℕ) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (source : A → ℝ) (target : B → ℝ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q A B) (b : Fin q → Fin (2 ^ k + 1)) : ℝ :=
  PartialMatching.legalMaximumValue
    (spatialLegalMarkedGraph q (mSourceCount ω) (mTargetCount ω)
      (gridCellLabel q m J k hm hJ) source target b ω)
    (fun i j ↦ mKineticCost q r kin ω i j + t * mProbe probe ω i j)

set_option maxHeartbeats 1000000 in
omit [MeasurableSpace A] [MeasurableSpace B] in
/-- Actual legal grid subadditivity, with all repairs paid at their spatial
parent scale and by original child legal source deficiencies. -/
theorem FiniteScalarBins.legalMarkedTilted_le_grid
    {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ) (hδ : 0 < δ)
    (q m J : ℕ) (hm : 0 < m) (hJ : m ≤ 2 ^ J) (hJ2 : 2 ^ J ≤ 2 * m)
    (source : A → ℝ) (target : B → ℝ) {r C G : ℝ}
    (hr : 0 ≤ r) (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkb : ∀ a b, source a < target b → ∀ v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hpb : ∀ a b, source a < target b → |probe a b| ≤ G)
    (t : ℝ) (ω : TwoMarkedCloudSpace q A B)
    (hS : ∀ i, mSourcePoint ω i ∈ unitCube q)
    (hT : ∀ j, mTargetPoint ω j ∈ unitCube q)
    (hsource : ∀ i, source (mSourceMark ω i) ∈ I)
    (hsep : ∀ i j, δ ≤ |target (mTargetMark ω j) - source (mSourceMark ω i)|) :
    legalMarkedTilted q source target r kin probe t ω ≤
      (∑ b : Fin q → Fin (2 ^ J + 1), gridLegalValue q m J J hm hJ source target r kin probe t ω b) +
      ∑ k ∈ Finset.range J,
        spatialLegalMarkedSourceDefectSum q (gridCellLabel q m J (k + 1) hm hJ) source target ω *
          (2 * ((D.count : ℝ) + 1) * legalGridEdgeBound q r C G t k) := by
  let allowed := legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) source target ω
  let cost := fun i : Fin (mSourceCount ω) ↦ fun j : Fin (mTargetCount ω) ↦
    mKineticCost q r kin ω i j + t * mProbe probe ω i j
  let s := fun k (i : Fin (mSourceCount ω)) ↦ gridCellLabel q m J k hm hJ (mSourcePoint ω i)
  let u := fun k (j : Fin (mTargetCount ω)) ↦ gridCellLabel q m J k hm hJ (mTargetPoint ω j)
  let value := fun k ↦ ∑ b : Fin q → Fin (2 ^ k + 1),
    PartialMatching.legalMaximumValue (PartialMatching.spatialLegalBlock allowed (s k) (u k) b) cost
  let error := fun k ↦ spatialLegalMarkedSourceDefectSum q
    (gridCellLabel q m J (k + 1) hm hJ) source target ω *
      (2 * ((D.count : ℝ) + 1) * legalGridEdgeBound q r C G t k)
  obtain ⟨label, allows, hallowed⟩ := D.exists_source_neighborhood_classes hδ
    (fun i : Fin (mSourceCount ω) ↦ source (mSourceMark ω i))
    (fun j : Fin (mTargetCount ω) ↦ target (mTargetMark ω j))
    (fun i ↦ hsource i) (fun i j ↦ hsep i j)
  have hstep (k : ℕ) (hk : k < J) : value k ≤ value (k + 1) + error k := by
    let parent := legalGridParent q m J k hm hJ
    have hs : parent ∘ s (k + 1) = s k :=
      funext (fun i ↦ legalGridParent_cell q m J k hm hJ (Nat.succ_le_of_lt hk) _)
    have ht : parent ∘ u (k + 1) = u k :=
      funext (fun j ↦ legalGridParent_cell q m J k hm hJ (Nat.succ_le_of_lt hk) _)
    have hv := PartialMatching.sum_parent_legalMaximumValue_le_children_add_deficits allowed
      (s (k + 1)) (u (k + 1)) parent label allows hallowed cost
      (legalGridEdgeBound_nonneg q k hr hC hG)
      (by
        intro i j hij hcell
        have hc : s k i = u k j := by
          change (parent ∘ s (k + 1)) i = (parent ∘ u (k + 1)) j at hcell
          simpa only [hs, ht] using hcell
        apply abs_legalMarkedEdge_le_same_grid q m J k hm hJ hJ2 hk.le source target
          hr hC hkb hpb t ω i j (hS i) (hT j) _ hc
        simpa only [allowed, legalMarkedGraph, Finset.mem_filter, Finset.mem_univ,
          true_and] using hij)
    rw [hs, ht] at hv
    simpa only [value, error, spatialLegalMarkedSourceDefectSum_eq_nat,
      spatialLegalMarkedGraph, s, u, allowed, Fintype.card_option, Fintype.card_fin,
      Nat.cast_add, Nat.cast_one] using hv
  let root := gridCellLabel q m J 0 hm hJ (fun _ ↦ 0)
  have hsroot (i) : s 0 i = root := gridCellLabel_root hm hJ _ _
  have htroot (j) : u 0 j = root := gridCellLabel_root hm hJ _ _
  have hgraph (b : Fin q → Fin (2 ^ 0 + 1)) :
      PartialMatching.spatialLegalBlock allowed (s 0) (u 0) b =
        if b = root then allowed else ∅ := by
    ext e
    by_cases hb : b = root
    · subst b
      simp [PartialMatching.spatialLegalBlock, hsroot, htroot]
    · simp [PartialMatching.spatialLegalBlock, hsroot, htroot, hb, Ne.symm hb]
  have hroot : value 0 = legalMarkedTilted q source target r kin probe t ω := by
    simp [value, hgraph, apply_ite (fun g ↦ PartialMatching.legalMaximumValue g cost)]
    rfl
  have htotal (L : ℕ) (hL : L ≤ J) : value 0 ≤ value L + ∑ k ∈ Finset.range L, error k := by
    induction L with
    | zero => simp
    | succ L ih =>
      have hprev := ih (Nat.le_trans (Nat.le_succ L) hL)
      have hn := hstep L (Nat.lt_of_lt_of_le (Nat.lt_succ_self L) hL)
      rw [Finset.sum_range_succ]
      linarith
  have h := htotal J le_rfl
  simpa only [hroot, value, error, gridLegalValue, spatialLegalMarkedGraph, allowed, cost, s, u] using h

end OTSelector.Reconstruction
