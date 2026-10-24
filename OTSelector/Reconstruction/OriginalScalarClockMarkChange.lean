import OTSelector.Reconstruction.MarkedStationaryValueLegalSubcloudStability

/-! True scalar-legal matching values are stable under changing original
marks. Every changed original vertex is explicitly deleted, and the common
unchanged graph retains its literal original costs. -/
open Set Function
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Changing original mark indices costs only their actual number, with one
fixed coarse scalar-bin constant. Both original legal graphs may differ. -/
theorem FiniteScalarBins.abs_legalMaximumValue_mark_change_le
    {range : Set ℝ} {gap : ℝ} (coarse : FiniteScalarBins range gap) (hgap : 0 < gap)
    {m n : ℕ} (source source' : Fin m → ℝ) (target target' : Fin n → ℝ)
    (hsource : ∀ i, source i ∈ range) (hsource' : ∀ i, source' i ∈ range)
    (hsep : ∀ i j, gap ≤ |target j - source i|)
    (hsep' : ∀ i j, gap ≤ |target' j - source' i|)
    (S : Finset (Fin m)) (T : Finset (Fin n))
    (hsourceEq : ∀ i, i ∉ S → source i = source' i)
    (htargetEq : ∀ j, j ∉ T → target j = target' j)
    (c c' : Fin m → Fin n → ℝ)
    (hcostEq : ∀ i j, i ∉ S → j ∉ T → c i j = c' i j)
    {B : ℝ} (hB : 0 ≤ B)
    (hc : ∀ i j, (i,j) ∈ scalarClockLegalGraph source target → |c i j| ≤ B)
    (hc' : ∀ i j, (i,j) ∈ scalarClockLegalGraph source' target' → |c' i j| ≤ B) :
    |PartialMatching.legalMaximumValue (scalarClockLegalGraph source target) c -
      PartialMatching.legalMaximumValue (scalarClockLegalGraph source' target') c'| ≤
        ((S.card + T.card : ℕ) : ℝ) * (4 * ((coarse.count : ℝ) + 1) * B) := by
  classical
  have hgraph : PartialMatching.vertexDeletedGraph (scalarClockLegalGraph source target) S T =
      PartialMatching.vertexDeletedGraph (scalarClockLegalGraph source' target') S T := by
    ext e
    by_cases hs : e.1 ∈ S
    · simp only [PartialMatching.vertexDeletedGraph,Finset.mem_filter,hs,not_true_eq_false,false_and,and_false]
    · by_cases ht : e.2 ∈ T
      · simp only [PartialMatching.vertexDeletedGraph,Finset.mem_filter,ht,not_true_eq_false,and_false]
      · simp only [PartialMatching.vertexDeletedGraph,scalarClockLegalGraph,Finset.mem_filter,
          Finset.mem_univ,true_and,hs,ht,not_false_eq_true,and_true,hsourceEq _ hs,htargetEq _ ht]
  have hsmall : PartialMatching.legalMaximumValue
      (PartialMatching.vertexDeletedGraph (scalarClockLegalGraph source target) S T) c =
      PartialMatching.legalMaximumValue
        (PartialMatching.vertexDeletedGraph (scalarClockLegalGraph source' target') S T) c' := by
    rw [hgraph]
    apply PartialMatching.legalMaximumValue_congr_on_allowed
    intro i j hij
    have h := (Finset.mem_filter.mp hij).2
    exact hcostEq i j h.1 h.2
  have h₀ := coarse.abs_legalMaximumValue_vertexDeletedGraph_sub_le hgap source target
    hsource hsep S T c hB hc
  have h₁ := coarse.abs_legalMaximumValue_vertexDeletedGraph_sub_le hgap source' target'
    hsource' hsep' S T c' hB hc'
  rw [← hsmall] at h₁
  have htriangle := abs_sub_le
    (PartialMatching.legalMaximumValue (scalarClockLegalGraph source target) c)
    (PartialMatching.legalMaximumValue
      (PartialMatching.vertexDeletedGraph (scalarClockLegalGraph source target) S T) c)
    (PartialMatching.legalMaximumValue (scalarClockLegalGraph source' target') c')
  rw [abs_sub_comm] at h₀
  nlinarith only [h₀,h₁,htriangle]

end OTSelector.Reconstruction
