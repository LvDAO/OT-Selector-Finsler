import OTSelector.Reconstruction.OriginalIIDMacroFrameCover

/-!
# Finitely many original rational frames over a compact macro core

Every original coordinate lies strictly inside one of the already prescribed
rational translated unit cubes. Compactness therefore gives a finite initial
segment of the same enumeration covering any compact core. The unchanged
first-frame owner rule vanishes beyond this segment, and its Fin-indexed
owners cover the core exactly, including all original frame boundaries.
-/

open Set Function Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Every original macro coordinate belongs to the interior of some frame
of the existing rational enumeration, also in transverse dimension zero. -/
theorem exists_mem_interior_originalMacroFrameCube
    (q : ℕ) (c : Fin q → ℝ) :
    ∃ j : ℕ, c ∈ interior (originalMacroFrameCube q j) := by
  have hr (i : Fin q) : ∃ r : ℚ,
      c i - (1 / 2 : ℝ) < r ∧ (r : ℝ) < c i + 1 / 2 :=
    exists_rat_btwn (by linarith)
  choose r hr using hr
  obtain ⟨j, hj⟩ := Classical.choose_spec (exists_surjective_nat (Fin q → ℚ)) r
  have hcenter (i : Fin q) : originalMacroFrameCenter q j i = (r i : ℝ) := by
    change ((originalMacroRationalCenters q j) i : ℝ) = (r i : ℝ)
    rw [originalMacroRationalCenters, hj]
  let W : Set (Fin q → ℝ) := ⋂ i : Fin q,
    (fun x : Fin q → ℝ => x i - originalMacroFrameCenter q j i) ⁻¹'
      Ioo (-(1 / 2 : ℝ)) (1 / 2)
  have hW : IsOpen W := isOpen_iInter_of_finite fun i =>
    isOpen_Ioo.preimage ((continuous_apply i).sub continuous_const)
  have hcW : c ∈ W := by
    apply mem_iInter.mpr
    intro i
    change -(1 / 2 : ℝ) < c i - originalMacroFrameCenter q j i ∧
      c i - originalMacroFrameCenter q j i < 1 / 2
    rw [hcenter i]
    constructor <;> linarith [(hr i).1, (hr i).2]
  have hsub : W ⊆ originalMacroFrameCube q j := by
    intro x hx
    change x - originalMacroFrameCenter q j ∈
      Icc (fun _ => -(1 / 2 : ℝ)) (fun _ => 1 / 2)
    constructor
    · intro i
      exact (mem_iInter.mp hx i).1.le
    · intro i
      exact (mem_iInter.mp hx i).2.le
  exact ⟨j, interior_maximal hsub hW hcW⟩

/-- The interiors of the original rational frames cover the whole coordinate
space; no frame is replaced or enlarged. -/
theorem iUnion_interior_originalMacroFrameCube (q : ℕ) :
    (⋃ j : ℕ, interior (originalMacroFrameCube q j)) = univ := by
  apply eq_univ_of_forall
  intro c
  obtain ⟨j, hj⟩ := exists_mem_interior_originalMacroFrameCube q c
  exact mem_iUnion.mpr ⟨j, hj⟩

/-- A compact original root core is covered by a finite initial segment of
the same enumerated frame interiors. Its bound is positive even for an empty
core or a zero-dimensional coordinate space. -/
theorem exists_originalMacroFrameCube_initial_cover_of_isCompact
    {q : ℕ} {K : Set (Fin q → ℝ)} (hK : IsCompact K) :
    ∃ J : ℕ, 0 < J ∧ K ⊆ ⋃ j < J, interior (originalMacroFrameCube q j) := by
  classical
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun j : ℕ => interior (originalMacroFrameCube q j))
    (fun _ => isOpen_interior)
    (by rw [iUnion_interior_originalMacroFrameCube]; exact subset_univ K)
  refine ⟨s.sup id + 1, Nat.succ_pos _, ?_⟩
  intro c hc
  obtain ⟨j, hj, hcj⟩ := mem_iUnion₂.mp (hs hc)
  exact mem_iUnion₂.mpr ⟨j,
    Nat.lt_succ_of_le (by simpa only [id_eq] using Finset.le_sup (f := id) hj), hcj⟩

/-- If an initial segment covers K, the original first-frame owner is empty
at every later index. The earlier-frame exclusion is unchanged. -/
theorem originalMacroFrameOwner_eq_empty_of_initial_cover
    {q : ℕ} {K : Set (Fin q → ℝ)} {J : ℕ}
    (hcover : K ⊆ ⋃ j < J, originalMacroFrameCube q j)
    {j : ℕ} (hj : J ≤ j) : originalMacroFrameOwner q K j = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro c hc
  have hcK := (originalMacroFrameOwner_subset q K j hc).1
  obtain ⟨k, hk, hck⟩ := mem_iUnion₂.mp (hcover hcK)
  rw [originalMacroFrameOwner_eq] at hc
  exact hc.2 (mem_iUnion₂.mpr ⟨k, hk.trans_le hj, hck⟩)

/-- The original owners below an initial covering bound form an exact Fin J
cover of K. This is the existing owner partition with its empty tail removed. -/
theorem iUnion_fin_originalMacroFrameOwner_eq_of_initial_cover
    {q : ℕ} {K : Set (Fin q → ℝ)} {J : ℕ}
    (hcover : K ⊆ ⋃ j < J, originalMacroFrameCube q j) :
    (⋃ j : Fin J, originalMacroFrameOwner q K j.val) = K := by
  apply Subset.antisymm
  · intro c hc
    obtain ⟨j, hj⟩ := mem_iUnion.mp hc
    exact (originalMacroFrameOwner_subset q K j.val hj).1
  · intro c hc
    have howner : c ∈ ⋃ j : ℕ, originalMacroFrameOwner q K j := by
      rw [iUnion_originalMacroFrameOwner]
      exact hc
    obtain ⟨j, hj⟩ := mem_iUnion.mp howner
    have hjJ : j < J := by
      by_contra hn
      rw [originalMacroFrameOwner_eq_empty_of_initial_cover hcover (Nat.le_of_not_gt hn)] at hj
      exact hj
    exact mem_iUnion.mpr ⟨⟨j, hjJ⟩, hj⟩

/-- One positive finite bound supplies the original frame cover, the empty
owner tail, and the exact finite owner cover needed for a single finite sum. -/
theorem exists_originalMacroFrameOwner_finite_cover_of_isCompact
    {q : ℕ} {K : Set (Fin q → ℝ)} (hK : IsCompact K) :
    ∃ J : ℕ, 0 < J ∧
      K ⊆ (⋃ j < J, originalMacroFrameCube q j) ∧
      (∀ j, J ≤ j → originalMacroFrameOwner q K j = ∅) ∧
      (⋃ j : Fin J, originalMacroFrameOwner q K j.val) = K := by
  obtain ⟨J, hJ, hcover⟩ := exists_originalMacroFrameCube_initial_cover_of_isCompact hK
  have hclosedCover : K ⊆ ⋃ j < J, originalMacroFrameCube q j := by
    intro c hc
    obtain ⟨j, hj, hcj⟩ := mem_iUnion₂.mp (hcover hc)
    exact mem_iUnion₂.mpr ⟨j, hj, interior_subset hcj⟩
  exact ⟨J, hJ, hclosedCover,
    fun _ hj => originalMacroFrameOwner_eq_empty_of_initial_cover hclosedCover hj,
    iUnion_fin_originalMacroFrameOwner_eq_of_initial_cover hclosedCover⟩

end OTSelector.Reconstruction
