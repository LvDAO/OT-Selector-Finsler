import OTSelector.Reconstruction.FinslerPhysicalSceneRootedNonproperExhaustion

/-!
# Genuine compact exhaustions containing actual escape cutoffs
-/

open Set Function Filter MeasureTheory TopologicalSpace
open scoped Topology
noncomputable section
namespace OTSelector.Reconstruction

/-- Any sequence of actual compact tail cutoffs can be contained in a genuine
compact exhaustion. It is a cofinal subsequence of the original exhaustion. -/
theorem exists_physicalScene_compact_exhaustion_domination
    {X : Type*} [TopologicalSpace X] (K : CompactExhaustion X)
    (L : ℕ → Set X) (hL : ∀ n, IsCompact (L n)) :
    ∃ K' : CompactExhaustion X, ∀ n, L n ⊆ K' n := by
  classical
  choose b hb using fun n ↦ K.exists_superset_of_isCompact (hL n)
  let index : ℕ → ℕ := Nat.rec (b 0) (fun n previous ↦ max (b (n + 1)) (previous + 1))
  have hs : StrictMono index := by
    apply strictMono_nat_of_lt_succ
    intro n
    change index n < max (b (n + 1)) (index n + 1)
    exact (Nat.lt_succ_self _).trans_le (le_max_right _ _)
  have hindex (n : ℕ) : b n ≤ index n := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact le_max_left _ _
  let K' : CompactExhaustion X := {
    toFun := fun n ↦ K (index n)
    isCompact' := fun n ↦ K.isCompact (index n)
    subset_interior_succ' := fun n ↦ K.subset_interior (hs (Nat.lt_succ_self n))
    iUnion_eq' := iUnion_eq_univ_iff.mpr fun x ↦ by
      obtain ⟨n, hn⟩ := K.exists_mem x
      exact ⟨n, K.subset (hs.id_le n) hn⟩ }
  exact ⟨K', fun n ↦ (hb n).trans (K.subset (hindex n))⟩

end OTSelector.Reconstruction
