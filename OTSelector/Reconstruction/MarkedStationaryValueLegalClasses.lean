import OTSelector.Reconstruction.MarkedStationaryValueLegalReachability
import OTSelector.Finite.RelationChain

/-!
# Short actual augmenting chains for finite source classes

The admissible target set is the same for every source in a given finite
class. Reachability is projected onto those classes and loops are erased
there. Actual old matching edges lift the resulting class chain back to
the original indices. The new chain has at most one new edge per class.
-/

open Set Function
noncomputable section
namespace OTSelector.Reconstruction.PartialMatching
set_option backward.isDefEq.respectTransparency false

variable {m n : ℕ} {J : Type*} [Fintype J]

def sourceClassStep (σ : OTSelector.PartialMatching m n) (sourceClass : Fin m → J)
    (sourceAllows : J → Fin n → Prop) (a b : J) : Prop :=
  ∃ i j, sourceClass i = b ∧ sourceAllows a j ∧ (i, j) ∈ σ.edges

/-- An actual nonmaximum legal graph admits a simple augmenting chain with
at most `card J` new edges whenever source classes have complete rectangles. -/
theorem exists_bounded_classAugmentingChain
    {allowed : Finset (Fin m × Fin n)} (σ : OTSelector.PartialMatching m n)
    (sourceClass : Fin m → J) (sourceAllows : J → Fin n → Prop)
    (hallowed : ∀ i j, (i, j) ∈ allowed ↔ sourceAllows (sourceClass i) j)
    (hcard : σ.card < legalMaximumCard allowed) :
    ∃ k : ℕ, k + 1 ≤ Fintype.card J ∧ Nonempty (LegalAugmentingChain allowed σ k) := by
  classical
  obtain ⟨i, ⟨i₀, hi₀, hpath⟩, j, hj, hij⟩ :=
    exists_reachable_free_target_of_card_lt σ hcard
  have hclasspath : Relation.ReflTransGen (sourceClassStep σ sourceClass sourceAllows)
      (sourceClass i₀) (sourceClass i) := by
    apply Relation.ReflTransGen.lift sourceClass ?_ _ _ hpath
    intro a b hab
    obtain ⟨c, hac, hbc⟩ := hab
    exact ⟨b, c, rfl, (hallowed a c).mp hac, hbc⟩
  obtain ⟨k, hk, x, hx, hfirst, hlast, hsteps⟩ :=
    OTSelector.exists_bounded_injective_relation_chain hclasspath
  dsimp only [sourceClassStep] at hsteps
  choose nextRow oldCol htype hallow hold using hsteps
  let rows : Fin (k + 1) → Fin m := Fin.cons i₀ nextRow
  let cols : Fin (k + 1) → Fin n := Fin.snoc oldCol j
  have hrowtype (a : Fin (k + 1)) : sourceClass (rows a) = x a := by
    refine Fin.cases ?_ (fun b ↦ ?_) a
    · simpa only [rows, Fin.cons_zero] using hfirst.symm
    · simpa only [rows, Fin.cons_succ] using htype b
  have hrows : Injective rows := by
    intro a b hab
    apply hx
    rw [← hrowtype a, ← hrowtype b, hab]
  have hcolsOld : Injective oldCol := by
    intro a b hab
    have heq := σ.col_inj _ (hold a) _ (hold b) hab
    have hroweq := congrArg Prod.fst heq
    apply Fin.succ_injective _
    apply hx
    exact (htype a).symm.trans ((congrArg sourceClass hroweq).trans (htype b))
  have hjnot : j ∉ range oldCol := by
    rintro ⟨a, ha⟩
    apply (Finset.mem_sdiff.mp hj).2
    exact ha ▸ Finset.mem_image.mpr ⟨(nextRow a, oldCol a), hold a, rfl⟩
  refine ⟨k, hk, ⟨⟨rows, cols, hrows, Fin.snoc_injective_iff.mpr ⟨hcolsOld, hjnot⟩,
    ?_, ?_, ?_, ?_⟩⟩⟩
  · simpa only [rows, Fin.cons_zero] using (Finset.mem_sdiff.mp hi₀).2
  · simpa only [cols, Fin.snoc_last] using (Finset.mem_sdiff.mp hj).2
  · intro a
    simpa only [rows, cols, Fin.cons_succ, Fin.snoc_castSucc] using hold a
  · intro a
    refine Fin.lastCases ?_ (fun b ↦ ?_) a
    · apply (hallowed _ _).mpr
      rw [hrowtype, hlast]
      simpa only [cols, Fin.snoc_last] using (hallowed i j).mp hij
    · apply (hallowed _ _).mpr
      rw [hrowtype]
      simpa only [cols, Fin.snoc_castSucc] using hallow b

end OTSelector.Reconstruction.PartialMatching
