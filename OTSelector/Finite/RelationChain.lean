import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-!
## Lemma skeleton

* **Conditions:** A reflexive-transitive directed relation chain; finite vertex type only for the cardinal bound.
* **Objects:** An injective vertex sequence with the original endpoints.
* **Proof detail:** Erase a loop whenever an endpoint repeats, then use injectivity to bound length.

## Mathematical sources

* Reinhard Diestel, *Graph Theory, 6th edition (2025)*, Sections 1.3 (paths and cycles) and 1.10 (other notions of graphs).
  https://diestel-graph-theory.com/Contents.pdf

**Relationship to the sources:** The directed arbitrary-relation formulation and exact Fin encoding are local elementary lemmas; no same-numbered theorem is attributed to Diestel.
-/

/-! A directed finite relation admits an injective vertex chain between any
two reflexive-transitively related vertices. The construction erases loops at
the moment their terminal vertex repeats. -/

open Function Set
noncomputable section
namespace OTSelector
set_option backward.isDefEq.respectTransparency false

theorem exists_injective_relation_chain {J : Type*} {R : J → J → Prop} {a b : J}
    (h : Relation.ReflTransGen R a b) :
    ∃ k : ℕ, ∃ x : Fin (k + 1) → J, Injective x ∧ x 0 = a ∧ x (Fin.last k) = b ∧
      ∀ i : Fin k, R (x i.castSucc) (x i.succ) := by
  classical
  induction h with
  | refl =>
      refine ⟨0, fun _ ↦ a, ?_, rfl, rfl, fun i ↦ Fin.elim0 i⟩
      intro i j _
      apply Fin.ext
      have := i.isLt
      have := j.isLt
      omega
  | @tail b c hab hbc ih =>
      obtain ⟨k, x, hx, hfirst, hlast, hstep⟩ := ih
      by_cases hc : c ∈ range x
      · obtain ⟨i, hi⟩ := hc
        let e : Fin (i.val + 1) → Fin (k + 1) :=
          fun j ↦ ⟨j.val, by have := i.isLt; have := j.isLt; omega⟩
        have he0 : e 0 = 0 := Fin.ext rfl
        have helast : e (Fin.last i.val) = i := Fin.ext rfl
        have heinj : Injective e := by
          intro u v huv
          exact Fin.ext (congrArg (fun j : Fin (k + 1) ↦ j.val) huv)
        refine ⟨i.val, x ∘ e, hx.comp heinj,
          ?_, ?_, ?_⟩
        · simpa only [comp_apply, he0] using hfirst
        · simpa only [comp_apply, helast] using hi
        · intro j
          let j' : Fin k := ⟨j.val, by have := j.isLt; have := i.isLt; omega⟩
          have heleft : e j.castSucc = j'.castSucc := Fin.ext rfl
          have heright : e j.succ = j'.succ := Fin.ext rfl
          simpa only [comp_apply, heleft, heright] using hstep j'
      · refine ⟨k + 1, Fin.snoc x c, Fin.snoc_injective_iff.mpr ⟨hx, hc⟩, ?_,
          by simp only [Fin.snoc_last], ?_⟩
        · simpa only [Fin.snoc_apply_zero] using hfirst
        · intro i
          refine Fin.lastCases ?_ (fun j ↦ ?_) i
          · simpa only [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, hlast] using hbc
          · simpa only [← Fin.castSucc_succ, Fin.snoc_castSucc] using hstep j

/-- Finite source classes bound the number of vertices in the reduced chain. -/
theorem exists_bounded_injective_relation_chain {J : Type*} [Fintype J]
    {R : J → J → Prop} {a b : J} (h : Relation.ReflTransGen R a b) :
    ∃ k : ℕ, k + 1 ≤ Fintype.card J ∧ ∃ x : Fin (k + 1) → J,
      Injective x ∧ x 0 = a ∧ x (Fin.last k) = b ∧
      ∀ i : Fin k, R (x i.castSucc) (x i.succ) := by
  obtain ⟨k, x, hx, hrest⟩ := exists_injective_relation_chain h
  exact ⟨k, by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective x hx,
    x, hx, hrest⟩

end OTSelector
