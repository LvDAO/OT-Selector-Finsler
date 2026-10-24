import OTSelector.Finite.MatchingBlockDeletedCounts
import OTSelector.Finite.PartialMatching
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalLegalScreeningComparatorGlobalDeletedCounts.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalLegalScreeningComparatorGlobalDeletedCounts`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalLegalScreeningComparatorGlobalDeletedCounts

**Conditions:** One original pair of free deletion sets has the displayed correct counts in every finite block.

**Objects:** Global original unused sets whose every block has the exact local completion cardinality.

**Proof detail:** Intersect the same global deletion sets with each block fiber, apply the local deleted-count identity and identify each local set with the corresponding filter of the global unused set.

**Sources:** [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [OTSelector project, Original strict-screen residual slack and repair](main.tex#strict-screen-residual-slack), main.tex label strict-screen-residual-slack, line 6749.

Source relation (adapter): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! One original deletion set induces every exact local completion count. -/
open Set Function
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PartialMatching
variable {m n : ℕ} {B : Type*} [DecidableEq B]

/-- Actual signed excesses are deleted on one unchanged original index set.
Its block restrictions therefore give both the exact local minimum completion
count and equally many unused source/target labels, without a global rank premise. -/
theorem originalGlobalDeletedUnused_count_spec
    (σ : OTSelector.PartialMatching m n) (c : Fin m → B) (d : Fin n → B)
    (hsame : ∀ e ∈ σ.edges, c e.1 = d e.2)
    (Ds : Finset (Fin m)) (Dt : Finset (Fin n))
    (hDs : Ds ⊆ σ.freeRows) (hDt : Dt ⊆ σ.freeCols)
    (hDscard : ∀ b, (Ds.filter (fun i ↦ c i = b)).card =
      (Finset.univ.filter (fun i ↦ c i = b)).card - (Finset.univ.filter (fun j ↦ d j = b)).card)
    (hDtcard : ∀ b, (Dt.filter (fun j ↦ d j = b)).card =
      (Finset.univ.filter (fun j ↦ d j = b)).card - (Finset.univ.filter (fun i ↦ c i = b)).card) :
    let U := σ.freeRows \ Ds
    let V := σ.freeCols \ Dt
    U ⊆ σ.freeRows ∧ V ⊆ σ.freeCols ∧
      ∀ b,
        (σ.edges.filter (fun e ↦ c e.1 = b)).card + (U.filter (fun i ↦ c i = b)).card =
          min (Finset.univ.filter (fun i ↦ c i = b)).card (Finset.univ.filter (fun j ↦ d j = b)).card ∧
        (U.filter (fun i ↦ c i = b)).card = (V.filter (fun j ↦ d j = b)).card := by
  refine ⟨Finset.sdiff_subset,Finset.sdiff_subset,?_⟩
  intro b
  have hs : Ds.filter (fun i ↦ c i = b) ⊆ σ.freeRows.filter (fun i ↦ c i = b) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨hDs (Finset.mem_filter.mp hi).1,(Finset.mem_filter.mp hi).2⟩
  have ht : Dt.filter (fun j ↦ d j = b) ⊆ σ.freeCols.filter (fun j ↦ d j = b) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨hDt (Finset.mem_filter.mp hj).1,(Finset.mem_filter.mp hj).2⟩
  have h := originalBlockDeletedUnused_count_spec σ c d hsame b
    (Ds.filter (fun i ↦ c i = b)) (Dt.filter (fun j ↦ d j = b)) hs ht (hDscard b) (hDtcard b)
  have heS : (σ.freeRows.filter (fun i ↦ c i = b)) \ (Ds.filter (fun i ↦ c i = b)) =
      (σ.freeRows \ Ds).filter (fun i ↦ c i = b) := by
    ext i
    simp only [Finset.mem_sdiff,Finset.mem_filter]
    tauto
  have heT : (σ.freeCols.filter (fun j ↦ d j = b)) \ (Dt.filter (fun j ↦ d j = b)) =
      (σ.freeCols \ Dt).filter (fun j ↦ d j = b) := by
    ext j
    simp only [Finset.mem_sdiff,Finset.mem_filter]
    tauto
  exact ⟨by simpa only [heS] using h.2.2.2.2.1,by simpa only [heS,heT] using h.2.2.2.2.2⟩

end OTSelector.Reconstruction.PartialMatching

end
end
