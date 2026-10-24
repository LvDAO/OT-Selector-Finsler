import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockClassSelection

/-! One global original kept set has exactly the independently repaired block classes. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ} {B : Type*} [Fintype B]

/-- All blocks are repaired on the same original sampler indices. Their union
is the global kept set; no new positions or labels are sampled. -/
def originalReserveBlocksKept (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T C : B → Set ℝ) (z : OriginalReserveSceneAux q) : Finset ℕ :=
  Finset.univ.biUnion (fun b ↦ originalReserveBlockKept K own other (S b) (T b) (C b) z)

theorem measurable_originalReserveBlocksKept {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    (own other : Fin 2) {S T C : B → Set ℝ}
    (hS : ∀ b, MeasurableSet (S b)) (hT : ∀ b, MeasurableSet (T b))
    (hC : ∀ b, MeasurableSet (C b)) :
    Measurable (originalReserveBlocksKept K own other S T C) := by
  exact (measurable_of_countable (fun U : B → Finset ℕ ↦ Finset.univ.biUnion U)).comp
    (measurable_pi_lambda _ (fun b ↦ measurable_originalReserveBlockKept hK own other (hS b) (hT b) (hC b)))

/-- Every retained index is inside the observed original finite prefix. -/
theorem originalReserveBlocksKept_subset_range (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T C : B → Set ℝ) (z : OriginalReserveSceneAux q) :
    originalReserveBlocksKept K own other S T C z ⊆ Finset.range z.2.1 := by
  intro i hi
  obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp hi
  exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hb).1).1

/-- Disjoint true clock blocks make global restriction exactly the repaired
original block set. There is no assumption about a spatial sampling law. -/
theorem originalReserveBlocksKept_filter_block (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T C : B → Set ℝ) (hdis : Pairwise (Disjoint on S))
    (z : OriginalReserveSceneAux q) (b : B) :
    (originalReserveBlocksKept K own other S T C z).filter (fun i ↦ z.2.2 i ∈ S b) =
      originalReserveBlockKept K own other (S b) (T b) (C b) z := by
  ext i
  constructor
  · intro hi
    obtain ⟨hU,hSb⟩ := Finset.mem_filter.mp hi
    obtain ⟨c,_,hc⟩ := Finset.mem_biUnion.mp hU
    have hSc := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hc).1).2
    have hcb : c = b := by
      by_contra hn
      exact disjoint_left.mp (hdis hn) hSc hSb
    simpa only [hcb] using hc
  · intro hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,hi⟩,
        (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).2⟩

/-- Every fine class inside its own true block agrees with the classwise
selector used to construct that stage's real population coupling. -/
theorem originalReserveBlocksKept_filter_class (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T C : B → Set ℝ) (hdis : Pairwise (Disjoint on S))
    (z : OriginalReserveSceneAux q) (b : B) {D : Set ℝ} (hD : D ⊆ S b) :
    (originalReserveBlocksKept K own other S T C z).filter (fun i ↦ z.2.2 i ∈ D) =
      originalReserveBlockClassKept K own other (S b) (T b) (C b) D z := by
  have hblock := originalReserveBlocksKept_filter_block K own other S T C hdis z b
  ext i
  simp only [originalReserveBlockClassKept, Finset.mem_filter]
  constructor
  · rintro ⟨hi,hmark⟩
    exact ⟨by rw [← hblock]; exact Finset.mem_filter.mpr ⟨hi,hD hmark⟩,hmark⟩
  · rintro ⟨hi,hmark⟩
    have hmem : i ∈ (originalReserveBlocksKept K own other S T C z).filter
        (fun i ↦ z.2.2 i ∈ S b) := by rw [hblock]; exact hi
    exact ⟨(Finset.mem_filter.mp hmem).1,hmark⟩

/-- The same global indices in the literal original Fin observation. -/
def originalReserveBlocksKeptFin (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T C : B → Set ℝ) (z : OriginalReserveSceneAux q) : Finset (Fin z.2.1) :=
  Finset.univ.filter (fun i ↦ i.val ∈ originalReserveBlocksKept K own other S T C z)

theorem originalReserveBlocksKept_eq_map_fin (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T C : B → Set ℝ) (z : OriginalReserveSceneAux q) :
    originalReserveBlocksKept K own other S T C z =
      (originalReserveBlocksKeptFin K own other S T C z).map Fin.valEmbedding := by
  ext i
  simp only [originalReserveBlocksKeptFin, Finset.mem_map, Finset.mem_filter,
    Finset.mem_univ, true_and, Fin.valEmbedding_apply]
  constructor
  · intro hi
    exact ⟨⟨i,Finset.mem_range.mp (originalReserveBlocksKept_subset_range K own other S T C z hi)⟩,hi,rfl⟩
  · rintro ⟨j,hj,rfl⟩
    exact hj

/-- The global actual stage count h_D equals the local block-class kept
count used by the iid/RN producer, with identical original Fin identities. -/
theorem originalReserveBlocksKeptFin_class_count (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T C : B → Set ℝ) (hdis : Pairwise (Disjoint on S))
    (z : OriginalReserveSceneAux q) (positions : ℕ → Fin q → ℝ)
    (b : B) {D : Set ℝ} (hD : D ⊆ S b) :
    originalStageRemainingReserveClassCount ⟨z.2.1,fun i ↦ (positions i,z.2.2 i)⟩
      (originalReserveBlocksKeptFin K own other S T C z) D =
      (originalReserveBlockClassKept K own other (S b) (T b) (C b) D z).card := by
  rw [← originalReserveBlocksKept_filter_class K own other S T C hdis z b hD,
    originalReserveBlocksKept_eq_map_fin, Finset.filter_map, Finset.card_map]
  rfl

end OTSelector.Reconstruction
