import OTSelector.Reconstruction.FinslerRelativeLawCellwiseBinPopulation

/-!
Original reference-bin feasibility and measurable legal population reconstruction.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction

/-- Finite subpartitions of disjoint original coefficient cores form one
finite disjoint original label partition, with no extra discarded root mass. -/
theorem sigma_cell_partition
    {C Z : Type*} [Fintype C] (K : C → Set Z)
    (hKdisj : Pairwise (Disjoint on K)) (N : C → ℕ)
    (cell : ∀ c, Fin (N c) → Set Z)
    (hdisj : ∀ c, Pairwise (Disjoint on cell c))
    (hunion : ∀ c, (⋃ j, cell c j) = K c) :
    Pairwise (Disjoint on fun p : Sigma (fun c ↦ Fin (N c)) ↦ cell p.1 p.2) ∧
      (⋃ p : Sigma (fun c ↦ Fin (N c)), cell p.1 p.2) = ⋃ c, K c := by
  constructor
  · intro p q hpq
    change Disjoint (cell p.1 p.2) (cell q.1 q.2)
    by_cases h : p.1 = q.1
    · rcases p with ⟨c, j⟩
      rcases q with ⟨c', k⟩
      dsimp only at h
      subst c'
      exact hdisj c (fun hjk ↦ hpq (congrArg (Sigma.mk c) hjk))
    · apply (hKdisj h).mono
      · intro z hz
        rw [← hunion p.1]
        exact mem_iUnion.mpr ⟨p.2, hz⟩
      · intro z hz
        rw [← hunion q.1]
        exact mem_iUnion.mpr ⟨q.2, hz⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨p, hp⟩ := mem_iUnion.mp hz
      apply mem_iUnion.mpr
      refine ⟨p.1, ?_⟩
      rw [← hunion p.1]
      exact mem_iUnion.mpr ⟨p.2, hp⟩
    · intro hz
      obtain ⟨c, hc⟩ := mem_iUnion.mp hz
      rw [← hunion c] at hc
      obtain ⟨j, hj⟩ := mem_iUnion.mp hc
      exact mem_iUnion.mpr ⟨⟨c, j⟩, hj⟩

end OTSelector.Reconstruction
