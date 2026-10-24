import OTSelector.Reconstruction.MarkedStationaryValueLegalAugment
import Mathlib.Logic.Relation

/-!
# Original-index reachability for legal augmentation

If no alternatingly reachable source can use a free target, every competing
legal matching injects into the old matching. Thus any legal matching below
the true graph maximum has a reachable free target. The argument works on
the actual finite graph, with no assumed residual capacity.
-/

open Set Function
noncomputable section
namespace OTSelector.Reconstruction.PartialMatching
set_option backward.isDefEq.respectTransparency false

variable {m n : ℕ}

/-- One forward legal edge followed by one actual reversed old matching edge. -/
def alternatingRowStep (allowed : Finset (Fin m × Fin n))
    (σ : OTSelector.PartialMatching m n) (i i' : Fin m) : Prop :=
  ∃ j : Fin n, (i, j) ∈ allowed ∧ (i', j) ∈ σ.edges

/-- Sources reached from some genuinely free original source. -/
def alternatingReachable (allowed : Finset (Fin m × Fin n))
    (σ : OTSelector.PartialMatching m n) (i : Fin m) : Prop :=
  ∃ i₀ ∈ σ.freeRows, Relation.ReflTransGen (alternatingRowStep allowed σ) i₀ i

theorem alternatingReachable_of_free {allowed : Finset (Fin m × Fin n)}
    {σ : OTSelector.PartialMatching m n} {i : Fin m} (hi : i ∈ σ.freeRows) :
    alternatingReachable allowed σ i := ⟨i, hi, .refl⟩

theorem alternatingReachable_step {allowed : Finset (Fin m × Fin n)}
    {σ : OTSelector.PartialMatching m n} {i i' : Fin m}
    (hi : alternatingReachable allowed σ i) (hstep : alternatingRowStep allowed σ i i') :
    alternatingReachable allowed σ i' := by
  obtain ⟨i₀, hfree, hpath⟩ := hi
  exact ⟨i₀, hfree, hpath.tail hstep⟩

/-- Without a reachable free target the original matching has maximum legal
cardinality. The proof explicitly injects every legal competitor into it. -/
theorem card_le_of_no_reachable_free_target
    {allowed : Finset (Fin m × Fin n)} (σ τ : OTSelector.PartialMatching m n)
    (hτ : IsLegal allowed τ)
    (hno : ∀ i, alternatingReachable allowed σ i →
      ∀ j ∈ σ.freeCols, (i, j) ∉ allowed) : τ.card ≤ σ.card := by
  classical
  have hchoose (e : Fin m × Fin n) (he : e ∈ τ.edges) :
      ∃ f ∈ σ.edges,
        (alternatingReachable allowed σ e.1 →
          alternatingReachable allowed σ f.1 ∧ f.2 = e.2) ∧
        (¬alternatingReachable allowed σ e.1 →
          ¬alternatingReachable allowed σ f.1 ∧ f.1 = e.1) := by
    by_cases hr : alternatingReachable allowed σ e.1
    · have hc : e.2 ∈ σ.cols := by
        by_contra h
        exact hno e.1 hr e.2
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩) (hτ he)
      obtain ⟨f, hf, hcol⟩ := Finset.mem_image.mp hc
      have hstep : alternatingRowStep allowed σ e.1 f.1 := by
        refine ⟨e.2, hτ he, ?_⟩
        simpa only [← hcol] using hf
      exact ⟨f, hf, fun _ ↦ ⟨alternatingReachable_step hr hstep, hcol⟩,
        fun h ↦ (h hr).elim⟩
    · have hs : e.1 ∈ σ.rows := by
        by_contra h
        exact hr (alternatingReachable_of_free
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩))
      obtain ⟨f, hf, hrow⟩ := Finset.mem_image.mp hs
      exact ⟨f, hf, fun h ↦ (hr h).elim, fun _ ↦ ⟨hrow.symm ▸ hr, hrow⟩⟩
  let f : τ.edges → σ.edges := fun e ↦
    ⟨(hchoose e.val e.property).choose, (hchoose e.val e.property).choose_spec.1⟩
  have hf (e : τ.edges) :
      (alternatingReachable allowed σ e.val.1 →
        alternatingReachable allowed σ (f e).val.1 ∧ (f e).val.2 = e.val.2) ∧
      (¬alternatingReachable allowed σ e.val.1 →
        ¬alternatingReachable allowed σ (f e).val.1 ∧ (f e).val.1 = e.val.1) :=
    (hchoose e.val e.property).choose_spec.2
  have hinj : Injective f := by
    intro e e' heq
    have heqv := congrArg Subtype.val heq
    by_cases hr : alternatingReachable allowed σ e.val.1 <;>
      by_cases hr' : alternatingReachable allowed σ e'.val.1
    · apply Subtype.ext
      apply τ.col_inj _ e.property _ e'.property
      exact (hf e).1 hr |>.2.symm |>.trans
        ((congrArg Prod.snd heqv).trans ((hf e').1 hr').2)
    · have h1 := ((hf e).1 hr).1
      have h2 := ((hf e').2 hr').1
      exact (h2 (congrArg Prod.fst heqv ▸ h1)).elim
    · have h1 := ((hf e).2 hr).1
      have h2 := ((hf e').1 hr').1
      exact (h1 ((congrArg Prod.fst heqv).symm ▸ h2)).elim
    · apply Subtype.ext
      apply τ.row_inj _ e.property _ e'.property
      exact (hf e).2 hr |>.2.symm |>.trans
        ((congrArg Prod.fst heqv).trans ((hf e').2 hr').2)
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe, OTSelector.PartialMatching.card] using hc

/-- A graph-deficient actual matching has an alternatingly reachable free
target; no separate Hall or residual-graph hypothesis is supplied. -/
theorem exists_reachable_free_target_of_card_lt
    {allowed : Finset (Fin m × Fin n)} (σ : OTSelector.PartialMatching m n)
    (hcard : σ.card < legalMaximumCard allowed) :
    ∃ i, alternatingReachable allowed σ i ∧ ∃ j ∈ σ.freeCols, (i, j) ∈ allowed := by
  by_contra h
  have hno : ∀ i, alternatingReachable allowed σ i →
      ∀ j ∈ σ.freeCols, (i, j) ∉ allowed := by
    intro i hi j hj he
    exact h ⟨i, hi, j, hj, he⟩
  obtain ⟨τ, hτlegal, hτcard⟩ := exists_legalMaximumCard allowed
  have hle := card_le_of_no_reachable_free_target σ τ hτlegal hno
  rw [hτcard] at hle
  omega

end OTSelector.Reconstruction.PartialMatching
