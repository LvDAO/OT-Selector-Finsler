import OTSelector.Reconstruction.FinslerTileBlockFrozenComparison
import OTSelector.Reconstruction.FinslerTileProbeCorrection
import OTSelector.Finite.MaxCardValueStability
import OTSelector.Probability.TileCountBlockBridge
import OTSelector.Reconstruction.FinslerCoefficientCoreSubplanSampling

/-!
# Cell-law stability for the concrete upper bound

This module supplies the deterministic and measure-theoretic stability layer
used to compare the frozen tile block under perturbed one-point laws.

## Contents

1. `maxCardValue_one_row_le`: two matrices of the same shape which differ in a
   single row differ in maximum-cardinality value by at most the row error.
2. `abs_maxCardValue_blockCost_one_row_le`: if two label arrays agree off one
   index and the two ambient matrices agree off the corresponding row, then the
   tile-`c` block values differ by at most twice the uniform edge bound.  The
   proof splits on whether the changed label stays in the tile or enters/leaves
   it, using `maxCardValue_reindex`, the row-addition stability
   `abs_maxCardValue_sub_le_add_rows`, and the elementary one-row estimate.
3. `abs_frozenModelTileBlock_one_source_le` and its target analogue: the
   single-point stability of `OTSelector.frozenModelTileBlock`.
4. `integral_frozenModelTileBlock_le_of_coupling`: the relative law-stability
   assembly from a coupling of the two sample laws, a good event on which the
   blocks agree, and the explicit relative stability on its complement.
5. `coupling_map_prod_mismatch` and
   `exists_physical_point_coupling_of_original_subplan_sampling`: pushing a
   coupling through the seed readout preserves its mismatch mass, so the
   subplan-sampling coupling of the normalized label-clock laws yields a
   coupling of the corresponding normalized physical point laws.

No `sorry`, `admit` or added axiom occurs.
-/

open MeasureTheory ProbabilityTheory Filter Set Function Matrix Manifold OTSelector.Geometry
open scoped BigOperators NNReal ENNReal Topology ContDiff Matrix.Norms.Operator

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace OTSelector

namespace PartialMatching

/-! ## Two matrices of the same shape differing in one row -/

/-- **One-row stability of the maximum-cardinality value.**  If two matrices of
the same shape agree outside the row `i₀` and their row-`i₀` entries differ by
at most `E`, then their maximum-cardinality values differ by at most `E`. -/
theorem maxCardValue_one_row_le {a b : ℕ} (c d : Fin a → Fin b → ℝ) (i₀ : Fin a)
    {E : ℝ} (hE0 : 0 ≤ E)
    (h : ∀ i, i ≠ i₀ → ∀ j, c i j = d i j)
    (hrow : ∀ j, |c i₀ j - d i₀ j| ≤ E) :
    |maxCardValue c - maxCardValue d| ≤ E := by
  classical
  have hsum_le : ∀ σ : PartialMatching a b,
      ∑ e ∈ σ.edges, (if e.1 = i₀ then E else 0) ≤ E := by
    intro σ
    have hcard : (σ.edges.filter (fun e => e.1 = i₀)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro e he e' he'
      exact σ.row_inj e (Finset.mem_filter.mp he).1 e' (Finset.mem_filter.mp he').1
        ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp he').2.symm)
    have hEq : ∑ e ∈ σ.edges, (if e.1 = i₀ then E else 0) =
        ((σ.edges.filter (fun e => e.1 = i₀)).card : ℝ) * E := by
      rw [← Finset.sum_filter]
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hEq]
    have hc : ((σ.edges.filter (fun e => e.1 = i₀)).card : ℝ) ≤ 1 := by
      exact_mod_cast hcard
    nlinarith
  rw [abs_sub_le_iff]
  constructor
  · obtain ⟨σ, hσcard, hσcost⟩ := exists_cost_eq_maxCardValue d
    have hle := Reconstruction.maxCardValue_le_of_le_const_mul_add_edge
      (c := c) (d := d) (B := fun i j => if i = i₀ then E else 0) (α := 1)
      (σ := σ) hσcard hσcost ?_
    · have hsum := hsum_le σ
      nlinarith
    · intro i j
      by_cases hij : i = i₀
      · subst hij
        have h1 := (abs_le.mp (hrow j)).2
        rw [ite_eq_left rfl]
        linarith
      · rw [h i hij j]
        simp [hij]
  · obtain ⟨σ, hσcard, hσcost⟩ := exists_cost_eq_maxCardValue c
    have hle := Reconstruction.maxCardValue_le_of_le_const_mul_add_edge
      (c := d) (d := c) (B := fun i j => if i = i₀ then E else 0) (α := 1)
      (σ := σ) hσcard hσcost ?_
    · have hsum := hsum_le σ
      nlinarith
    · intro i j
      by_cases hij : i = i₀
      · subst hij
        have h1 := (abs_le.mp (hrow j)).1
        rw [ite_eq_left rfl]
        linarith
      · rw [← h i hij j]
        simp [hij]

/-- Transposition of a partial matching. -/
def transpose {m n : ℕ} (σ : PartialMatching m n) : PartialMatching n m where
  edges := σ.edges.image (fun e : Fin m × Fin n => (e.2, e.1))
  row_inj := by
    intro e he e' he' hrow
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he'
    have h2 : a.2 = b.2 := by simpa using hrow
    have hab : a = b := σ.col_inj a ha b hb h2
    subst hab
    rfl
  col_inj := by
    intro e he e' he' hcol
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he'
    have h1 : a.1 = b.1 := by simpa using hcol
    have hab : a = b := σ.row_inj a ha b hb h1
    subst hab
    rfl

theorem card_transpose {m n : ℕ} (σ : PartialMatching m n) :
    σ.transpose.card = σ.card := by
  unfold transpose card
  rw [Finset.card_image_of_injOn]
  intro e _ e' _ h
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
  exact Prod.ext h2 h1

theorem cost_transpose {m n : ℕ} (c : Fin m → Fin n → ℝ) (σ : PartialMatching m n) :
    σ.transpose.cost (fun i j => c j i) = σ.cost c := by
  show (∑ e ∈ σ.edges.image (fun e : Fin m × Fin n => (e.2, e.1)),
      (fun e : Fin n × Fin m => c e.2 e.1) e) = ∑ e ∈ σ.edges, c e.1 e.2
  rw [Finset.sum_image]
  intro e _ e' _ h
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
  exact Prod.ext h2 h1

/-- The maximum-cardinality value is invariant under transposition. -/
theorem maxCardValue_transpose {m n : ℕ} (c : Fin m → Fin n → ℝ) :
    maxCardValue (fun i : Fin n => fun j : Fin m => c j i) = maxCardValue c := by
  classical
  unfold maxCardValue
  congr 1
  ext v
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨σ.transpose, ?_, ?_⟩
    · rw [card_transpose]
      simpa [Nat.min_comm] using hσ
    · rw [cost_transpose]
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨σ.transpose, ?_, ?_⟩
    · rw [card_transpose]
      simpa [Nat.min_comm] using hσ
    · rw [cost_transpose]

end PartialMatching

namespace BlockStability

open PartialMatching

/-! ## Reindexing a block with one extra row -/

/-- **Surjectivity of the block enumeration onto its finset.**  Every ambient
index in the tile `c` is hit by `blockEmbeddingS`. -/
theorem blockEmbeddingS_surjOn {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (blockS : Fin N → ι) (c : ι) {i : Fin N} (hi : i ∈ blockFinset blockS c) :
    ∃ r : Fin (blockSizeS blockS c), blockEmbeddingS blockS c r = i := by
  classical
  have hbij : Function.Bijective (fun r : Fin (blockSizeS blockS c) =>
      (⟨blockEmbeddingS blockS c r, blockEmbeddingS_mem blockS c r⟩ :
        blockFinset blockS c)) := by
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
    · intro r s h
      exact blockEmbeddingS_injective blockS c (Subtype.ext_iff.mp h)
    · rw [Fintype.card_subtype]
      simp [blockSizeS, blockFinset]
  obtain ⟨r, hr⟩ := hbij.2 ⟨i, hi⟩
  exact ⟨r, congrArg Subtype.val hr⟩

/-- **Moving the extra row of a block to the last position.**  If the tile of
`blockS` is the tile of `blockS'` together with the single extra index `i₀`,
there is an equivalence of the block index types which enumerates the rows of
`blockS'` first (in their `blockS'`-enumeration order) and `i₀` last. -/
theorem exists_blockEmbeddingS_insert_equiv {N : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (blockS blockS' : Fin N → ι) (c : ι) (i₀ : Fin N)
    (hS : blockFinset blockS c = insert i₀ (blockFinset blockS' c))
    (hnot : i₀ ∉ blockFinset blockS' c) :
    ∃ e : Fin (blockSizeS blockS' c + 1) ≃ Fin (blockSizeS blockS c),
      (∀ r : Fin (blockSizeS blockS' c),
        blockEmbeddingS blockS c (e (Fin.castSucc r)) = blockEmbeddingS blockS' c r) ∧
      blockEmbeddingS blockS c (e (Fin.last _)) = i₀ := by
  classical
  let a := blockSizeS blockS' c
  have hcard : blockSizeS blockS c = a + 1 := by
    simp only [a, blockSizeS, hS, Finset.card_insert_of_notMem hnot]
  let pos : Fin a → Fin (blockSizeS blockS c) := fun r =>
    Finset.equivFin (blockFinset blockS c)
      ⟨blockEmbeddingS blockS' c r, by
        rw [hS]
        exact Finset.mem_insert_of_mem (blockEmbeddingS_mem blockS' c r)⟩
  let lastPos : Fin (blockSizeS blockS c) :=
    Finset.equivFin (blockFinset blockS c)
      ⟨i₀, by rw [hS]; exact Finset.mem_insert_self _ _⟩
  let φ : Fin (a + 1) → Fin (blockSizeS blockS c) := Fin.lastCases lastPos pos
  have hφ_castSucc : ∀ r : Fin a, φ (Fin.castSucc r) = pos r := fun r =>
    Fin.lastCases_castSucc r
  have hφ_last : φ (Fin.last a) = lastPos := Fin.lastCases_last
  have hpos_key : ∀ r : Fin a, blockEmbeddingS blockS c (pos r) =
      blockEmbeddingS blockS' c r := by
    intro r
    simp only [pos, blockEmbeddingS, Equiv.symm_apply_apply]
  have hlast_key : blockEmbeddingS blockS c lastPos = i₀ := by
    simp only [lastPos, blockEmbeddingS, Equiv.symm_apply_apply]
  have hφ_key : ∀ r : Fin (a + 1), blockEmbeddingS blockS c (φ r) =
      Fin.lastCases i₀ (fun r' : Fin a => blockEmbeddingS blockS' c r') r := by
    intro r
    rcases Fin.eq_castSucc_or_eq_last r with ⟨r', rfl⟩ | hr
    · rw [hφ_castSucc, hpos_key]
      simp
    · rw [hr, hφ_last, hlast_key]
      simp
  have hφ_inj : Function.Injective φ := by
    intro r s hrs
    have h := congrArg (blockEmbeddingS blockS c) hrs
    rw [hφ_key, hφ_key] at h
    rcases Fin.eq_castSucc_or_eq_last r with ⟨r', rfl⟩ | hr
    · rcases Fin.eq_castSucc_or_eq_last s with ⟨s', rfl⟩ | hs
      · simp only [Fin.lastCases_castSucc] at h
        have h' := blockEmbeddingS_injective blockS' c h
        rw [h']
      · rw [hs] at h
        simp only [Fin.lastCases_castSucc, Fin.lastCases_last] at h
        exact absurd h.symm (fun hh => hnot (hh ▸ blockEmbeddingS_mem blockS' c r'))
    · rw [hr] at h ⊢
      rcases Fin.eq_castSucc_or_eq_last s with ⟨s', rfl⟩ | hs
      · simp only [Fin.lastCases_castSucc, Fin.lastCases_last] at h
        exact absurd h.symm (fun hh => hnot (hh ▸ blockEmbeddingS_mem blockS' c s'))
      · rw [hs]
  have hφ_bij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφ_inj, by
      rw [Fintype.card_fin, Fintype.card_fin, hcard]⟩
  let e : Fin (a + 1) ≃ Fin (blockSizeS blockS c) := Equiv.ofBijective φ hφ_bij
  refine ⟨e, ?_, ?_⟩
  · intro r
    show blockEmbeddingS blockS c (e (Fin.castSucc r)) = blockEmbeddingS blockS' c r
    simp only [e, Equiv.ofBijective_apply, hφ_castSucc, hpos_key]
  · show blockEmbeddingS blockS c (e (Fin.last a)) = i₀
    simp only [e, Equiv.ofBijective_apply, hφ_last, hlast_key]

/-- **Adding one row to a tile block.**  If the tile of `blockS` is the tile of
`blockS'` together with the extra index `i₀`, the ambient matrices agree off
`i₀`, and both are bounded by `E`, then the block values differ by at most
`2 * E`. -/
theorem abs_maxCardValue_blockCost_one_row_add_le {N : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (u u' v : Fin N → ι) (D D' : Fin N → Fin N → ℝ) (c : ι)
    (i₀ : Fin N) {E : ℝ} (hE0 : 0 ≤ E)
    (hS : blockFinset u c = insert i₀ (blockFinset u' c))
    (hnot : i₀ ∉ blockFinset u' c)
    (hD : ∀ i, i ≠ i₀ → ∀ j, D' i j = D i j)
    (hbound : ∀ i j, |D i j| ≤ E) (hbound' : ∀ i j, |D' i j| ≤ E) :
    |maxCardValue (blockCost u v D c) - maxCardValue (blockCost u' v D' c)| ≤ 2 * E := by
  classical
  obtain ⟨e, hrowE, hlastE⟩ := exists_blockEmbeddingS_insert_equiv u u' c i₀ hS hnot
  let C : Fin (blockSizeS u' c + 1) → Fin (blockSizeT v c) → ℝ :=
    fun r j => blockCost u v D c (e r) j
  have hCval : maxCardValue C = maxCardValue (blockCost u v D c) := by
    have h := maxCardValue_reindex (c := blockCost u v D c) e.symm
      (Equiv.refl (Fin (blockSizeT v c)))
    simpa [C, Equiv.symm_symm] using h
  have hCbound : ∀ r j, |C r j| ≤ E := by
    intro r j
    exact hbound _ _
  have hsub_eq : (fun r : Fin (blockSizeS u' c) => fun j : Fin (blockSizeT v c) =>
      C (Fin.castLE (Nat.le_add_right (blockSizeS u' c) 1) r) j) =
      blockCost u' v D' c := by
    funext r j
    have hcast : Fin.castLE (Nat.le_add_right (blockSizeS u' c) 1) r = Fin.castSucc r :=
      Fin.ext rfl
    rw [hcast]
    show blockCost u v D c (e (Fin.castSucc r)) j = blockCost u' v D' c r j
    rw [blockCost, blockCost, hrowE r]
    have hmem := blockEmbeddingS_mem u' c r
    have hne : blockEmbeddingS u' c r ≠ i₀ := fun h => hnot (h ▸ hmem)
    exact (hD _ hne _).symm
  have h := abs_maxCardValue_sub_le_add_rows (a := blockSizeS u' c) (δ := 1) C hE0 hCbound
  rw [hsub_eq, hCval] at h
  simpa using h

/-- **Transporting block enumerations along equal tiles.**  If two label arrays
have the same tile `c`, their block enumerations are related by an equivalence
of the block index types. -/
theorem exists_blockEmbeddingS_equiv_of_eq {N : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (u u' : Fin N → ι) (c : ι)
    (hS_eq : blockFinset u c = blockFinset u' c) :
    ∃ e : Fin (blockSizeS u c) ≃ Fin (blockSizeS u' c),
      ∀ r, blockEmbeddingS u' c (e r) = blockEmbeddingS u c r := by
  classical
  let f : Fin (blockSizeS u c) → Fin (blockSizeS u' c) := fun r =>
    Finset.equivFin (blockFinset u' c)
      ⟨blockEmbeddingS u c r, by rw [← hS_eq]; exact blockEmbeddingS_mem u c r⟩
  have hf_inj : Function.Injective f := by
    intro r s hrs
    have h := congrArg (fun x => (Finset.equivFin (blockFinset u' c)).symm x) hrs
    simp only [f, Equiv.symm_apply_apply] at h
    have h2 : blockEmbeddingS u c r = blockEmbeddingS u c s := by
      simpa only [blockEmbeddingS] using congrArg Subtype.val h
    exact blockEmbeddingS_injective u c h2
  have hcard : blockSizeS u c = blockSizeS u' c := by simp [blockSizeS, hS_eq]
  have hf_bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, by
      rw [Fintype.card_fin, Fintype.card_fin, hcard]⟩
  refine ⟨Equiv.ofBijective f hf_bij, ?_⟩
  intro r
  simp only [Equiv.ofBijective_apply, f, blockEmbeddingS, Equiv.symm_apply_apply]

/-- **One-point stability of the tile block.**  Changing the source label and
environment at a single index changes the tile value by at most `2 E`, where
`E` bounds both ambient matrices. -/
theorem abs_maxCardValue_blockCost_one_row_le {N : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (u u' v : Fin N → ι) (D D' : Fin N → Fin N → ℝ) (c : ι)
    (i₀ : Fin N) {E : ℝ} (hE0 : 0 ≤ E)
    (hu : ∀ i, i ≠ i₀ → u' i = u i)
    (hD : ∀ i, i ≠ i₀ → ∀ j, D' i j = D i j)
    (hbound : ∀ i j, |D i j| ≤ E) (hbound' : ∀ i j, |D' i j| ≤ E)
    (hrow : ∀ j, |D' i₀ j - D i₀ j| ≤ 2 * E) :
    |maxCardValue (blockCost u v D c) - maxCardValue (blockCost u' v D' c)| ≤ 2 * E := by
  classical
  by_cases hu0 : u i₀ = c
  · by_cases hu0' : u' i₀ = c
    · -- The changed index stays in the tile: same block finset, one row differs.
      have hS_eq : blockFinset u c = blockFinset u' c := by
        ext i
        by_cases hi : i = i₀
        · subst hi
          simp only [blockFinset, Finset.mem_filter, Finset.mem_univ, true_and, hu0, hu0']
        · simp only [blockFinset, Finset.mem_filter, Finset.mem_univ, true_and, hu i hi]
      obtain ⟨e, he⟩ := exists_blockEmbeddingS_equiv_of_eq u u' c hS_eq
      let c' : Fin (blockSizeS u c) → Fin (blockSizeT v c) → ℝ := fun r j =>
        blockCost u' v D' c (e r) j
      have hc' : maxCardValue c' = maxCardValue (blockCost u' v D' c) := by
        have h := maxCardValue_reindex (c := blockCost u' v D' c) e.symm
          (Equiv.refl (Fin (blockSizeT v c)))
        simpa [c', Equiv.symm_symm] using h
      obtain ⟨r₀, hr₀⟩ := blockEmbeddingS_surjOn u c (by
        simp only [blockFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hu0)
      have hmain := maxCardValue_one_row_le (c := blockCost u v D c) (d := c') r₀
        (E := 2 * E) (by linarith) ?_ ?_
      · rw [hc'] at hmain
        exact hmain
      · intro r hr j
        simp only [c', blockCost, he r]
        have hne : blockEmbeddingS u c r ≠ i₀ := by
          intro h
          exact hr (blockEmbeddingS_injective u c (h.trans hr₀.symm))
        exact (hD _ hne _).symm
      · intro j
        simp only [c', blockCost, he r₀, hr₀]
        rw [abs_sub_comm]
        exact hrow (blockEmbeddingT v c j)
    · -- The changed index enters the tile: an extra row is added.
      have hS : blockFinset u c = insert i₀ (blockFinset u' c) := by
        ext i
        simp only [blockFinset, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert]
        constructor
        · intro hi
          by_cases h : i = i₀
          · exact Or.inl h
          · exact Or.inr (by rw [hu i h]; exact hi)
        · rintro (rfl | hi')
          · exact hu0
          · by_cases h : i = i₀
            · subst h; exact hu0
            · rwa [← hu i h]
      have hnot : i₀ ∉ blockFinset u' c := by
        simp only [blockFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hu0'
      exact abs_maxCardValue_blockCost_one_row_add_le u u' v D D' c i₀ hE0 hS hnot hD
        hbound hbound'
  · by_cases hu0' : u' i₀ = c
    · -- The changed index leaves the tile: the roles of the two blocks swap.
      have hS : blockFinset u' c = insert i₀ (blockFinset u c) := by
        ext i
        simp only [blockFinset, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert]
        constructor
        · intro hi
          by_cases h : i = i₀
          · exact Or.inl h
          · exact Or.inr (by rw [← hu i h]; exact hi)
        · rintro (rfl | hi')
          · exact hu0'
          · by_cases h : i = i₀
            · subst h; exact hu0'
            · rwa [hu i h]
      have hnot : i₀ ∉ blockFinset u c := by
        simp only [blockFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hu0
      have h := abs_maxCardValue_blockCost_one_row_add_le u' u v D' D c i₀ hE0 hS hnot
        (fun i hi j => (hD i hi j).symm) hbound' hbound
      rwa [abs_sub_comm]
    · -- The changed index stays outside the tile in both blocks.
      have hS_eq : blockFinset u c = blockFinset u' c := by
        ext i
        by_cases hi : i = i₀
        · subst hi
          simp only [blockFinset, Finset.mem_filter, Finset.mem_univ, true_and, hu0, hu0']
        · simp only [blockFinset, Finset.mem_filter, Finset.mem_univ, true_and, hu i hi]
      obtain ⟨e, he⟩ := exists_blockEmbeddingS_equiv_of_eq u u' c hS_eq
      let c' : Fin (blockSizeS u c) → Fin (blockSizeT v c) → ℝ := fun r j =>
        blockCost u' v D' c (e r) j
      have hc' : maxCardValue c' = maxCardValue (blockCost u' v D' c) := by
        have h := maxCardValue_reindex (c := blockCost u' v D' c) e.symm
          (Equiv.refl (Fin (blockSizeT v c)))
        simpa [c', Equiv.symm_symm] using h
      have hmat : c' = blockCost u v D c := by
        funext r j
        simp only [c', blockCost, he r]
        have hmem := blockEmbeddingS_mem u c r
        have hne : blockEmbeddingS u c r ≠ i₀ := by
          simp only [blockFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
          exact fun h => hu0 (h ▸ hmem)
        exact hD _ hne _
      rw [hmat] at hc'
      rw [hc']
      simp
      linarith


/-! ## Single-point stability of the frozen tile block -/

/-- **Changing one source point of the frozen tile block.**  If only the source
point at index `i₀` changes, the frozen tile block changes by at most
`2 (|t| B + B)`, where `B` bounds both the frozen kinetic and the probe. -/
theorem abs_frozenModelTileBlock_one_source_le {m : ℕ} {Xs Yt ι : Type*}
    [Fintype ι] [DecidableEq ι] (labS : Xs → ι) (labT : Yt → ι)
    (F G : Xs → Yt → ℝ) (t : ℝ) (c : ι) {B : ℝ} (hB0 : 0 ≤ B)
    (hF : ∀ x y, |F x y| ≤ B) (hG : ∀ x y, |G x y| ≤ B)
    (x x' : Fin (m + 1) → Xs) (y : Fin (m + 1) → Yt) (i₀ : Fin (m + 1))
    (hx : ∀ i, i ≠ i₀ → x' i = x i) :
    |frozenModelTileBlock (fun i => labS (x i)) (fun j => labT (y j))
        (fun i j => F (x i) (y j)) (fun i j => G (x i) (y j)) t c -
      frozenModelTileBlock (fun i => labS (x' i)) (fun j => labT (y j))
        (fun i j => F (x' i) (y j)) (fun i j => G (x' i) (y j)) t c| ≤
      2 * (|t| * B + B) := by
  classical
  have hE0 : 0 ≤ |t| * B + B :=
    add_nonneg (mul_nonneg (abs_nonneg t) hB0) hB0
  let D : Fin (m + 1) → Fin (m + 1) → ℝ :=
    perturbedEdgeCost (fun i j => F (x i) (y j)) (fun i j => G (x i) (y j)) t
  let D' : Fin (m + 1) → Fin (m + 1) → ℝ :=
    perturbedEdgeCost (fun i j => F (x' i) (y j)) (fun i j => G (x' i) (y j)) t
  have hDval : ∀ i j, D i j = F (x i) (y j) + t * G (x i) (y j) := fun i j => rfl
  have hD'val : ∀ i j, D' i j = F (x' i) (y j) + t * G (x' i) (y j) := fun i j => rfl
  have hboundD : ∀ i j, |D i j| ≤ |t| * B + B := by
    intro i j
    rw [hDval]
    calc |F (x i) (y j) + t * G (x i) (y j)|
        ≤ |F (x i) (y j)| + |t * G (x i) (y j)| := abs_add_le _ _
      _ = |F (x i) (y j)| + |t| * |G (x i) (y j)| := by rw [abs_mul]
      _ ≤ B + |t| * B :=
          add_le_add (hF _ _) (mul_le_mul_of_nonneg_left (hG _ _) (abs_nonneg t))
      _ = |t| * B + B := by ring
  have hboundD' : ∀ i j, |D' i j| ≤ |t| * B + B := by
    intro i j
    rw [hD'val]
    calc |F (x' i) (y j) + t * G (x' i) (y j)|
        ≤ |F (x' i) (y j)| + |t * G (x' i) (y j)| := abs_add_le _ _
      _ = |F (x' i) (y j)| + |t| * |G (x' i) (y j)| := by rw [abs_mul]
      _ ≤ B + |t| * B :=
          add_le_add (hF _ _) (mul_le_mul_of_nonneg_left (hG _ _) (abs_nonneg t))
      _ = |t| * B + B := by ring
  have hrow : ∀ j : Fin (m + 1), |D' i₀ j - D i₀ j| ≤ 2 * (|t| * B + B) := by
    intro j
    rw [hD'val, hDval]
    have hFdiff : |F (x' i₀) (y j) - F (x i₀) (y j)| ≤ 2 * B := by
      calc |F (x' i₀) (y j) - F (x i₀) (y j)|
          = |F (x' i₀) (y j) + -(F (x i₀) (y j))| := by ring_nf
        _ ≤ |F (x' i₀) (y j)| + |-(F (x i₀) (y j))| := abs_add_le _ _
        _ = |F (x' i₀) (y j)| + |F (x i₀) (y j)| := by rw [abs_neg]
        _ ≤ B + B := add_le_add (hF _ _) (hF _ _)
        _ = 2 * B := by ring
    have hGdiff : |G (x' i₀) (y j) - G (x i₀) (y j)| ≤ 2 * B := by
      calc |G (x' i₀) (y j) - G (x i₀) (y j)|
          = |G (x' i₀) (y j) + -(G (x i₀) (y j))| := by ring_nf
        _ ≤ |G (x' i₀) (y j)| + |-(G (x i₀) (y j))| := abs_add_le _ _
        _ = |G (x' i₀) (y j)| + |G (x i₀) (y j)| := by rw [abs_neg]
        _ ≤ B + B := add_le_add (hG _ _) (hG _ _)
        _ = 2 * B := by ring
    calc |F (x' i₀) (y j) + t * G (x' i₀) (y j) -
          (F (x i₀) (y j) + t * G (x i₀) (y j))|
        = |(F (x' i₀) (y j) - F (x i₀) (y j)) +
            t * (G (x' i₀) (y j) - G (x i₀) (y j))| := by ring_nf
      _ ≤ |F (x' i₀) (y j) - F (x i₀) (y j)| +
            |t * (G (x' i₀) (y j) - G (x i₀) (y j))| := abs_add_le _ _
      _ = |F (x' i₀) (y j) - F (x i₀) (y j)| +
            |t| * |G (x' i₀) (y j) - G (x i₀) (y j)| := by rw [abs_mul]
      _ ≤ 2 * B + |t| * (2 * B) :=
          add_le_add hFdiff (mul_le_mul_of_nonneg_left hGdiff (abs_nonneg t))
      _ = 2 * (|t| * B + B) := by ring
  have h := BlockStability.abs_maxCardValue_blockCost_one_row_le
    (u := fun i => labS (x i)) (u' := fun i => labS (x' i))
    (v := fun j => labT (y j))
    (D := D) (D' := D') (c := c) (i₀ := i₀) hE0
    (fun i hi => by simp only [hx i hi])
    (fun i hi j => by simp only [hD'val, hDval, hx i hi])
    hboundD hboundD' hrow
  simpa only [frozenModelTileBlock, D, D'] using h

/-- The frozen tile block is invariant under transposition of the two colours. -/
theorem frozenModelTileBlock_transpose {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (blockS blockT : Fin (m + 1) → ι) (F G : Fin (m + 1) → Fin (m + 1) → ℝ)
    (t : ℝ) (c : ι) :
    frozenModelTileBlock blockT blockS (fun j i => F i j) (fun j i => G i j) t c =
      frozenModelTileBlock blockS blockT F G t c := by
  unfold frozenModelTileBlock
  exact PartialMatching.maxCardValue_transpose (blockCost blockS blockT
    (perturbedEdgeCost F G t) c)

/-- **Changing one target point of the frozen tile block.**  Target analogue of
`abs_frozenModelTileBlock_one_source_le`. -/
theorem abs_frozenModelTileBlock_one_target_le {m : ℕ} {Xs Yt ι : Type*}
    [Fintype ι] [DecidableEq ι] (labS : Xs → ι) (labT : Yt → ι)
    (F G : Xs → Yt → ℝ) (t : ℝ) (c : ι) {B : ℝ} (hB0 : 0 ≤ B)
    (hF : ∀ x y, |F x y| ≤ B) (hG : ∀ x y, |G x y| ≤ B)
    (x : Fin (m + 1) → Xs) (y y' : Fin (m + 1) → Yt) (j₀ : Fin (m + 1))
    (hy : ∀ j, j ≠ j₀ → y' j = y j) :
    |frozenModelTileBlock (fun i => labS (x i)) (fun j => labT (y j))
        (fun i j => F (x i) (y j)) (fun i j => G (x i) (y j)) t c -
      frozenModelTileBlock (fun i => labS (x i)) (fun j => labT (y' j))
        (fun i j => F (x i) (y' j)) (fun i j => G (x i) (y' j)) t c| ≤
      2 * (|t| * B + B) := by
  have h := abs_frozenModelTileBlock_one_source_le (m := m)
    (labS := labT) (labT := labS) (F := fun y x => F x y) (G := fun y x => G x y)
    (t := t) (c := c) (B := B) hB0
    (fun y x => hF x y) (fun y x => hG x y) y y' x j₀ hy
  rw [frozenModelTileBlock_transpose (blockS := fun i => labS (x i))
      (blockT := fun j => labT (y j)) (F := fun i j => F (x i) (y j))
      (G := fun i j => G (x i) (y j)) t c,
    frozenModelTileBlock_transpose (blockS := fun i => labS (x i))
      (blockT := fun j => labT (y' j)) (F := fun i j => F (x i) (y' j))
      (G := fun i j => G (x i) (y' j)) t c] at h
  exact h


/-! ## Relative law stability from a product coupling -/

/-- **Relative expectation stability from a coupling with a good event.**

Let `P` and `P'` be coupled by `Pc`.  If on a measurable good set the two
functionals agree, on its complement the first is within relative error
`2 m (δs + δt)` of the second up to the constant `2 m (δs + δt) (|t| Gb)`, and
the coupling mass of the complement is at most `ofReal (m (δs + δt))`, then the
expectations satisfy the same relative bound (with the smallness
`m (δs + δt) ≤ 1` absorbing the mismatch mass into the constant term).

The hypotheses `hgood`/`hbad` are exactly the pointwise inputs that a repeated
application of `abs_frozenModelTileBlock_one_source_le` /
`abs_frozenModelTileBlock_one_target_le` on the mismatched coordinates is meant
to supply. -/
theorem integral_le_of_coupling {Ω : Type*} [MeasurableSpace Ω]
    (P P' : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (f f' : Ω → ℝ) {m δs δt t Gb : ℝ}
    (hm : 0 ≤ m) (hδs : 0 ≤ δs) (hδt : 0 ≤ δt) (hGb : 0 ≤ Gb)
    (hfmeas : Measurable f) (hf'meas : Measurable f')
    (hfint : Integrable f P) (hf'int : Integrable f' P')
    (hf0 : ∀ x, 0 ≤ f x) (hf'0 : ∀ x, 0 ≤ f' x)
    (Pc : Measure (Ω × Ω)) [IsProbabilityMeasure Pc]
    (hP : Pc.map Prod.fst = P) (hP' : Pc.map Prod.snd = P')
    (Good : Set Ω) (hGood : MeasurableSet Good)
    (hmass : Pc (Prod.fst ⁻¹' Goodᶜ) ≤ ENNReal.ofReal (m * (δs + δt)))
    (hgood : ∀ᵐ p ∂Pc, p.1 ∈ Good → f p.1 = f' p.2)
    (hbad : ∀ᵐ p ∂Pc, p.1 ∉ Good →
      f p.1 ≤ (1 + 2 * m * (δs + δt)) * f' p.2 + 2 * m * (δs + δt) * (|t| * Gb))
    (hsmall : m * (δs + δt) ≤ 1) :
    ∫ x, f x ∂P ≤ (1 + 2 * m * (δs + δt)) * (∫ x, f' x ∂P') +
      2 * m * (δs + δt) * (|t| * Gb) := by
  let C : ℝ := 2 * m * (δs + δt)
  let K : ℝ := |t| * Gb
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hK : 0 ≤ K := mul_nonneg (abs_nonneg t) hGb
  have hf_comp : Integrable (fun p : Ω × Ω ↦ f p.1) Pc := by
    have h : Integrable f (Pc.map Prod.fst) := by rw [hP]; exact hfint
    exact h.comp_measurable measurable_fst
  have hf'_comp : Integrable (fun p : Ω × Ω ↦ f' p.2) Pc := by
    have h : Integrable f' (Pc.map Prod.snd) := by rw [hP']; exact hf'int
    exact h.comp_measurable measurable_snd
  have hpoint : ∀ᵐ p ∂Pc, f p.1 ≤ (1 + C) * f' p.2 + C * K := by
    filter_upwards [hgood, hbad] with p hg hb
    by_cases hp : p.1 ∈ Good
    · rw [hg hp]
      nlinarith [hf'0 p.2]
    · exact hb hp
  have hA : ∫ x, f x ∂P = ∫ p, f p.1 ∂Pc := by
    rw [← hP]
    exact integral_map measurable_fst.aemeasurable
      (by rw [hP]; exact hfmeas.aestronglyMeasurable)
  have hA' : ∫ x, f' x ∂P' = ∫ p, f' p.2 ∂Pc := by
    rw [← hP']
    exact integral_map measurable_snd.aemeasurable
      (by rw [hP']; exact hf'meas.aestronglyMeasurable)
  rw [hA, hA']
  calc
    ∫ p, f p.1 ∂Pc ≤ ∫ p, ((1 + C) * f' p.2 + C * K) ∂Pc :=
      integral_mono_ae hf_comp ((hf'_comp.const_mul _).add (integrable_const _)) hpoint
    _ = (1 + C) * (∫ p, f' p.2 ∂Pc) + C * K := by
      rw [integral_add (hf'_comp.const_mul _) (integrable_const _), integral_const_mul]
      simp
    _ = _ := rfl

end BlockStability

end OTSelector
