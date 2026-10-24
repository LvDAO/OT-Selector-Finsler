import OTSelector.Finite.MaxCardValueRowStability
import OTSelector.Finite.MaxCardValueScaling
import OTSelector.Finite.MaxCardValueSigned
import OTSelector.Finite.PartialMatching
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.MarkedRelativeLawRepair.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.MarkedRelativeLawRepair`; the selected original proof blocks follow. -/
section

/-!
# Probability.MarkedRelativeLawRepair

**Conditions:** The original kinetic costs are nonnegative, probes have the explicit absolute bound, and a full repair matching contains the unchanged sampled core.

**Objects:** Relative optimal-value comparison retaining actual repair energy and the count of changed endpoints.

**Proof detail:** Split both objective sums into the shared core and its complement, use the relative kinetic bound only on the core, and charge bounded probe errors per missing edge; endpoint injectivity bounds missing edges by moved source/target counts.

**Sources:** [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [OTSelector project, Original strict-screen residual slack and repair](main.tex#strict-screen-residual-slack), main.tex label strict-screen-residual-slack, line 6749.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Relative law comparison through a retained matching

A common sampling retains the edges whose two endpoints do not move. The
kinetic cost on those edges is compared relatively. All remaining kinetic
cost is kept as the cost of an explicit repair matching; no uniform bound on
the kinetic matrix is used. Only the bounded probe is charged per deleted edge.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector.PartialMatching

variable {m n : ℕ}

/-- A matching obtained from the model optimum by retaining a common core and
repairing it gives a relative comparison with the exact repair kinetic cost.
The repair may depend on the entire coupled sample. -/
theorem maxCardValue_le_relative_common_core_add_repair
    {c c' g g' : Fin m → Fin n → ℝ} {t G ρ : ℝ}
    (hρ : 0 ≤ ρ) (hG : 0 ≤ G)
    (hc : ∀ i j, 0 ≤ c i j)
    (hg : ∀ i j, |g i j| ≤ G) (hg' : ∀ i j, |g' i j| ≤ G)
    (σ τ : PartialMatching m n) (hσ : σ.card = min m n)
    (hσopt : σ.cost (fun i j ↦ c i j + t * g i j) =
      maxCardValue (fun i j ↦ c i j + t * g i j))
    (hτ : τ.card = min m n)
    (s : Finset (Fin m × Fin n)) (hsσ : s ⊆ σ.edges) (hsτ : s ⊆ τ.edges)
    (hrel : ∀ e ∈ s, c' e.1 e.2 ≤ (1 + ρ) * c e.1 e.2)
    (hprobe : ∀ e ∈ s, g' e.1 e.2 = g e.1 e.2) :
    maxCardValue (fun i j ↦ c' i j + t * g' i j) ≤
      (1 + ρ) * maxCardValue (fun i j ↦ c i j + t * g i j) +
        ρ * |t| * G * (min m n : ℝ) +
        (∑ e ∈ τ.edges \ s, c' e.1 e.2) +
        2 * |t| * G * ((min m n - s.card : ℕ) : ℝ) := by
  classical
  let K := |t| * G
  have hK : 0 ≤ K := mul_nonneg (abs_nonneg t) hG
  have ht (i : Fin m) (j : Fin n) : |t * g i j| ≤ K := by
    simpa only [abs_mul] using mul_le_mul_of_nonneg_left (hg i j) (abs_nonneg t)
  have ht' (i : Fin m) (j : Fin n) : t * g' i j ≤ K :=
    (le_abs_self _).trans (by
      simpa only [abs_mul] using mul_le_mul_of_nonneg_left (hg' i j) (abs_nonneg t))
  have hshift (i : Fin m) (j : Fin n) : 0 ≤ c i j + t * g i j + K := by
    have := (abs_le.mp (ht i j)).1
    linarith [hc i j]
  have hret : (∑ e ∈ s, (c' e.1 e.2 + t * g' e.1 e.2)) ≤
      (1 + ρ) * (σ.cost (fun i j ↦ c i j + t * g i j + K)) -
        (s.card : ℝ) * K := by
    calc (∑ e ∈ s, (c' e.1 e.2 + t * g' e.1 e.2))
        ≤ ∑ e ∈ s, ((1 + ρ) * (c e.1 e.2 + t * g e.1 e.2 + K) - K) := by
          apply Finset.sum_le_sum
          intro e he
          rw [hprobe e he]
          have htk : 0 ≤ t * g e.1 e.2 + K := by
            have := (abs_le.mp (ht e.1 e.2)).1
            linarith
          have := mul_nonneg hρ htk
          nlinarith [hrel e he]
      _ = (1 + ρ) * (∑ e ∈ s, (c e.1 e.2 + t * g e.1 e.2 + K)) -
          (s.card : ℝ) * K := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
            simp
      _ ≤ (1 + ρ) * (σ.cost (fun i j ↦ c i j + t * g i j + K)) -
          (s.card : ℝ) * K := by
            apply sub_le_sub_right
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            exact σ.cost_subMatching_le _ s hsσ hshift
  have hrepair : (∑ e ∈ τ.edges \ s, (c' e.1 e.2 + t * g' e.1 e.2)) ≤
      (∑ e ∈ τ.edges \ s, c' e.1 e.2) +
        ((min m n - s.card : ℕ) : ℝ) * K := by
    calc (∑ e ∈ τ.edges \ s, (c' e.1 e.2 + t * g' e.1 e.2))
        ≤ ∑ e ∈ τ.edges \ s, (c' e.1 e.2 + K) := by
          exact Finset.sum_le_sum fun e _ ↦ add_le_add_right (ht' e.1 e.2) _
      _ = (∑ e ∈ τ.edges \ s, c' e.1 e.2) +
          ((min m n - s.card : ℕ) : ℝ) * K := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
              Finset.card_sdiff_of_subset hsτ]
            change _ + ((τ.card - s.card : ℕ) : ℝ) * K = _
            rw [hτ]
  have hsplit : τ.cost (fun i j ↦ c' i j + t * g' i j) =
      (∑ e ∈ s, (c' e.1 e.2 + t * g' e.1 e.2)) +
        ∑ e ∈ τ.edges \ s, (c' e.1 e.2 + t * g' e.1 e.2) := by
    exact (Finset.sum_sdiff hsτ (f := fun e ↦ c' e.1 e.2 + t * g' e.1 e.2)).symm.trans
      (add_comm _ _)
  have hcard : s.card ≤ min m n := (Finset.card_le_card hsσ).trans_eq hσ
  have hcardR : ((min m n - s.card : ℕ) : ℝ) = (min m n : ℝ) - s.card :=
    by simpa only [Nat.cast_min] using (Nat.cast_sub (R := ℝ) hcard)
  have hshiftcost : σ.cost (fun i j ↦ c i j + t * g i j + K) =
      maxCardValue (fun i j ↦ c i j + t * g i j) + (min m n : ℝ) * K := by
    rw [cost_add_const, hσopt, hσ]
    simp
  have hmain := maxCardValue_le_of_card (fun i j ↦ c' i j + t * g' i j) hτ
  rw [hsplit] at hmain
  rw [hshiftcost] at hret
  dsimp only [K] at hret hrepair hcardR hmain ⊢
  rw [hcardR] at hrepair ⊢
  nlinarith

/-- Retain exactly the model edges whose source and target coordinates both
agree with the actual sample. -/
def commonSampleCore {X Y : Type*} (σ : PartialMatching m n)
    (x x' : Fin m → X) (y y' : Fin n → Y) : Finset (Fin m × Fin n) := by
  classical
  exact σ.edges.filter fun e ↦ x e.1 = x' e.1 ∧ y e.2 = y' e.2

theorem commonSampleCore_subset {X Y : Type*} (σ : PartialMatching m n)
    (x x' : Fin m → X) (y y' : Fin n → Y) :
    commonSampleCore σ x x' y y' ⊆ σ.edges := by
  classical
  exact Finset.filter_subset _ _

/-- At most one retained edge uses any target index. -/
theorem card_filter_cols_le (σ : PartialMatching m n) (S : Finset (Fin n)) :
    (σ.edges.filter fun e ↦ e.2 ∈ S).card ≤ S.card := by
  classical
  have hsub : (σ.edges.filter fun e ↦ e.2 ∈ S).image Prod.snd ⊆ S := by
    intro j hj
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_filter.mp he).2
  have hinj : Set.InjOn Prod.snd
      (↑(σ.edges.filter fun e ↦ e.2 ∈ S) : Set (Fin m × Fin n)) := by
    intro e he e' he' h
    exact σ.col_inj e (Finset.mem_filter.mp he).1 e'
      (Finset.mem_filter.mp he').1 h
  calc (σ.edges.filter fun e ↦ e.2 ∈ S).card
      = ((σ.edges.filter fun e ↦ e.2 ∈ S).image Prod.snd).card := by
        rw [Finset.card_image_of_injOn hinj]
    _ ≤ S.card := Finset.card_le_card hsub

/-- Removing every edge incident to a moved sample deletes at most the number
of moved source and target coordinates, even for a sample-dependent optimum. -/
theorem card_sdiff_commonSampleCore_le {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (σ : PartialMatching m n)
    (x x' : Fin m → X) (y y' : Fin n → Y) :
    (σ.edges \ commonSampleCore σ x x' y y').card ≤
      (Finset.univ.filter fun i ↦ x i ≠ x' i).card +
        (Finset.univ.filter fun j ↦ y j ≠ y' j).card := by
  classical
  let S := Finset.univ.filter fun i ↦ x i ≠ x' i
  let T := Finset.univ.filter fun j ↦ y j ≠ y' j
  have heq : σ.edges \ commonSampleCore σ x x' y y' =
      (σ.edges.filter fun e ↦ e.1 ∈ S) ∪ (σ.edges.filter fun e ↦ e.2 ∈ T) := by
    ext e
    simp only [commonSampleCore, S, T, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_union]
    tauto
  rw [heq]
  exact Finset.card_union_le _ _ |>.trans
    (Nat.add_le_add (σ.card_filter_rows_le S) (σ.card_filter_cols_le T))

/-- The count form used when the model matching is maximum cardinality. -/
theorem missing_commonSampleCore_le {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (σ : PartialMatching m n)
    (hσ : σ.card = min m n)
    (x x' : Fin m → X) (y y' : Fin n → Y) :
    min m n - (commonSampleCore σ x x' y y').card ≤
      (Finset.univ.filter fun i ↦ x i ≠ x' i).card +
        (Finset.univ.filter fun j ↦ y j ≠ y' j).card := by
  have h := card_sdiff_commonSampleCore_le σ x x' y y'
  rwa [Finset.card_sdiff_of_subset (commonSampleCore_subset σ x x' y y'),
    ← card, hσ] at h

end OTSelector.PartialMatching

end
end
