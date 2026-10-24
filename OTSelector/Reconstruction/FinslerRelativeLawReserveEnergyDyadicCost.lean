import OTSelector.Reconstruction.FinslerRelativeLawReserveEnergyDyadicComplete

/-!
# Actual quadratic-majorized kinetic and bounded-probe repair

The concrete adaptive completion budget applies to any physical kinetic matrix
with a nonnegative quadratic coordinate majorant. A signed bounded probe costs
only its bound times the actual number of added edges. Illegal repaired edges
remain a separately reported count.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- An actual full extension with a quadratic-majorized kinetic cost and a
signed bounded probe. The coefficient may depend on the sample size; no
uniform kinetic edge bound is used. -/
theorem exists_completion_quadratic_probe_le_dyadicBudget
    {N q : ℕ} (K : ℕ) (σ : OTSelector.PartialMatching N N)
    (x y : Fin N → Fin q → ℝ) (u : Fin q → ℝ)
    (hu : ∀ i, 0 < u i ∧ u i ≤ 1)
    (hx : ∀ i k, 0 ≤ x i k ∧ x i k ≤ 1)
    (hy : ∀ j k, 0 ≤ y j k ∧ y j k ≤ 1)
    (allowed : Finset (Fin N × Fin N)) (c g : Fin N → Fin N → ℝ)
    {A G : ℝ} (hA : 0 ≤ A) (hc : ∀ i j, c i j ≤ A * ∑ k, (x i k - y j k) ^ 2)
    (hg : ∀ i j, |g i j| ≤ G) (t : ℝ) :
    ∃ τ : OTSelector.PartialMatching N N,
      τ.card = N ∧ σ.edges ⊆ τ.edges ∧
      (∑ e ∈ τ.edges \ σ.edges, (c e.1 e.2 + t * g e.1 e.2)) ≤
        A * dyadicOrphanRepairBudget K σ x y u + |t| * G * ((N : ℝ) - σ.card) ∧
      ((τ.edges \ σ.edges).filter fun e ↦ e ∉ allowed).card ≤ N - σ.card := by
  classical
  obtain ⟨τ, hτ, hsub, hquad, hillegal⟩ :=
    exists_completion_le_dyadicOrphanRepairBudget K σ x y u hu hx hy allowed
  refine ⟨τ, hτ, hsub, ?_, hillegal⟩
  have hprobe (i j : Fin N) : t * g i j ≤ |t| * G := by
    calc
      _ ≤ |t * g i j| := le_abs_self _
      _ = |t| * |g i j| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hg i j) (abs_nonneg _)
  have hcount : (((τ.edges \ σ.edges).card : ℕ) : ℝ) = (N : ℝ) - σ.card := by
    rw [Finset.card_sdiff_of_subset hsub]
    have hσ : σ.card ≤ N := σ.card_le.trans (min_le_left N N)
    change ((τ.card - σ.card : ℕ) : ℝ) = _
    rw [hτ, Nat.cast_sub hσ]
  calc
    _ ≤ ∑ e ∈ τ.edges \ σ.edges,
        (A * (∑ k, (x e.1 k - y e.2 k) ^ 2) + |t| * G) :=
      Finset.sum_le_sum fun e _ ↦ add_le_add (hc e.1 e.2) (hprobe e.1 e.2)
    _ = A * (∑ e ∈ τ.edges \ σ.edges, ∑ k, (x e.1 k - y e.2 k) ^ 2) +
        |t| * G * ((N : ℝ) - σ.card) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul, hcount]
      ring
    _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left hquad hA) _

end OTSelector.Reconstruction
