import OTSelector.Reconstruction.FinslerRelativeLawReserveEnergyExpectation

/-!
The explicit finite-cutoff flux coefficient admits relative quadratic-energy
absorption, with its full retained-cardinality remainder displayed. Unrestricted
completion also records the possible number of clock-illegal added edges.
-/

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction

/-- A completion's possible illegal added edges remain bounded by its actual
added cardinality. This assertion does not claim any of those edges are legal. -/
theorem card_illegal_added_le_missing {m n : ℕ}
    (σ τ : OTSelector.PartialMatching m n) (hτ : τ.card = min m n)
    (hsub : σ.edges ⊆ τ.edges) (allowed : Finset (Fin m × Fin n)) :
    ((τ.edges \ σ.edges).filter fun e ↦ e ∉ allowed).card ≤ min m n - σ.card := by
  classical
  calc
    _ ≤ (τ.edges \ σ.edges).card := Finset.card_filter_le _ _
    _ = min m n - σ.card := by rw [Finset.card_sdiff_of_subset hsub]; exact congrArg (· - σ.card) hτ

/-- The actual completion budget is nonnegative for nonnegative hierarchy
weights and base cost. -/
theorem adaptiveOrphanRepairBudget_nonneg
    {X : Type*} {K N : ℕ} {C : Fin K → Type*} [∀ k, Fintype (C k)]
    (σ : OTSelector.PartialMatching N N) (cell : (k : Fin K) → X → C k)
    (x y : Fin N → X) {base : ℝ} (hb : 0 ≤ base)
    (weight : Fin K → ℝ) (hw : ∀ k, 0 ≤ weight k) :
    0 ≤ adaptiveOrphanRepairBudget σ cell x y base weight := by
  have hcard : (σ.card : ℝ) ≤ N := by exact_mod_cast σ.card_le.trans (min_le_left N N)
  unfold adaptiveOrphanRepairBudget
  apply add_nonneg (mul_nonneg (sub_nonneg.mpr hcard) hb)
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro k hk
  apply mul_nonneg (hw k)
  apply add_nonneg (Finset.sum_nonneg fun c _ ↦ abs_nonneg _)
  exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)

/-- A finite-cutoff coefficient times actual retained displacement can be
absorbed into any prescribed positive fraction of quadratic kinetic energy.
The square of that coefficient remains in an explicit count remainder. -/
theorem retainedCoordinateDisplacement_mul_le_energy
    {m n q : ℕ} (σ : OTSelector.PartialMatching m n)
    (x : Fin m → Fin q → ℝ) (y : Fin n → Fin q → ℝ)
    (A : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    A * retainedCoordinateDisplacement σ x y ≤
      ρ * retainedSquaredDisplacement σ x y +
        (σ.card : ℝ) * q * A ^ 2 / (4 * ρ) := by
  have hpoint (d : ℝ) : A * |d| ≤ ρ * d ^ 2 + A ^ 2 / (4 * ρ) := by
    have hs := sq_nonneg (2 * ρ * |d| - A)
    have heq : ρ * d ^ 2 + A ^ 2 / (4 * ρ) =
        (4 * ρ ^ 2 * d ^ 2 + A ^ 2) / (4 * ρ) := by field_simp
    rw [heq]
    apply (le_div_iff₀ (by positivity : 0 < 4 * ρ)).mpr
    by_cases hd : 0 ≤ d
    · rw [abs_of_nonneg hd] at hs ⊢
      nlinarith
    · rw [abs_of_neg (lt_of_not_ge hd)] at hs ⊢
      nlinarith
  unfold retainedCoordinateDisplacement retainedSquaredDisplacement
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ e ∈ σ.edges, ∑ i : Fin q,
        (ρ * (x e.1 i - y e.2 i) ^ 2 + A ^ 2 / (4 * ρ)) := by
      apply Finset.sum_le_sum
      intro e he
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ ↦ hpoint _
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, OTSelector.PartialMatching.card]
      ring

/-- Expected relative kinetic absorption uses the actual selected matching's
quadratic energy and cardinality, without a law for its unused endpoints. -/
theorem integral_retainedCoordinateDisplacement_mul_le_energy
    {Ω : Type*} [MeasurableSpace Ω] {m n q : ℕ} (P : Measure Ω)
    (σ : Ω → OTSelector.PartialMatching m n)
    (xs : Fin m → Ω → Fin q → ℝ) (ys : Fin n → Ω → Fin q → ℝ)
    (hL : Integrable (fun ω ↦ retainedCoordinateDisplacement (σ ω)
      (fun i ↦ xs i ω) (fun j ↦ ys j ω)) P)
    (hE : Integrable (fun ω ↦ retainedSquaredDisplacement (σ ω)
      (fun i ↦ xs i ω) (fun j ↦ ys j ω)) P)
    (hcard : Integrable (fun ω ↦ ((σ ω).card : ℝ)) P)
    (A : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    A * (∫ ω, retainedCoordinateDisplacement (σ ω)
      (fun i ↦ xs i ω) (fun j ↦ ys j ω) ∂P) ≤
      ρ * (∫ ω, retainedSquaredDisplacement (σ ω)
        (fun i ↦ xs i ω) (fun j ↦ ys j ω) ∂P) +
        (∫ ω, ((σ ω).card : ℝ) ∂P) * q * A ^ 2 / (4 * ρ) := by
  have hb := integral_mono (hL.const_mul A)
    ((hE.const_mul ρ).add (((hcard.mul_const q).mul_const (A ^ 2)).div_const (4 * ρ)))
    (fun ω ↦ retainedCoordinateDisplacement_mul_le_energy (σ ω)
      (fun i ↦ xs i ω) (fun j ↦ ys j ω) A hρ)
  have heq := integral_add (hE.const_mul ρ)
    (((hcard.mul_const q).mul_const (A ^ 2)).div_const (4 * ρ))
  simp only [Pi.add_apply] at hb
  rw [integral_const_mul, heq, integral_const_mul, integral_div,
    integral_mul_const, integral_mul_const] at hb
  exact hb

end OTSelector.Reconstruction
