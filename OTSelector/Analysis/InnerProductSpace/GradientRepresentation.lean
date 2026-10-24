import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Analysis.InnerProductSpace.GradientRepresentation

## Lemma skeleton

* **Conditions:** A linear discrepancy is bounded by C≥0 times the norm of a linear gradient map into a complete real Hilbert space.

* **Objects:** A weak flux representing the discrepancy with norm≤C, minimal among all representing fluxes.

* **Proof detail:** Factor the discrepancy through the gradient range, extend it continuously to the closed range, and take the Hilbert Riesz representative there. Its inclusion in the ambient space represents the discrepancy; orthogonality to the range shows every other representative has at least its norm.

## Mathematical sources

- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=72): Section 1.5.2, Theorem 1.5.6, p. 63.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=62): Section 1.4, Theorem 1.4.13, p. 53.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=61): Section 1.4, Exercises 1.4.12–1.4.13, pp. 52–53.

Source relation (composition): A functional-analytic construction and minimum-norm characterization; no Neumann PDE solvability theorem is assumed.
-/

/-!
# Constructing a weak Neumann flux from the actual gradient estimate

A discrepancy acts on the original test functions only through their gradient.
The bounded gradient functional is extended without changing its norm, and the
Riesz representative is an actual Hilbert-space flux. No PDE solver is assumed.
-/
open Set Function
open scoped RealInnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 2200000

/-- A bound on the actual test-gradient pairing constructs a genuine weak
flux, with the same energy bound and minimum norm among all fluxes realizing
those same test pairings. The test space itself need not be complete. -/
theorem exists_weakFlux_of_gradient_bound
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [AddCommGroup V] [Module ℝ V]
    (grad : V →ₗ[ℝ] H) (discrepancy : V →ₗ[ℝ] ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ v, ‖discrepancy v‖ ≤ C * ‖grad v‖) :
    ∃ flux : H, (∀ v, inner ℝ flux (grad v) = discrepancy v) ∧ ‖flux‖ ≤ C ∧
      ∀ other : H, (∀ v, inner ℝ other (grad v) = discrepancy v) → ‖flux‖ ≤ ‖other‖ := by
  classical
  have hconsistent {x y : V} (hxy : grad x = grad y) : discrepancy x = discrepancy y := by
    have hzero : grad (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hz : discrepancy (x - y) = 0 := norm_le_zero_iff.mp
      (by simpa only [hzero, norm_zero, mul_zero] using hbound (x - y))
    rw [map_sub] at hz
    exact sub_eq_zero.mp hz
  let pre : grad.range → V := fun y ↦ Classical.choose y.property
  have hpre (y : grad.range) : grad (pre y) = (y : H) := Classical.choose_spec y.property
  let linear : grad.range →ₗ[ℝ] ℝ :=
    { toFun := fun y ↦ discrepancy (pre y)
      map_add' := fun x y ↦ by
        calc
          _ = discrepancy (pre x + pre y) := hconsistent (by simp only [map_add, hpre]; rfl)
          _ = _ := discrepancy.map_add _ _
      map_smul' := fun a y ↦ by
        calc
          _ = discrepancy (a • pre y) := hconsistent (by simp only [map_smul, hpre]; rfl)
          _ = _ := discrepancy.map_smul _ _ }
  have hnorm (y : grad.range) : ‖linear y‖ ≤ C * ‖y‖ := by
    change ‖discrepancy (pre y)‖ ≤ C * ‖(y : H)‖
    simpa only [hpre] using hbound (pre y)
  let functional : StrongDual ℝ grad.range := linear.mkContinuous C hnorm
  obtain ⟨extension, hext, hnormext⟩ := exists_extension_norm_eq grad.range functional
  let flux : H := (InnerProductSpace.toDual ℝ H).symm extension
  have hfluxnorm : ‖flux‖ = ‖functional‖ := by
    calc
      _ = ‖extension‖ := (InnerProductSpace.toDual ℝ H).symm.norm_map extension
      _ = _ := hnormext
  refine ⟨flux, ?_, hfluxnorm.le.trans (functional.opNorm_le_bound hC hnorm), ?_⟩
  · intro v
    calc
      _ = extension (grad v) := InnerProductSpace.toDual_symm_apply
      _ = functional (grad.rangeRestrict v) := hext (grad.rangeRestrict v)
      _ = discrepancy v := by
        change discrepancy (pre (grad.rangeRestrict v)) = discrepancy v
        exact hconsistent (hpre (grad.rangeRestrict v))
  · intro other hother
    have hfnorm : ‖functional‖ ≤ ‖other‖ := functional.opNorm_le_bound (norm_nonneg other) fun y ↦ by
      change ‖discrepancy (pre y)‖ ≤ ‖other‖ * ‖(y : H)‖
      have hy := hother (pre y)
      rw [hpre] at hy
      rw [← hy]
      exact norm_inner_le_norm other (y : H)
    exact hfluxnorm.le.trans hfnorm

end OTSelector.Reconstruction
