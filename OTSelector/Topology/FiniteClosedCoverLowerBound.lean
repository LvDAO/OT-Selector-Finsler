import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Topology.ContinuousOn

/-!
# Topology.FiniteClosedCoverLowerBound

Conditions: A continuous-within map whose nearby image lies in finitely many closed pieces, with centered inverse bounds on pieces containing the central image.

Objects: One positive centered lower bound valid near the source center.

Proof detail: Continuity excludes every closed piece not containing the central image. Take a common finite bound for the remaining inverse constants, intersect their eventual neighborhoods and invert the resulting positive constant.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4, Appendix 4A](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=6): Section 4A2A–4A2B, pp. 6–10 (closures, Hausdorff spaces, continuity and products).

Source relation: Elementary finite closed-cover gluing, derived locally from continuity and finite intersections; source set membership/density is not added.
-/

/-!
# Centered lower bounds from a finite closed cover

A continuous map whose nearby images lie in finitely many closed pieces inherits a
centered lower bound from the inverse bounds on the pieces containing its central
image. The source set is arbitrary, and coverage is an explicit eventual hypothesis.
-/

open Set Filter Topology
open scoped BigOperators

namespace OTSelector.Geometry

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [Fintype ι]

/-- Finitely many closed target pieces glue centered inverse estimates to a positive
lower bound near the source center. Only pieces containing the central image need an
estimate; continuity eventually excludes all other pieces. -/
theorem exists_pos_eventually_norm_sub_le_of_finite_closed_cover
    {f : E → F} {s : Set E} {x₀ : E} (P : ι → Set F)
    (hclosed : ∀ i, IsClosed (P i)) (hf : ContinuousWithinAt f s x₀)
    (hcover : ∀ᶠ x in 𝓝[s] x₀, ∃ i, f x ∈ P i)
    (hbound : ∀ i, f x₀ ∈ P i → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ x in 𝓝[s] x₀, f x ∈ P i → ‖x - x₀‖ ≤ C * ‖f x - f x₀‖) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x in 𝓝[s] x₀, c * ‖x - x₀‖ ≤ ‖f x - f x₀‖ := by
  classical
  have hpieces : ∀ i, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ x in 𝓝[s] x₀, f x ∈ P i → ‖x - x₀‖ ≤ C * ‖f x - f x₀‖ := by
    intro i
    by_cases hi : f x₀ ∈ P i
    · exact hbound i hi
    · refine ⟨0, le_rfl, ?_⟩
      filter_upwards [hf.eventually ((hclosed i).isOpen_compl.mem_nhds hi)] with x hx
      exact fun hxi ↦ (hx hxi).elim
  choose C hCnonneg hCbound using hpieces
  let D : ℝ := 1 + ∑ i, C i
  have hDpos : 0 < D := by
    have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ ↦ hCnonneg i
    dsimp [D]
    linarith
  refine ⟨1 / D, one_div_pos.mpr hDpos, ?_⟩
  filter_upwards [hcover, eventually_all.mpr hCbound] with x hx hxb
  obtain ⟨i, hi⟩ := hx
  have hCi : C i ≤ D := by
    have hsum : C i ≤ ∑ j, C j :=
      Finset.single_le_sum (fun j _ ↦ hCnonneg j) (Finset.mem_univ i)
    dsimp [D]
    linarith
  have hxD : ‖x - x₀‖ ≤ D * ‖f x - f x₀‖ :=
    (hxb i hi).trans (mul_le_mul_of_nonneg_right hCi (norm_nonneg _))
  rw [one_div_mul_eq_div]
  exact (div_le_iff₀ hDpos).2 (by simpa only [mul_comm] using hxD)

/-- The finite closed-cover bound with each inverse estimate stated in the filter
restricted to its source piece. No source membership or density hypothesis is needed. -/
theorem exists_pos_eventually_norm_sub_le_of_finite_closed_cover_within_piece
    {f : E → F} {s : Set E} {x₀ : E} (P : ι → Set F)
    (hclosed : ∀ i, IsClosed (P i)) (hf : ContinuousWithinAt f s x₀)
    (hcover : ∀ᶠ x in 𝓝[s] x₀, ∃ i, f x ∈ P i)
    (hbound : ∀ i, f x₀ ∈ P i → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ x in 𝓝[s ∩ f ⁻¹' (P i)] x₀, ‖x - x₀‖ ≤ C * ‖f x - f x₀‖) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x in 𝓝[s] x₀, c * ‖x - x₀‖ ≤ ‖f x - f x₀‖ := by
  apply exists_pos_eventually_norm_sub_le_of_finite_closed_cover P hclosed hf hcover
  intro i hi
  obtain ⟨C, hCnonneg, hCbound⟩ := hbound i hi
  refine ⟨C, hCnonneg, ?_⟩
  simpa only [nhdsWithin_inter', eventually_inf_principal, mem_preimage] using hCbound

end OTSelector.Geometry
