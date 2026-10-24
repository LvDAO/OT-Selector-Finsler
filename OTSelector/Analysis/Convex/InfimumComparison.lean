import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
## Lemma skeleton

* **Conditions:** Real greatest lower bounds of objectives on one common feasible set.
* **Objects:** Attained infima, two uniformly close objective values and concave lower envelopes.
* **Proof detail:** Use the greatest-lower-bound property in each direction; for concavity bound every competitor.

## Mathematical sources

* Sheldon Axler, *Supplement for Measure, Integration & Real Analysis*, Section C, Definitions 0.32 and 0.35, pp. 18–19.
  https://measure.axler.net/SupplementMIRA.pdf#page=18
* Stephen Boyd; Lieven Vandenberghe, *Convex Optimization (2004)*, Section 3.2.3, pp. 80–81 (p. 81 also states the concave infimum version).
  https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=95

**Relationship to the sources:** The uniform-error estimate needs neither convexity nor attainment. Envelope concavity is directly stated in Boyd; the exact IsGLB APIs are formal wrappers.
-/

/-!
# Comparing objective infima

This infrastructure concerns a real objective on a fixed feasible set. The feasible objects may
be permutations, partial matchings, or fractional allocations; no geometry or probability enters.

## Lemma skeleton

* **Conditions:** identify each value as the greatest lower bound of its feasible objectives.
* **Objects:** a common feasible set `s`, objectives `f`, `g`, and their real values `u`, `v`.
* **Proof detail:** compare objectives on `s`, then use the greatest-lower-bound property once in
  each direction. Attainment is an optional way to establish that property.

For tilt-dependent objectives, the same lower-bound argument transfers concavity of every
competitor to concavity of the value. Source locations are listed beside each technique below.
-/

open Set

namespace OTSelector.Analysis.Convex

variable {α : Type*} {s : Set α} {f g : α → ℝ} {u v B : ℝ}

/-- An attained lower bound is the objective infimum.

This is the greatest-lower-bound characterization of an infimum; see Axler, *Supplement for
Measure, Integration & Real Analysis*, §C, Definitions 0.32 and 0.35, pp. 18–19:
<https://measure.axler.net/SupplementMIRA.pdf#page=18>.
-/
theorem isGLB_image_of_le_of_attained
    (hle : ∀ x ∈ s, u ≤ f x) (hatt : ∃ x ∈ s, f x = u) : IsGLB (f '' s) u := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hle x hx
  · intro b hb
    obtain ⟨x, hx, hfx⟩ := hatt
    exact hfx ▸ hb ⟨x, hx, rfl⟩

/-- Uniform objective errors bound the error of the infima, without assuming attainment.

This is an elementary corollary of the greatest-lower-bound property, applied once in each
direction; see Axler, *Supplement for Measure, Integration & Real Analysis*, §C, Definition 0.32,
p. 18: <https://measure.axler.net/SupplementMIRA.pdf#page=18>. The book supplies the underlying
infimum principle; the uniform-error corollary is proved here and needs no convexity.
-/
theorem abs_sub_le_of_isGLB_image
    (hf : IsGLB (f '' s) u) (hg : IsGLB (g '' s) v)
    (hbound : ∀ x ∈ s, |f x - g x| ≤ B) : |u - v| ≤ B := by
  have hle (f g : α → ℝ) (u v : ℝ)
      (hf : IsGLB (f '' s) u) (hg : IsGLB (g '' s) v)
      (hb : ∀ x ∈ s, |f x - g x| ≤ B) : u - v ≤ B := by
    have hlow : u - B ≤ v := hg.2 (by
      rintro _ ⟨x, hx, rfl⟩
      have h1 := hf.1 ⟨x, hx, rfl⟩
      have h2 := (abs_le.mp (hb x hx)).2
      linarith)
    linarith
  exact abs_sub_le_iff.mpr ⟨hle f g u v hf hg hbound,
    hle g f v u hg hf (fun x hx ↦ by simpa only [abs_sub_comm] using hbound x hx)⟩

/-- A real lower envelope of concave competitors is concave on their common domain.

See Boyd and Vandenberghe, *Convex Optimization*, §3.2.3, pp. 80–81; p. 81 states that a
pointwise infimum of concave functions is concave:
<https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=95>. The real `IsGLB` hypothesis
makes finiteness of every value explicit.
-/
theorem concaveOn_of_isGLB_image {D : Set ℝ} {F : ℝ → α → ℝ} {value : ℝ → ℝ}
    (hD : Convex ℝ D) (hvalue : ∀ t ∈ D, IsGLB (F t '' s) (value t))
    (hF : ∀ x ∈ s, ConcaveOn ℝ D (fun t ↦ F t x)) : ConcaveOn ℝ D value := by
  refine ⟨hD, ?_⟩
  intro t ht u hu a b ha hb hab
  apply (hvalue _ (hD ht hu ha hb hab)).2
  rintro _ ⟨x, hx, rfl⟩
  simpa only [smul_eq_mul] using (add_le_add
    (mul_le_mul_of_nonneg_left (hvalue t ht |>.1 ⟨x, hx, rfl⟩) ha)
    (mul_le_mul_of_nonneg_left (hvalue u hu |>.1 ⟨x, hx, rfl⟩) hb)).trans
      (by simpa only [smul_eq_mul] using (hF x hx).2 ht hu ha hb hab)

end OTSelector.Analysis.Convex
