import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.MetricSpace.Thickening

/-!
## Lemma skeleton

* **Conditions:** C3 function on an open set; a segment derivative bound or compact subset.
* **Objects:** The actual quadratic Taylor remainder and a uniform cubic bound.
* **Proof detail:** Apply mean-value/Taylor estimates along the segment; bound derivatives uniformly on a compact neighborhood.

## Mathematical sources

* Jiří Lebl, *Basic Analysis I: Introduction to Real Analysis, Volume I*, Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder).
  https://www.jirka.org/ra/html/sec_taylor.html
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf

**Relationship to the sources:** The Fréchet form and its deliberately nonoptimal constant C are proved locally from the cited Taylor/mean-value principles.
-/

/-!
# Uniform cubic error for the actual quadratic Taylor expansion

Three applications of the real mean value bound give a cubic estimate using the
actual first and second Frechet derivatives. Compactness makes the constants uniform
on compact subsets of an open finite-dimensional C3 domain.
-/

open Set Filter Metric
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

set_option backward.isDefEq.respectTransparency false

private theorem norm_quadratic_remainder_le {g g₁ g₂ g₃ : ℝ → ℝ} {C : ℝ}
    (h₀ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g (g₁ t) t)
    (h₁ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g₁ (g₂ t) t)
    (h₂ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g₂ (g₃ t) t)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖g₃ t‖ ≤ C) :
    ‖g 1 - g 0 - g₁ 0 - (1 / 2 : ℝ) * g₂ 0‖ ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbound 0 (by simp))
  have hb₂ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖g₂ t - g₂ 0‖ ≤ C := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s hs ↦ (h₂ s hs).hasDerivWithinAt)
      (fun s hs ↦ hbound s (Ico_subset_Icc_self hs)) t ht
    exact h.trans (by simpa using mul_le_mul_of_nonneg_left ht.2 hC)
  let r₁ : ℝ → ℝ := fun t ↦ g₁ t - g₁ 0 - t * g₂ 0
  have hd₁ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt r₁ (g₂ t - g₂ 0) t := by
    simpa only [r₁, Pi.sub_apply, id_eq, sub_zero, one_mul] using! ((h₁ t ht).sub_const (g₁ 0)).sub
      ((hasDerivAt_id t).mul_const (g₂ 0))
  have hb₁ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖r₁ t‖ ≤ C := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s hs ↦ (hd₁ s hs).hasDerivWithinAt)
      (fun s hs ↦ hb₂ s (Ico_subset_Icc_self hs)) t ht
    simp only [r₁, zero_mul, sub_self, sub_zero] at h ⊢
    exact h.trans (by simpa using mul_le_mul_of_nonneg_left ht.2 hC)
  let r₀ : ℝ → ℝ := fun t ↦ g t - g 0 - t * g₁ 0 - (1 / 2 : ℝ) * t ^ 2 * g₂ 0
  have hd₀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt r₀ (r₁ t) t := by
    have h := (((h₀ t ht).sub_const (g 0)).sub
      ((hasDerivAt_id t).mul_const (g₁ 0))).sub
      ((((hasDerivAt_id t).pow 2).const_mul (1 / 2 : ℝ)).mul_const (g₂ 0))
    convert h using 1 <;> try dsimp only [r₀, r₁]
    all_goals first | rfl | (simp only [id_eq]; ring)
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun s hs ↦ (hd₀ s hs).hasDerivWithinAt)
    (fun s hs ↦ hb₁ s (Ico_subset_Icc_self hs))
  simpa [r₀] using h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- A bound on the actual third Frechet derivative along one segment controls the
quadratic Taylor remainder by that bound times the cube of the displacement norm. -/
theorem norm_quadratic_taylor_remainder_le {f : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U) {x h : E}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ U) {C : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (x + t • h)‖ ≤ C) :
    ‖f (x + h) - f x - fderiv ℝ f x h -
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) x h h‖ ≤ C * ‖h‖ ^ 3 := by
  have hf₁ : ContDiffOn ℝ 2 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
  have hf₂ : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ f)) U :=
    hf₁.fderiv_of_isOpen hU (by norm_num)
  let γ : ℝ → E := fun t ↦ x + t • h
  have hγ (t : ℝ) : HasDerivAt γ h t := by
    simpa only [γ, Pi.add_apply, id_eq, one_smul, zero_add] using!
      (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const h)
  let g₀ : ℝ → ℝ := fun t ↦ f (γ t)
  let g₁ : ℝ → ℝ := fun t ↦ fderiv ℝ f (γ t) h
  let g₂ : ℝ → ℝ := fun t ↦ fderiv ℝ (fderiv ℝ f) (γ t) h h
  let g₃ : ℝ → ℝ := fun t ↦ fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (γ t) h h h
  have h₀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt g₀ (g₁ t) t :=
    ((hf.contDiffAt (hU.mem_nhds (hseg t ht))).differentiableAt (by norm_num)).hasFDerivAt
      |>.comp_hasDerivAt t (hγ t)
  have h₁ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt g₁ (g₂ t) t := by
    have hd := ((hf₁.contDiffAt (hU.mem_nhds (hseg t ht))).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hγ t)
    simpa only [zero_add, add_zero, ContinuousLinearMap.map_zero] using!
      hd.clm_apply (hasDerivAt_const t h)
  have h₂ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt g₂ (g₃ t) t := by
    have hd := ((hf₂.contDiffAt (hU.mem_nhds (hseg t ht))).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hγ t)
    simpa only [zero_add, add_zero, ContinuousLinearMap.map_zero] using!
      (hd.clm_apply (hasDerivAt_const t h)).clm_apply (hasDerivAt_const t h)
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖g₃ t‖ ≤ C * ‖h‖ ^ 3 := by
    let D := fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (γ t)
    calc
      ‖g₃ t‖ ≤ ‖D h h‖ * ‖h‖ := (D h h).le_opNorm h
      _ ≤ (‖D h‖ * ‖h‖) * ‖h‖ :=
        mul_le_mul_of_nonneg_right ((D h).le_opNorm h) (norm_nonneg _)
      _ ≤ ((‖D‖ * ‖h‖) * ‖h‖) * ‖h‖ := by
        gcongr
        exact D.le_opNorm h
      _ ≤ ((C * ‖h‖) * ‖h‖) * ‖h‖ := by
        gcongr
        exact hbound t ht
      _ = C * ‖h‖ ^ 3 := by ring
  simpa only [g₀, g₁, g₂, γ, zero_smul, one_smul, add_zero] using
    norm_quadratic_remainder_le h₀ h₁ h₂ hb


variable [FiniteDimensional ℝ E]

/-- On a compact subset of an open C3 domain, one radius and one nonnegative constant
control the actual quadratic Taylor remainder at every center. -/
theorem exists_uniform_quadratic_taylor_remainder_bound {f : E → ℝ} {U K : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ r > 0, ∃ C ≥ 0, ∀ x ∈ K, ∀ h : E, ‖h‖ ≤ r →
      ‖f (x + h) - f x - fderiv ℝ f x h -
        (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) x h h‖ ≤ C * ‖h‖ ^ 3 := by
  have hf₁ : ContDiffOn ℝ 2 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
  have hf₂ : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ f)) U :=
    hf₁.fderiv_of_isOpen hU (by norm_num)
  have hD := hf₂.continuousOn_fderiv_of_isOpen hU (by norm_num)
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨η, hη, hηK⟩ := hK.exists_isCompact_cthickening
  let r := min δ η
  have hr : 0 < r := lt_min hδ hη
  have hTU : cthickening r K ⊆ U :=
    (cthickening_mono (min_le_left δ η) K).trans hδU
  have hT : IsCompact (cthickening r K) :=
    hηK.of_isClosed_subset isClosed_cthickening (cthickening_mono (min_le_right δ η) K)
  obtain ⟨B, hB⟩ := hT.exists_bound_of_continuousOn (hD.mono hTU)
  refine ⟨r, hr, max B 0, le_max_right _ _, ?_⟩
  intro x hx h hh
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x + t • h ∈ cthickening r K := by
    apply mem_cthickening_of_dist_le (x + t • h) x r K hx
    calc
      dist (x + t • h) x = ‖t • h‖ := by rw [dist_eq_norm, add_sub_cancel_left]
      _ = t * ‖h‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      _ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
      _ ≤ r := by simpa using hh
  exact norm_quadratic_taylor_remainder_le hU hf (fun t ht ↦ hTU (hseg t ht))
    (fun t ht ↦ (hB _ (hseg t ht)).trans (le_max_left _ _))

/-- Actual C3 regularity at one point supplies a cubic error bound for its quadratic
Taylor expansion on a closed displacement ball. -/
theorem exists_quadratic_taylor_remainder_bound_of_contDiffAt {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 3 f x) :
    ∃ r > 0, ∃ C ≥ 0, ∀ h : E, ‖h‖ ≤ r →
      ‖f (x + h) - f x - fderiv ℝ f x h -
        (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) x h h‖ ≤ C * ‖h‖ ^ 3 := by
  obtain ⟨U, hUf, hU, hx⟩ := _root_.mem_nhds_iff.mp (hf.eventually (by norm_num))
  have hfU : ContDiffOn ℝ 3 f U := fun y hy ↦
    (show ContDiffAt ℝ 3 f y from hUf hy).contDiffWithinAt
  obtain ⟨r, hr, C, hC, hbound⟩ := exists_uniform_quadratic_taylor_remainder_bound
    hU hfU isCompact_singleton (singleton_subset_iff.mpr hx)
  exact ⟨r, hr, C, hC, hbound x (mem_singleton x)⟩

end OTSelector.Geometry
