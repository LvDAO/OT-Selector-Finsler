import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
/-
Copyright 2026 The DifferentialGeometry contributors.
Released under Apache 2.0 license as described in the upstream LICENSE file.

Adapted from qinz1yang/differential-geometry, commit
fd2f07fba4c6c102ba626c59153ad98da8f0d442:
DifferentialGeometry/Analysis/ODE/Flow/LinearODE/Variational.lean
https://github.com/qinz1yang/differential-geometry

Local modifications: project-local imports and namespace; compatibility with the
project's pinned Lean/mathlib; removal of declarations outside the required closure
where noted below. Original mathematical hypotheses and proofs are preserved.
-/

/-!
## Lemma skeleton

* **Conditions:** A time-dependent field differentiable in state along a chosen central curve.
* **Objects:** The linear variational equation y′=Dxf(t,α(t))y with initial increment.
* **Proof detail:** Package the linear equation, read off continuity and initial data, derive continuous coefficients and close its solutions under linear combinations.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.4, equations (2.46)–(2.50) and Theorem 2.10, pp. 45–47.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf

**Relationship to the sources:** This module defines the variational-solution interface and elementary consequences. It does not assume that a flow derivative already exists.
-/

/-!
# Linear variational equations along a curve

The variational equation is defined using the actual state derivative of a time-dependent
vector field. This module supplies derivative continuity and linearity of its solutions.
Only the independent upstream open-interval existence/uniqueness branch is omitted;
the closed-interval existence and solution operator are provided in the next modules.
-/

noncomputable section

open Set Function Filter Metric
open scoped Topology NNReal

namespace OTSelector.Geometry.LocalFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def IsVariationalSolutionOn
    (f : ℝ → E → E) (α : ℝ → E) (δ : E) (t₀ : ℝ) (y : ℝ → E) (s : Set ℝ) : Prop :=
  y t₀ = δ ∧
    ∀ t ∈ s, HasDerivWithinAt y ((fderiv ℝ (f t) (α t)) (y t)) s t

def IsVariationalSolution
    (f : ℝ → E → E) (α : ℝ → E) (δ : E) (t₀ : ℝ) (y : ℝ → E) : Prop :=
  y t₀ = δ ∧
    ∀ t : ℝ, HasDerivAt y ((fderiv ℝ (f t) (α t)) (y t)) t

namespace IsVariationalSolutionOn

variable {f : ℝ → E → E} {α : ℝ → E} {δ : E} {t₀ : ℝ} {y : ℝ → E} {s : Set ℝ}

lemma initial (hy : IsVariationalSolutionOn f α δ t₀ y s) : y t₀ = δ := hy.1

lemma hasDerivWithinAt (hy : IsVariationalSolutionOn f α δ t₀ y s) :
    ∀ t ∈ s, HasDerivWithinAt y ((fderiv ℝ (f t) (α t)) (y t)) s t := hy.2

lemma mono {s' : Set ℝ} (hy : IsVariationalSolutionOn f α δ t₀ y s) (hs : s' ⊆ s) :
    IsVariationalSolutionOn f α δ t₀ y s' :=
  ⟨hy.1, fun t ht => (hy.2 t (hs ht)).mono hs⟩

lemma continuousOn (hy : IsVariationalSolutionOn f α δ t₀ y s) : ContinuousOn y s :=
  fun t ht => (hy.2 t ht).continuousWithinAt

lemma hasDerivAt_of_isOpen (hy : IsVariationalSolutionOn f α δ t₀ y s) (hs : IsOpen s)
    {t : ℝ} (ht : t ∈ s) :
    HasDerivAt y ((fderiv ℝ (f t) (α t)) (y t)) t :=
  (hy.2 t ht).hasDerivAt (hs.mem_nhds ht)

end IsVariationalSolutionOn

namespace IsVariationalSolution

variable {f : ℝ → E → E} {α : ℝ → E} {δ : E} {t₀ : ℝ} {y : ℝ → E}

lemma initial (hy : IsVariationalSolution f α δ t₀ y) : y t₀ = δ := hy.1

lemma hasDerivAt (hy : IsVariationalSolution f α δ t₀ y) :
    ∀ t : ℝ, HasDerivAt y ((fderiv ℝ (f t) (α t)) (y t)) t := hy.2

lemma toIsVariationalSolutionOn (hy : IsVariationalSolution f α δ t₀ y) (s : Set ℝ) :
    IsVariationalSolutionOn f α δ t₀ y s :=
  ⟨hy.1, fun t _ => (hy.2 t).hasDerivWithinAt⟩

lemma continuous (hy : IsVariationalSolution f α δ t₀ y) : Continuous y :=
  continuous_iff_continuousAt.mpr (fun t => (hy.2 t).continuousAt)

end IsVariationalSolution

section Linearization

variable {f : ℝ → E → E} {α : ℝ → E} {s : Set ℝ} {u : Set E}

lemma fderiv_eq_comp_inr {f : ℝ → E → E} {p : ℝ × E}
    (hdiff_joint : DifferentiableAt ℝ (uncurry f) p) :
    fderiv ℝ (f p.1) p.2
      = (fderiv ℝ (uncurry f) p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  have hfd_joint : HasFDerivAt (uncurry f) (fderiv ℝ (uncurry f) p) p :=
    hdiff_joint.hasFDerivAt
  have hg : HasFDerivAt (fun y : E => ((p.1 : ℝ), y))
      (ContinuousLinearMap.inr ℝ ℝ E) p.2 := by
    have h1 : HasFDerivAt (fun _ : E => (p.1 : ℝ)) (0 : E →L[ℝ] ℝ) p.2 :=
      hasFDerivAt_const _ _
    have h2 : HasFDerivAt (fun y : E => y) (ContinuousLinearMap.id ℝ E) p.2 :=
      hasFDerivAt_id _
    have h3 := h1.prodMk h2
    have : (0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)
        = ContinuousLinearMap.inr ℝ ℝ E := by
      ext y <;> simp
    rw [this] at h3
    exact h3
  have hp_eq : ((p.1 : ℝ), p.2) = p := by ext <;> rfl
  have hfd_joint' :
      HasFDerivAt (uncurry f) (fderiv ℝ (uncurry f) p)
        ((fun y : E => ((p.1 : ℝ), y)) p.2) := by
    change HasFDerivAt (uncurry f) (fderiv ℝ (uncurry f) p) ((p.1, p.2))
    rw [hp_eq]
    exact hfd_joint
  have hcomp_raw :
      HasFDerivAt ((uncurry f) ∘ (fun y : E => ((p.1 : ℝ), y)))
        ((fderiv ℝ (uncurry f) p).comp (ContinuousLinearMap.inr ℝ ℝ E)) p.2 :=
    HasFDerivAt.comp p.2 hfd_joint' hg
  have huncurry_eq : (uncurry f) ∘ (fun y : E => ((p.1 : ℝ), y)) = f p.1 := by
    funext y; rfl
  rw [huncurry_eq] at hcomp_raw
  exact hcomp_raw.fderiv

lemma continuousOn_partialFDeriv_uncurry
    (hf : ContDiffOn ℝ 1 (uncurry f) (s ×ˢ u)) (hs : IsOpen s) (hu : IsOpen u) :
    ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) (s ×ˢ u) := by
  have hprod_open : IsOpen (s ×ˢ u) := hs.prod hu
  have hf_full :
      ContinuousOn (fun p : ℝ × E => fderiv ℝ (uncurry f) p) (s ×ˢ u) :=
    hf.continuousOn_fderiv_of_isOpen hprod_open le_rfl
  have hpartial_eq :
      EqOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
        (fun p : ℝ × E =>
          (fderiv ℝ (uncurry f) p).comp (ContinuousLinearMap.inr ℝ ℝ E))
        (s ×ˢ u) := by
      intro p hp
      have hp_open : (s ×ˢ u) ∈ 𝓝 p := hprod_open.mem_nhds hp
      have hdiff_joint : DifferentiableAt ℝ (uncurry f) p :=
        ((hf.contDiffAt hp_open).differentiableAt one_ne_zero)
      exact fderiv_eq_comp_inr hdiff_joint
  have hcomp_cont :
      ContinuousOn (fun p : ℝ × E =>
        (fderiv ℝ (uncurry f) p).comp (ContinuousLinearMap.inr ℝ ℝ E)) (s ×ˢ u) := by
    have hpostL : Continuous
        (fun M : (ℝ × E) →L[ℝ] E => M.comp (ContinuousLinearMap.inr ℝ ℝ E)) := by
      exact Continuous.clm_comp_const continuous_id (ContinuousLinearMap.inr ℝ ℝ E)
    exact hpostL.comp_continuousOn hf_full
  exact hcomp_cont.congr hpartial_eq

lemma continuousOn_fderiv_along_curve
    (hf : ContDiffOn ℝ 1 (uncurry f) (s ×ˢ u)) (hs : IsOpen s) (hu : IsOpen u)
    (hα : ContinuousOn α s) (hmem : ∀ t ∈ s, α t ∈ u) :
    ContinuousOn (fun t => fderiv ℝ (f t) (α t)) s := by
  have hpartial := continuousOn_partialFDeriv_uncurry hf hs hu
  have hcont_curve : ContinuousOn (fun t : ℝ => (t, α t)) s :=
    continuousOn_id.prodMk hα
  have hmaps : MapsTo (fun t : ℝ => (t, α t)) s (s ×ˢ u) := fun t ht => ⟨ht, hmem t ht⟩
  exact hpartial.comp hcont_curve hmaps

lemma exists_bound_fderiv_along_curve_Icc {tmin tmax : ℝ}
    (hf : ContDiffOn ℝ 1 (uncurry f) (s ×ˢ u)) (hs : IsOpen s) (hu : IsOpen u)
    (hα : ContinuousOn α s) (hmem : ∀ t ∈ s, α t ∈ u)
    (hsub : Icc tmin tmax ⊆ s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc tmin tmax, ‖fderiv ℝ (f t) (α t)‖ ≤ M := by
  rcases le_or_gt tmin tmax with hle | hlt
  · have hcont : ContinuousOn (fun t => fderiv ℝ (f t) (α t)) s :=
      continuousOn_fderiv_along_curve hf hs hu hα hmem
    have hcont' : ContinuousOn (fun t => fderiv ℝ (f t) (α t)) (Icc tmin tmax) :=
      hcont.mono hsub
    have hcont_norm : ContinuousOn (fun t => ‖fderiv ℝ (f t) (α t)‖) (Icc tmin tmax) :=
      continuous_norm.comp_continuousOn hcont'
    have hcpt : IsCompact (Icc tmin tmax) := isCompact_Icc
    have hne : (Icc tmin tmax).Nonempty := ⟨tmin, left_mem_Icc.mpr hle⟩
    rcases hcpt.exists_isMaxOn hne hcont_norm with ⟨t₁, _, ht₁_max⟩
    exact ⟨‖fderiv ℝ (f t₁) (α t₁)‖, norm_nonneg _, fun t ht => ht₁_max ht⟩
  · refine ⟨0, le_rfl, fun t ht => ?_⟩
    exact absurd (lt_of_le_of_lt ht.1 (lt_of_le_of_lt ht.2 hlt)) (lt_irrefl _)

end Linearization

/- The upstream independent open-interval uniqueness/existence branch is omitted;
the required closed-interval variational construction is in VariationalSolutionOperator. -/

section Linearity

variable {f : ℝ → E → E} {α : ℝ → E} {t₀ : ℝ}

theorem IsVariationalSolutionOn.linear_combination
    {δ₁ δ₂ : E} {c₁ c₂ : ℝ} {y₁ y₂ : ℝ → E} {s : Set ℝ}
    (h₁ : IsVariationalSolutionOn f α δ₁ t₀ y₁ s)
    (h₂ : IsVariationalSolutionOn f α δ₂ t₀ y₂ s) :
    IsVariationalSolutionOn f α (c₁ • δ₁ + c₂ • δ₂) t₀
      (fun t => c₁ • y₁ t + c₂ • y₂ t) s := by
  refine ⟨?_, ?_⟩
  · simp [h₁.1, h₂.1]
  · intro t ht
    have hd₁ := h₁.2 t ht
    have hd₂ := h₂.2 t ht
    have hd_sum : HasDerivWithinAt (fun t => c₁ • y₁ t + c₂ • y₂ t)
        (c₁ • ((fderiv ℝ (f t) (α t)) (y₁ t)) + c₂ • ((fderiv ℝ (f t) (α t)) (y₂ t))) s t :=
      (hd₁.const_smul c₁).add (hd₂.const_smul c₂)
    have hlin :
        (fderiv ℝ (f t) (α t)) (c₁ • y₁ t + c₂ • y₂ t)
          = c₁ • ((fderiv ℝ (f t) (α t)) (y₁ t))
              + c₂ • ((fderiv ℝ (f t) (α t)) (y₂ t)) := by
      simp [map_add]
    rw [hlin]
    exact hd_sum

theorem IsVariationalSolutionOn.const_smul
    {δ : E} {c : ℝ} {y : ℝ → E} {s : Set ℝ}
    (h : IsVariationalSolutionOn f α δ t₀ y s) :
    IsVariationalSolutionOn f α (c • δ) t₀ (fun t => c • y t) s := by
  have h₂ : IsVariationalSolutionOn f α (0 : E) t₀ (fun _ => (0 : E)) s := by
    refine ⟨by simp, ?_⟩
    intro t _
    have hz : ((fderiv ℝ (f t) (α t)) (0 : E)) = 0 := by simp
    rw [hz]
    exact hasDerivWithinAt_const t s (0 : E)
  have hcomb := h.linear_combination (c₁ := c) (c₂ := 0) h₂
  simpa using hcomb

theorem IsVariationalSolutionOn.add
    {δ₁ δ₂ : E} {y₁ y₂ : ℝ → E} {s : Set ℝ}
    (h₁ : IsVariationalSolutionOn f α δ₁ t₀ y₁ s)
    (h₂ : IsVariationalSolutionOn f α δ₂ t₀ y₂ s) :
    IsVariationalSolutionOn f α (δ₁ + δ₂) t₀ (fun t => y₁ t + y₂ t) s := by
  have hcomb := h₁.linear_combination (c₁ := 1) (c₂ := 1) h₂
  simpa using hcomb

theorem IsVariationalSolutionOn.zero
    {s : Set ℝ} :
    IsVariationalSolutionOn f α (0 : E) t₀ (fun _ => (0 : E)) s := by
  refine ⟨by simp, ?_⟩
  intro t _
  have hz : ((fderiv ℝ (f t) (α t)) (0 : E)) = 0 := by simp
  rw [hz]
  exact hasDerivWithinAt_const t s (0 : E)

end Linearity

end OTSelector.Geometry.LocalFlow

end
