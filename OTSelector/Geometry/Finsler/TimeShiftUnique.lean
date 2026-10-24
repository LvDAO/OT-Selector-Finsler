import OTSelector.Geometry.Finsler.AffineTime
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Uniqueness

/-!
# Geometry.Finsler.TimeShiftUnique

* **Conditions:** Two actual Euler–Lagrange trajectories defined for all real times attain the same tangent state at possibly different times.
* **Objects:** Exact equality after the corresponding translation of time.
* **Proof detail:** Translate one actual curve by a slope-one affine clock, compute its tangent and apply intrinsic initial-value uniqueness.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): Metric completeness, calibration and unit speed are not hypotheses of this same-state uniqueness lemma.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerTimeShiftUnique.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerTimeShiftUnique`; the selected original proof blocks follow. -/
section

/-!
# Complete Finsler trajectories determined by one tangent state

Two complete solutions of the original energy Euler--Lagrange equation that attain the same
actual tangent state at different times agree after the corresponding translation of time.
The proof translates the second curve by a positive affine map of slope one, computes its
actual tangent by the manifold chain rule, and applies complete-trajectory uniqueness.

Completeness here means that both curves solve the equation for every real time. Metric
completeness, calibration, minimizing behavior, and unit speed are not hypotheses.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] {F : ContinuousFinslerNorm E M}

/-- Complete original energy trajectories with the same tangent state agree after time shift. -/
theorem eq_timeShift_of_complete_tangent_eq (hF : F.IsSmoothStronglyConvex)
    {c d : ℝ → M} {s t : ℝ}
    (hc : F.IsEulerLagrangeOn c univ) (hd : F.IsEulerLagrangeOn d univ)
    (hv : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨s, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t, (1 : ℝ)⟩) :
    c = fun r ↦ d (r - s + t) := by
  let k : ℝ → M := fun r ↦ d (r - s + t)
  have hk : F.IsEulerLagrangeOn k univ := by
    have hfun : k = d ∘ (fun r ↦ (1 : ℝ) * (r - (s - t))) := by
      funext r
      dsimp [k]
      congr 1
      ring
    rw [hfun]
    simpa only [preimage_univ] using
      hF.isEulerLagrangeOn_affine hd (s := 1) (a := s - t) zero_lt_one
  have ht : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d (s - s + t) := by
    simpa only [sub_self, zero_add] using
      (hF.contMDiffAt_of_isEulerLagrangeAt (hd t (mem_univ _))).mdifferentiableAt
        (by simp)
  have hshift : HasDerivAt (fun r : ℝ ↦ r - s + t) 1 s := by
    simpa using ((hasDerivAt_id s).sub_const s).add_const t
  have htan : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) k ⟨s, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t, (1 : ℝ)⟩ := by
    change tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (d ∘ (fun r ↦ r - s + t))
      ⟨s, (1 : ℝ)⟩ = _
    rw [tangentMap_comp_at ⟨s, (1 : ℝ)⟩ ht hshift.differentiableAt.mdifferentiableAt]
    have hscalar : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r ↦ r - s + t)
        ⟨s, (1 : ℝ)⟩ = ⟨t, (1 : ℝ)⟩ := by
      simp only [tangentMap, mfderiv_eq_fderiv]
      congr 1
      · simp
      · exact (fderiv_apply_one_eq_deriv (𝕜 := ℝ)).trans hshift.deriv
    rw [hscalar]
  funext r
  exact hF.eqOn_of_isEulerLagrangeOn isOpen_univ isPreconnected_univ hc hk
    (mem_univ s) (hv.trans htan.symm) (mem_univ r)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
