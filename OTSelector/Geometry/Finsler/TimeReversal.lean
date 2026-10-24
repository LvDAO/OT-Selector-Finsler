import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.AffineTime
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Hamiltonian.Basic

/-!
# Geometry.Finsler.TimeReversal

* **Conditions:** The original reversible Finsler norm and actual Euler–Lagrange dynamics on the reflected time domain.
* **Objects:** Sign reversal of actual tangent/momentum, preserved speed/smoothness and the original equation after t↦a−t.
* **Proof detail:** Use even energy, odd momentum, even base force and the two cancelling derivative signs in the chain rule.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.

Source relation (derived): Reversibility belongs to the actual formal norm; these conclusions are not asserted for arbitrary irreversible Finsler metrics.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerTimeReversal.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerTimeReversal`; the selected original proof blocks follow. -/
section

/-!
# Time reversal of the original reversible Finsler energy dynamics

The original fiber energy is even in velocity. Its actual chart momentum is odd and its base
force is even, so the two signs in the time-reversed Euler--Lagrange equation cancel. Thus
`fun t ↦ c (a - t)` solves the same original equation on the reflected time domain. The actual
tangent vector reverses sign, while smoothness and the original Finsler speed are preserved.
These are local differential identities; no transformed geodesic equation is assumed.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem timeReverse_hasDerivAt (a t : ℝ) :
    HasDerivAt (fun r ↦ a - r) (-1) t := by
  simpa using (hasDerivAt_id t).const_sub a

private theorem timeReverse_contDiff (a : ℝ) :
    ContDiff ℝ ∞ (fun r ↦ a - r) :=
  contDiff_const.sub contDiff_id

/-- The original reversible Finsler fiber energy is even in the actual tangent velocity. -/
theorem fiberEnergy_neg (F : ContinuousFinslerNorm E M) (x : M)
    (v : TangentSpace 𝓘(ℝ, E) x) : F.fiberEnergy x (-v) = F.fiberEnergy x v := by
  simpa using F.fiberEnergy_smul x (-1) v

/-- Evenness survives the original tangent-bundle coordinate change. -/
theorem chartEnergy_neg (F : ContinuousFinslerNorm E M) (old : M)
    {x : E} (hx : x ∈ (extChartAt 𝓘(ℝ, E) old).target) (v : E) :
    F.chartEnergy old (x, -v) = F.chartEnergy old (x, v) := by
  simpa using F.chartEnergy_smul old hx (-1) v

/-- The actual chart momentum is odd, including the derivative convention at zero velocity. -/
theorem chartLegendre_neg (F : ContinuousFinslerNorm E M) (old : M)
    {x : E} (hx : x ∈ (extChartAt 𝓘(ℝ, E) old).target) (v : E) :
    fiberLegendre (F.chartEnergy old) (x, -v) =
      -fiberLegendre (F.chartEnergy old) (x, v) := by
  let L : E → ℝ := fun w ↦ F.chartEnergy old (x, w)
  have heq : L ∘ (ContinuousLinearEquiv.neg ℝ : E ≃L[ℝ] E) = L :=
    funext (F.chartEnergy_neg old hx)
  have hd := (ContinuousLinearEquiv.neg ℝ : E ≃L[ℝ] E).comp_right_fderiv
    (f := L) (x := v)
  rw [heq] at hd
  change fderiv ℝ L (-v) = -fderiv ℝ L v
  ext w
  have hw := congrArg (fun p : E →L[ℝ] ℝ ↦ p w) hd
  change (fderiv ℝ L v) w = (fderiv ℝ L (-v)) (-w) at hw
  rw [map_neg] at hw
  simpa using (neg_eq_iff_eq_neg.mpr hw).symm

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The actual tangent vector of the reflected curve is the negative original tangent vector. -/
theorem tangentMap_timeReverse {c : ℝ → M} {a t : ℝ}
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (a - t)) :
    tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r ↦ c (a - r)) ⟨t, (1 : ℝ)⟩ =
      ⟨c (a - t), -mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (a - t) 1⟩ := by
  have hd := timeReverse_hasDerivAt a t
  change tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (c ∘ (fun r ↦ a - r)) ⟨t, (1 : ℝ)⟩ = _
  rw [tangentMap_comp_at ⟨t, (1 : ℝ)⟩ hc hd.differentiableAt.mdifferentiableAt]
  have ht : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r ↦ a - r)
      ⟨t, (1 : ℝ)⟩ = ⟨a - t, (-1 : ℝ)⟩ := by
    simp only [tangentMap, mfderiv_eq_fderiv]
    congr 1
    exact (fderiv_apply_one_eq_deriv (𝕜 := ℝ)).trans hd.deriv
  rw [ht]
  simp only [tangentMap, map_neg]

/-- Reflection preserves the original Finsler speed at the corresponding time. -/
theorem speed_timeReverse (F : ContinuousFinslerNorm E M) {c : ℝ → M} {a t : ℝ}
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (a - t)) :
    F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r ↦ c (a - r)) ⟨t, (1 : ℝ)⟩) =
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨a - t, (1 : ℝ)⟩) := by
  rw [tangentMap_timeReverse hc]
  simpa [tangentMap] using F.map_smul (c (a - t)) (-1)
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (a - t) 1)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- An actual smooth manifold curve remains smooth after time reflection. -/
theorem contMDiff_timeReverse {c : ℝ → M}
    (hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c) (a : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t ↦ c (a - t)) :=
  hc.comp (timeReverse_contDiff a).contMDiff

/-- Every original unit-speed differentiable curve remains unit speed after reflection. -/
theorem unitSpeed_timeReverse (F : ContinuousFinslerNorm E M) {c : ℝ → M}
    (hc : MDifferentiable 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c)
    (hspeed : ∀ t, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1)
    (a : ℝ) :
    ∀ t, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r ↦ c (a - r))
      ⟨t, (1 : ℝ)⟩) = 1 := by
  intro t
  rw [F.speed_timeReverse (hc (a - t)), hspeed]

namespace IsSmoothStronglyConvex
variable {F : ContinuousFinslerNorm E M}

private theorem chartEnergy_eulerLagrange_timeReverse
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {x : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hx : ContDiffOn ℝ 2 x I)
    (hphase : ∀ t ∈ I, (x t, deriv x t) ∈ chartEnergyDomain old)
    (hEL : ∀ t ∈ I, HasDerivAt
      (fun r ↦ fiberLegendre (F.chartEnergy old) (x r, deriv x r))
      (baseEnergyDifferential (F.chartEnergy old) (x t, deriv x t)) t)
    {a t : ℝ} (ht : a - t ∈ I) :
    HasDerivAt
      (fun r ↦ fiberLegendre (F.chartEnergy old)
        (x (a - r), deriv (fun v ↦ x (a - v)) r))
      (baseEnergyDifferential (F.chartEnergy old)
        (x (a - t), deriv (fun v ↦ x (a - v)) t)) t := by
  have hd (r : ℝ) (hr : a - r ∈ I) :
      deriv (fun v ↦ x (a - v)) r = -deriv x (a - r) := by
    simpa only [Function.comp_def, neg_one_smul] using
      (((hx.contDiffAt (hI.mem_nhds hr)).differentiableAt
        (by norm_num)).hasDerivAt.scomp r (timeReverse_hasDerivAt a r)).deriv
  have hforce : baseEnergyDifferential (F.chartEnergy old)
      (x (a - t), deriv (fun v ↦ x (a - v)) t) =
      baseEnergyDifferential (F.chartEnergy old) (x (a - t), deriv x (a - t)) := by
    rw [hd t ht]
    simpa using hF.chartBaseEnergy_smul old (hphase _ ht) (-1)
  rw [hforce]
  have h := ((hEL _ ht).scomp t (timeReverse_hasDerivAt a t)).neg
  simp only [neg_one_smul, neg_neg] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [((timeReverse_contDiff a).continuous.continuousAt.preimage_mem_nhds
    (hI.mem_nhds ht))] with r hr
  rw [hd r hr]
  exact F.chartLegendre_neg old (hphase _ hr).1 _

/-- Reflection preserves the original intrinsic Euler--Lagrange equation at each time. -/
theorem isEulerLagrangeAt_timeReverse (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {a t : ℝ} (hc : F.IsEulerLagrangeAt c (a - t)) :
    F.IsEulerLagrangeAt (fun r ↦ c (a - r)) t := by
  obtain ⟨old, I, hI, ht, hmap, hx, hphase, hEL⟩ := hc
  let τ : ℝ → ℝ := fun r ↦ a - r
  let J := τ ⁻¹' I
  have hτ : ContDiff ℝ ∞ τ := timeReverse_contDiff a
  have hJ : IsOpen J := hI.preimage hτ.continuous
  have hd (r : ℝ) (hr : r ∈ J) :
      deriv ((extChartAt 𝓘(ℝ, E) old ∘ c) ∘ τ) r =
        -deriv (extChartAt 𝓘(ℝ, E) old ∘ c) (τ r) := by
    simpa only [Function.comp_def, neg_one_smul] using
      (((hx.contDiffAt (hI.mem_nhds hr)).differentiableAt
        (by norm_num)).hasDerivAt.scomp r (timeReverse_hasDerivAt a r)).deriv
  refine ⟨old, J, hJ, ht, (fun r hr ↦ hmap hr),
    hx.comp (hτ.of_le (by simp)).contDiffOn (fun _ hr ↦ hr), ?_, ?_⟩
  · intro r hr
    change (((extChartAt 𝓘(ℝ, E) old ∘ c) ∘ τ) r,
      deriv ((extChartAt 𝓘(ℝ, E) old ∘ c) ∘ τ) r) ∈ chartEnergyDomain old
    rw [hd r hr]
    exact ⟨(hphase _ hr).1, neg_ne_zero.mpr (hphase _ hr).2⟩
  · intro r hr
    exact hF.chartEnergy_eulerLagrange_timeReverse old hI hx hphase hEL hr

/-- The same original energy equation holds throughout the reflected time domain. -/
theorem isEulerLagrangeOn_timeReverse (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {I : Set ℝ} (hc : F.IsEulerLagrangeOn c I) (a : ℝ) :
    F.IsEulerLagrangeOn (fun r ↦ c (a - r)) ((fun r ↦ a - r) ⁻¹' I) :=
  fun _ ht ↦ hF.isEulerLagrangeAt_timeReverse (hc _ ht)

/-- Complete original energy trajectories remain complete original trajectories after reflection. -/
theorem isEulerLagrangeOn_timeReverse_univ (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} (hc : F.IsEulerLagrangeOn c univ) (a : ℝ) :
    F.IsEulerLagrangeOn (fun r ↦ c (a - r)) univ := by
  simpa only [preimage_univ] using hF.isEulerLagrangeOn_timeReverse hc a

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
