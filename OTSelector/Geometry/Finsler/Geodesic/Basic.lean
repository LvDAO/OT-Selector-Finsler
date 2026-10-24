import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Energy.Transition
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic

/-!
## Lemma skeleton

* **Conditions:** A smooth manifold with a continuous reversible Finsler norm; a curve locally solves the nonzero-velocity chartwise Euler–Lagrange equation. Smooth strong convexity is required for regularity and chart covariance consequences.
* **Objects:** Intrinsic predicates IsEulerLagrangeAt and IsEulerLagrangeOn, locality/congruence APIs, smoothness and equations in any genuine chart.
* **Proof detail:** Define the equation by one local chart witness. Use equality of curve germs, inverse charts, covariance and ODE regularity to transfer witnesses and derive smoothness.

## Mathematical sources

* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)*, Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.2, Theorem 2.2 (Picard–Lindelöf) and Lemma 2.3 (regularity), p. 38.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=49
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf

**Relationship to the sources:** Coordinate-free local encoding of the spray/Euler–Lagrange characterization. Unlike the geometric definition in the source, local distance minimality is a later proved property, not part of these predicates.
-/

/-!
# Intrinsic local Euler--Lagrange curves for the original Finsler energy

The predicate below describes the actual curve in genuine atlas coordinates near each
time. Its coordinate velocity is nonzero and its momentum obeys the Euler--Lagrange
equation. Covariance makes the property independent of the witnessing chart. This is
a local differential equation property; global distance minimization is not part of it.
-/

open Set Filter Manifold
open scoped Topology ContDiff

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem eulerLagrange_of_eventuallyEq {L : E × E → ℝ}
    {x y : ℝ → E} {t : ℝ} (heq : x =ᶠ[𝓝 t] y)
    (hEL : HasDerivAt (fun s ↦ fiberLegendre L (x s, deriv x s))
      (baseEnergyDifferential L (x t, deriv x t)) t) :
    HasDerivAt (fun s ↦ fiberLegendre L (y s, deriv y s))
      (baseEnergyDifferential L (y t, deriv y t)) t := by
  have hp : (fun s ↦ (y s, deriv y s)) =ᶠ[𝓝 t] (fun s ↦ (x s, deriv x s)) := by
    filter_upwards [heq.symm, heq.symm.deriv] with s hs hds
    exact Prod.ext hs hds
  rw [hp.eq_of_nhds]
  exact hEL.congr_of_eventuallyEq (hp.fun_comp (fiberLegendre L))

namespace ContinuousFinslerNorm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable {F : ContinuousFinslerNorm E M} {c d : ℝ → M} {I J : Set ℝ} {t : ℝ}

theorem IsEulerLagrangeAt.eventually (hc : F.IsEulerLagrangeAt c t) :
    ∀ᶠ s in 𝓝 t, F.IsEulerLagrangeAt c s := by
  obtain ⟨old, U, hU, ht, hmap, hx, hphase, hEL⟩ := hc
  filter_upwards [hU.mem_nhds ht] with s hs
  exact ⟨old, U, hU, hs, hmap, hx, hphase, hEL⟩

theorem IsEulerLagrangeAt.congr (hc : F.IsEulerLagrangeAt c t)
    (heq : c =ᶠ[𝓝 t] d) : F.IsEulerLagrangeAt d t := by
  obtain ⟨old, U, hU, ht, hmap, hx, hphase, hEL⟩ := hc
  obtain ⟨V, hVsub, hV, htV⟩ := mem_nhds_iff.mp heq
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have hcoord : EqOn (extChartAt 𝓘(ℝ, E) old ∘ c)
      (extChartAt 𝓘(ℝ, E) old ∘ d) W := fun s hs ↦
    congrArg (extChartAt 𝓘(ℝ, E) old) (hVsub hs.2)
  refine ⟨old, W, hW, ⟨ht, htV⟩, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [← hVsub hs.2]
    exact hmap hs.1
  · exact (hx.mono inter_subset_left).congr (fun s hs ↦ (hcoord hs).symm)
  · intro s hs
    rw [← hcoord hs, ← hcoord.deriv hW hs]
    exact hphase s hs.1
  · intro s hs
    exact eulerLagrange_of_eventuallyEq
      (hcoord.eventuallyEq_of_mem (hW.mem_nhds hs)) (hEL s hs.1)

theorem isEulerLagrangeAt_congr (heq : c =ᶠ[𝓝 t] d) :
    F.IsEulerLagrangeAt c t ↔ F.IsEulerLagrangeAt d t :=
  ⟨fun h ↦ h.congr heq, fun h ↦ h.congr heq.symm⟩

theorem IsEulerLagrangeOn.mono (hc : F.IsEulerLagrangeOn c I) (hJI : J ⊆ I) :
    F.IsEulerLagrangeOn c J := fun t ht ↦ hc t (hJI ht)

theorem IsEulerLagrangeOn.congr (hc : F.IsEulerLagrangeOn c I)
    (hI : IsOpen I) (heq : EqOn c d I) : F.IsEulerLagrangeOn d I :=
  fun t ht ↦ (hc t ht).congr (heq.eventuallyEq_of_mem (hI.mem_nhds ht))

theorem isOpen_setOf_isEulerLagrangeAt (F : ContinuousFinslerNorm E M) (c : ℝ → M) :
    IsOpen {t | F.IsEulerLagrangeAt c t} :=
  isOpen_iff_mem_nhds.mpr (fun _ ht ↦ ht.eventually)

/-- A genuine C2 coordinate solution defines the intrinsic local equation on its
open time domain. No smoothness bootstrap is needed for this construction. -/
theorem isEulerLagrangeOn_chart_symm (F : ContinuousFinslerNorm E M) (old : M)
    {x : ℝ → E} (hI : IsOpen I) (hx : ContDiffOn ℝ 2 x I)
    (hphase : ∀ s ∈ I, (x s, deriv x s) ∈ chartEnergyDomain old)
    (hEL : ∀ s ∈ I, HasDerivAt
      (fun r ↦ fiberLegendre (F.chartEnergy old) (x r, deriv x r))
      (baseEnergyDifferential (F.chartEnergy old) (x s, deriv x s)) s) :
    F.IsEulerLagrangeOn ((extChartAt 𝓘(ℝ, E) old).symm ∘ x) I := by
  let c := (extChartAt 𝓘(ℝ, E) old).symm ∘ x
  have heq : EqOn (extChartAt 𝓘(ℝ, E) old ∘ c) x I := by
    intro s hs
    exact (extChartAt 𝓘(ℝ, E) old).right_inv (hphase s hs).1
  intro t ht
  refine ⟨old, I, hI, ht, ?_, hx.congr heq, ?_, ?_⟩
  · intro s hs
    exact (extChartAt 𝓘(ℝ, E) old).map_target (hphase s hs).1
  · intro s hs
    rw [heq hs, heq.deriv hI hs]
    exact hphase s hs
  · intro s hs
    exact eulerLagrange_of_eventuallyEq
      (heq.symm.eventuallyEq_of_mem (hI.mem_nhds hs)) (hEL s hs)

namespace IsSmoothStronglyConvex

variable [FiniteDimensional ℝ E]

/-- The local actual C2 equation automatically makes the manifold curve smooth. -/
theorem contMDiffAt_of_isEulerLagrangeAt (hF : F.IsSmoothStronglyConvex)
    (hc : F.IsEulerLagrangeAt c t) : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c t := by
  obtain ⟨old, U, hU, ht, hmap, hx, hphase, hEL⟩ := hc
  have hxSmooth := hF.contDiffOn_chartEulerLagrange_of_contDiffOn_two old
    hU hx hphase hEL
  have hcSmooth := (contMDiffOn_extChartAt_symm old).comp hxSmooth.contMDiffOn
    (fun s hs ↦ (hphase s hs).1)
  have heq : EqOn c ((extChartAt 𝓘(ℝ, E) old).symm ∘
      (extChartAt 𝓘(ℝ, E) old ∘ c)) U := by
    intro s hs
    exact ((extChartAt 𝓘(ℝ, E) old).left_inv (hmap hs)).symm
  exact (hcSmooth.congr heq).contMDiffAt (hU.mem_nhds ht)

theorem contMDiffOn_of_isEulerLagrangeOn (hF : F.IsSmoothStronglyConvex)
    (hc : F.IsEulerLagrangeOn c I) : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c I :=
  fun t ht ↦ (hF.contMDiffAt_of_isEulerLagrangeAt (hc t ht)).contMDiffWithinAt

/-- The intrinsic local equation holds in every chart containing the curve at the
given time, after restricting to an open time neighborhood. -/
theorem exists_chartEulerLagrangeOn_of_isEulerLagrangeAt
    (hF : F.IsSmoothStronglyConvex) (hc : F.IsEulerLagrangeAt c t)
    (new : M) (hnew : c t ∈ (extChartAt 𝓘(ℝ, E) new).source) :
    ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧
      MapsTo c U (extChartAt 𝓘(ℝ, E) new).source ∧
      ContDiffOn ℝ ∞ (extChartAt 𝓘(ℝ, E) new ∘ c) U ∧
      (∀ s ∈ U, ((extChartAt 𝓘(ℝ, E) new ∘ c) s,
        deriv (extChartAt 𝓘(ℝ, E) new ∘ c) s) ∈ chartEnergyDomain new) ∧
      ∀ s ∈ U, HasDerivAt
        (fun r ↦ fiberLegendre (F.chartEnergy new)
          ((extChartAt 𝓘(ℝ, E) new ∘ c) r, deriv (extChartAt 𝓘(ℝ, E) new ∘ c) r))
        (baseEnergyDifferential (F.chartEnergy new)
          ((extChartAt 𝓘(ℝ, E) new ∘ c) s, deriv (extChartAt 𝓘(ℝ, E) new ∘ c) s)) s := by
  obtain ⟨old, U, hU, ht, hmap, hx, hphase, hEL⟩ := hc
  have hcOn : F.IsEulerLagrangeOn c U :=
    fun s hs ↦ ⟨old, U, hU, hs, hmap, hx, hphase, hEL⟩
  have hcSmooth := hF.contMDiffOn_of_isEulerLagrangeOn hcOn
  have hxSmooth := hF.contDiffOn_chartEulerLagrange_of_contDiffOn_two old
    hU hx hphase hEL
  let J := U ∩ c ⁻¹' (extChartAt 𝓘(ℝ, E) new).source
  have hJ : IsOpen J := hcSmooth.continuousOn.isOpen_inter_preimage hU
    (isOpen_extChartAt_source new)
  have htJ : t ∈ J := ⟨ht, hnew⟩
  have hcmap : MapsTo c J (extChartAt 𝓘(ℝ, E) new).source := fun _ hs ↦ hs.2
  let x := extChartAt 𝓘(ℝ, E) old ∘ c
  let y := extChartAt 𝓘(ℝ, E) new ∘ c
  let z := chartTransition new old ∘ x
  have hxmap : MapsTo x J (chartTransitionDomain new old) := by
    intro s hs
    refine ⟨(hphase s hs.1).1, ?_⟩
    change (extChartAt 𝓘(ℝ, E) old).symm
      (extChartAt 𝓘(ℝ, E) old (c s)) ∈ (extChartAt 𝓘(ℝ, E) new).source
    rw [(extChartAt 𝓘(ℝ, E) old).left_inv (hmap hs.1)]
    exact hs.2
  have hslit : ∀ s ∈ J,
      (x s, deriv x s) ∈ chartTransitionDomain new old ×ˢ {w : E | w ≠ 0} :=
    fun s hs ↦ ⟨hxmap hs, (hphase s hs.1).2⟩
  have hzeq : EqOn z y J := by
    intro s hs
    change extChartAt 𝓘(ℝ, E) new
      ((extChartAt 𝓘(ℝ, E) old).symm (extChartAt 𝓘(ℝ, E) old (c s))) = _
    rw [(extChartAt 𝓘(ℝ, E) old).left_inv (hmap hs.1)]
    rfl
  have hzEL := (hF.chartEulerLagrange_iff_chartTransition new old (y := x) hJ
    (hx.mono inter_subset_left) hslit).mp (fun s hs ↦ hEL s hs.1)
  refine ⟨J, hJ, htJ, hcmap,
    contDiffOn_chart_curve new (hcSmooth.mono inter_subset_left) hcmap, ?_, ?_⟩
  · intro s hs
    have hdx : DifferentiableAt ℝ x s :=
      (hxSmooth.contDiffAt (hU.mem_nhds hs.1)).differentiableAt (by simp)
    have hdφ := ((contDiffOn_chartTransition new old).contDiffAt
      ((isOpen_chartTransitionDomain new old).mem_nhds (hxmap hs))).differentiableAt
        (by simp)
    have hzphase : (z s, deriv z s) ∈ chartEnergyDomain new := by
      change ((chartTransition new old ∘ x) s,
        deriv (chartTransition new old ∘ x) s) ∈ chartEnergyDomain new
      rw [(hdφ.hasFDerivAt.comp_hasDerivAt s hdx.hasDerivAt).deriv]
      simpa only [Function.comp_apply] using
        mapsTo_chartTransition_energyDomain new old (hslit s hs)
    rw [hzeq hs, hzeq.deriv hJ hs] at hzphase
    exact hzphase
  · intro s hs
    exact eulerLagrange_of_eventuallyEq
      (hzeq.eventuallyEq_of_mem (hJ.mem_nhds hs)) (hzEL s hs)

/-- On any time set whose image is contained in one chart, the intrinsic local
equation gives smooth actual coordinates, nonzero velocity and the true equation
throughout that set. The input curve need not have one common witnessing chart. -/
theorem chartEulerLagrange_of_isEulerLagrangeOn (hF : F.IsSmoothStronglyConvex)
    (hc : F.IsEulerLagrangeOn c I) (old : M)
    (hmap : MapsTo c I (extChartAt 𝓘(ℝ, E) old).source) :
    ContDiffOn ℝ ∞ (extChartAt 𝓘(ℝ, E) old ∘ c) I ∧
    (∀ s ∈ I, ((extChartAt 𝓘(ℝ, E) old ∘ c) s,
      deriv (extChartAt 𝓘(ℝ, E) old ∘ c) s) ∈ chartEnergyDomain old) ∧
    ∀ s ∈ I, HasDerivAt
      (fun r ↦ fiberLegendre (F.chartEnergy old)
        ((extChartAt 𝓘(ℝ, E) old ∘ c) r, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) r))
      (baseEnergyDifferential (F.chartEnergy old)
        ((extChartAt 𝓘(ℝ, E) old ∘ c) s, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) s)) s := by
  refine ⟨contDiffOn_chart_curve old (hF.contMDiffOn_of_isEulerLagrangeOn hc) hmap,
    ?_, ?_⟩
  · intro s hs
    obtain ⟨U, _, hsU, _, _, hphase, _⟩ :=
      hF.exists_chartEulerLagrangeOn_of_isEulerLagrangeAt (hc s hs) old (hmap hs)
    exact hphase s hsU
  · intro s hs
    obtain ⟨U, _, hsU, _, _, _, hEL⟩ :=
      hF.exists_chartEulerLagrangeOn_of_isEulerLagrangeAt (hc s hs) old (hmap hs)
    exact hEL s hsU

end IsSmoothStronglyConvex
end ContinuousFinslerNorm
end OTSelector.Geometry
