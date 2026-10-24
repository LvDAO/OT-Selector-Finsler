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
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic

/-!
## Lemma skeleton

* **Conditions:** A smooth strongly convex Finsler structure in finite dimension, two intrinsic solutions with equal actual tangent at one time; an open preconnected time domain and Hausdorff manifold for interval-wide equality.
* **Objects:** Equality of solution germs, continuity and equality of actual tangent lifts, and equality of manifold curves.
* **Proof detail:** Use the true phase ODE in local charts to obtain local uniqueness. The tangent-equality set is closed by continuity and open by germ uniqueness, hence fills the connected time set.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.2, Theorem 2.2 (Picard–Lindelöf) and Lemma 2.3 (regularity), p. 38.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=49
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61
* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)*, Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf

**Relationship to the sources:** Intrinsic chart/tangent-bundle implementation of Picard–Lindelöf uniqueness and the overlap continuation argument. The local Hausdorff tangent-bundle helper is an implementation adapter.
-/

/-!
# Uniqueness of intrinsic Finsler Euler--Lagrange curves

Equality of actual tangent velocities includes equality of positions. Local coordinate
uniqueness therefore gives equal curve germs. Continuity of the actual tangent lifts
and connectedness propagate their equality throughout an open preconnected time domain.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem tangentMap_eq_of_eventuallyEq {c d : ℝ → M} {t : ℝ}
    (h : c =ᶠ[𝓝 t] d) :
    tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t, (1 : ℝ)⟩ := by
  refine TotalSpace.ext h.eq_of_nhds ?_
  rw [tangentMap, h.eq_of_nhds, tangentMap, h.mfderiv_eq]

private theorem t2Space_tangentBundle [T2Space M] : T2Space (TangentBundle 𝓘(ℝ, E) M) := by
  apply t2_iff_nhds.mpr
  intro p q hpq
  have : NeBot (𝓝 p ⊓ 𝓝 q) := hpq
  have hbase : p.1 = q.1 := tendsto_nhds_unique
    ((FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E) (M := M))).continuousAt.tendsto.mono_left
      inf_le_left)
    ((FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E) (M := M))).continuousAt.tendsto.mono_left
      inf_le_right)
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E) (M := M)) p.1
  have hp : p ∈ e.source := e.mem_source.mpr (mem_baseSet_trivializationAt _ _ _)
  have hq : q ∈ e.source := e.mem_source.mpr (hbase ▸ mem_baseSet_trivializationAt _ _ _)
  have heq : e p = e q := tendsto_nhds_unique
    ((e.toOpenPartialHomeomorph.continuousAt hp).tendsto.mono_left inf_le_left)
    ((e.toOpenPartialHomeomorph.continuousAt hq).tendsto.mono_left inf_le_right)
  exact e.toOpenPartialHomeomorph.injOn hp hq heq

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable [FiniteDimensional ℝ E] {F : ContinuousFinslerNorm E M}
  {c d : ℝ → M} {I : Set ℝ} {t₀ : ℝ}

/-- Equal actual tangent velocities at one time give equal local solution germs. -/
theorem eulerLagrange_eventuallyEq_of_tangentMap_eq (hF : F.IsSmoothStronglyConvex)
    (hc : F.IsEulerLagrangeAt c t₀) (hd : F.IsEulerLagrangeAt d t₀)
    (hv : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t₀, (1 : ℝ)⟩) :
    c =ᶠ[𝓝 t₀] d := by
  obtain ⟨a, U, hU, htU, hcmap, hcx, hcphase, hcEL⟩ := hc
  obtain ⟨b, V, hV, htV, hdmap, hdx, hdphase, hdEL⟩ := hd
  have hcOn : F.IsEulerLagrangeOn c U :=
    fun t ht ↦ ⟨a, U, hU, ht, hcmap, hcx, hcphase, hcEL⟩
  have hdOn : F.IsEulerLagrangeOn d V :=
    fun t ht ↦ ⟨b, V, hV, ht, hdmap, hdx, hdphase, hdEL⟩
  exact hF.manifoldEulerLagrange_eventuallyEq_of_same_initial_data a b hU hV htU htV
    (hF.contMDiffOn_of_isEulerLagrangeOn hcOn) (hF.contMDiffOn_of_isEulerLagrangeOn hdOn)
    hcmap hdmap (fun t ht ↦ (hcphase t ht).2) (fun t ht ↦ (hdphase t ht).2)
    hcEL hdEL (congrArg (fun v : TangentBundle 𝓘(ℝ, E) M ↦ v.1) hv) hv

/-- The actual tangent lift of an intrinsic solution is continuous on its open time domain. -/
theorem continuousOn_tangentCurve_of_isEulerLagrangeOn (hF : F.IsSmoothStronglyConvex)
    (hI : IsOpen I) (hc : F.IsEulerLagrangeOn c I) :
    ContinuousOn (fun t ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) I := by
  have hsmooth := hF.contMDiffOn_of_isEulerLagrangeOn hc
  have huniq : UniqueMDiffOn 𝓘(ℝ, ℝ) I := hI.uniqueMDiffOn
  have htm := hsmooth.continuousOn_tangentMapWithin (by simp) huniq
  have hsection : Continuous (fun t : ℝ ↦ (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    convert (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk (continuous_const (y := (1 : ℝ)))) using 1
    funext t
    rfl
  apply (htm.comp hsection.continuousOn (fun _ ht ↦ ht)).congr
  intro t ht
  exact (tangentMapWithin_eq_tangentMap (huniq t ht)
    ((hF.contMDiffAt_of_isEulerLagrangeAt (hc t ht)).mdifferentiableAt (by simp))).symm

/-- Actual tangent lifts of two intrinsic solutions agree throughout an open preconnected
time domain when they agree at one time. No fixed common coordinate chart is assumed. -/
theorem tangentCurve_eqOn_of_isEulerLagrangeOn [T2Space M] (hF : F.IsSmoothStronglyConvex)
    (hI : IsOpen I) (hconn : IsPreconnected I)
    (hc : F.IsEulerLagrangeOn c I) (hd : F.IsEulerLagrangeOn d I) (ht₀ : t₀ ∈ I)
    (hv : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t₀, (1 : ℝ)⟩) :
    EqOn (fun t ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩)
      (fun t ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t, (1 : ℝ)⟩) I := by
  have : T2Space (TangentBundle 𝓘(ℝ, E) M) := t2Space_tangentBundle
  have : PreconnectedSpace I := Subtype.preconnectedSpace hconn
  let S : Set I := {t | tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t.1, (1 : ℝ)⟩ =
    tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t.1, (1 : ℝ)⟩}
  have hclosed : IsClosed S := isClosed_eq
    (hF.continuousOn_tangentCurve_of_isEulerLagrangeOn hI hc).domRestrict
    (hF.continuousOn_tangentCurve_of_isEulerLagrangeOn hI hd).domRestrict
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have heq := hF.eulerLagrange_eventuallyEq_of_tangentMap_eq (hc t t.2) (hd t t.2) ht
    have hphase : ∀ᶠ s in 𝓝 (t : ℝ), tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨s, (1 : ℝ)⟩ =
        tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨s, (1 : ℝ)⟩ :=
      heq.eventuallyEq_nhds.mono (fun _ hs ↦ tangentMap_eq_of_eventuallyEq hs)
    exact continuousAt_subtype_val.tendsto.eventually hphase
  have hS : S = univ := (show IsClopen S from ⟨hclosed, hopen⟩).eq_univ ⟨⟨t₀, ht₀⟩, hv⟩
  intro t ht
  have hmem : (⟨t, ht⟩ : I) ∈ S := hS.symm ▸ mem_univ _
  exact hmem

/-- Intrinsic Euler--Lagrange curves with the same initial actual tangent velocity
agree on their whole open preconnected time domain. -/
theorem eqOn_of_isEulerLagrangeOn [T2Space M] (hF : F.IsSmoothStronglyConvex)
    (hI : IsOpen I) (hconn : IsPreconnected I)
    (hc : F.IsEulerLagrangeOn c I) (hd : F.IsEulerLagrangeOn d I) (ht₀ : t₀ ∈ I)
    (hv : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t₀, (1 : ℝ)⟩) : EqOn c d I := by
  intro t ht
  exact congrArg (fun v : TangentBundle 𝓘(ℝ, E) M ↦ v.1)
    (hF.tangentCurve_eqOn_of_isEulerLagrangeOn hI hconn hc hd ht₀ hv ht)

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry
