import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Hamiltonian.GraphDynamics
import OTSelector.Geometry.Finsler.AdaptedClock
import OTSelector.Geometry.Finsler.AdaptedGraphLagrangian
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.EulerLagrangeCovariance
import OTSelector.Geometry.Finsler.LengthHomogeneity

/-!
# Geometry.Finsler.AdaptedGraphCurve

* **Conditions:** An intrinsic nonzero-velocity Euler–Lagrange germ, or a smooth scalar clock with strictly positive derivative.
* **Objects:** A genuine positive inverse clock and an actual adapted graph curve preserving the original energy/length formulas.
* **Proof detail:** Choose the momentum clock, apply the scalar inverse theorem and use positive velocity homogeneity in the true time change.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerAdaptedGraphCurve.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerAdaptedGraphCurve`; the selected original proof blocks follow. -/
section

/-!
# A genuine adapted graph of an intrinsic Finsler Euler--Lagrange curve

The original momentum chooses the transverse kernel and a positive clock. The scalar
inverse function theorem constructs the actual inverse clock. Thus neither a time
change nor graph Euler--Lagrange is an input to the final intrinsic consumer.
-/

open Set Filter Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

/-- A smooth positive clock has a genuine smooth local inverse inside the given
open domain. Positivity of the inverse derivative is derived from the actual inverse. -/
theorem exists_smooth_positive_clock_inverse {f : ℝ → ℝ} {I : Set ℝ} {t : ℝ}
    (hI : IsOpen I) (ht : t ∈ I) (hf : ContDiffOn ℝ ∞ f I)
    (hpos : ∀ s ∈ I, 0 < deriv f s) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      (e : ℝ → ℝ) = f ∧ t ∈ e.source ∧ e.source ⊆ I ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧ ∀ s ∈ e.target, 0 < deriv e.symm s := by
  have hfAt := hf.contDiffAt (hI.mem_nhds ht)
  have hd := (hfAt.differentiableAt (by simp)).hasDerivAt
  have hd' := hd.hasFDerivAt_equiv (hpos t ht).ne'
  let e₀ := hfAt.toOpenPartialHomeomorph f hd' (by simp)
  let e := e₀.restr I
  have he : (e : ℝ → ℝ) = f := rfl
  have hsource : e.source = e₀.source ∩ I := e₀.restr_source' I hI
  have ht₀ : t ∈ e₀.source := hfAt.mem_toOpenPartialHomeomorph_source hd' (by simp)
  have htE : t ∈ e.source := by rw [hsource]; exact ⟨ht₀, ht⟩
  have hsub : e.source ⊆ I := by rw [hsource]; exact inter_subset_right
  have hdAt (s : ℝ) (hs : s ∈ e.target) : HasDerivAt e
      (deriv f (e.symm s)) (e.symm s) := by
    rw [he]
    exact ((hf.contDiffAt (hI.mem_nhds (hsub (e.map_target hs)))).differentiableAt
      (by simp)).hasDerivAt
  refine ⟨e, he, htE, hsub, ?_, ?_⟩
  · intro s hs
    apply (e.contDiffAt_symm_deriv (hpos _ (hsub (e.map_target hs))).ne'
      hs (hdAt s hs) ?_).contDiffWithinAt
    rw [he]
    exact hf.contDiffAt (hI.mem_nhds (hsub (e.map_target hs)))
  · intro s hs
    rw [(e.hasDerivAt_symm hs (hpos _ (hsub (e.map_target hs))).ne' (hdAt s hs)).deriv]
    exact inv_pos.mpr (hpos _ (hsub (e.map_target hs)))

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}

/-- An actual intrinsic solution automatically admits a smooth graph representation
in the momentum-adapted coordinates. Its actual inverse clock is positive, and its
spatial graph satisfies the original-length-derived graph Euler--Lagrange equation. -/
theorem exists_adaptedGraph_curve_of_isEulerLagrangeAt
    (hF : F.IsSmoothStronglyConvex) {c : ℝ → M} {t : ℝ}
    (hc : F.IsEulerLagrangeAt c t) (old : M)
    (hx : c t ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    let x := extChartAt 𝓘(ℝ, E) old ∘ c
    let p := fiberLegendre (F.chartEnergy old) (x t, deriv x t)
    Module.finrank ℝ p.ker + 1 = Module.finrank ℝ E ∧
    ∃ (A : E ≃L[ℝ] (ℝ × p.ker)) (I : Set ℝ) (e : OpenPartialHomeomorph ℝ ℝ),
      let τ := e.symm
      let y := fun s ↦ (A (x (τ s))).2
      A (deriv x t) = (1, 0) ∧ IsOpen I ∧ IsPreconnected I ∧ t ∈ I ∧
      MapsTo c I (extChartAt 𝓘(ℝ, E) old).source ∧ ContDiffOn ℝ ∞ x I ∧
      (e : ℝ → ℝ) = (fun s ↦ (A (x s)).1) ∧ t ∈ e.source ∧ e.source ⊆ I ∧
      (A (x t)).1 ∈ e.target ∧ τ ((A (x t)).1) = t ∧
      ContDiffOn ℝ ∞ τ e.target ∧ MapsTo τ e.target I ∧
      (∀ s ∈ e.target, 0 < deriv τ s) ∧ ContDiffOn ℝ ∞ y e.target ∧
      (∀ s ∈ e.target, A (x (τ s)) = (s, y s)) ∧
      (∀ s ∈ e.target, HasDerivAt
        (fun r ↦ fiberLegendre (F.adaptedGraphLagrangian old A) ((r, y r), deriv y r))
        (GraphHamiltonian.positionDifferential (F.adaptedGraphLagrangian old A)
          ((s, y s), deriv y s)) s) ∧
      ∀ s ∈ e.target,
        tangentLift A.symm ((s, y s), (1, deriv y s)) =
          (x (τ s), deriv τ s • deriv x (τ s)) ∧
        F.adaptedGraphLagrangian old A ((s, y s), deriv y s) =
          deriv τ s * (F.chartLength old (x (τ s), deriv x (τ s)) : ℝ) ∧
        pullbackEnergy A.symm (F.chartEnergy old) ((s, y s), (1, deriv y s)) =
          deriv τ s ^ 2 * F.chartEnergy old (x (τ s), deriv x (τ s)) := by
  let x := extChartAt 𝓘(ℝ, E) old ∘ c
  obtain ⟨hdim, A, J₀, hJ₀, ht₀, _, hy₀, hyt, hpos₀, _, _, _⟩ :=
    hF.exists_adapted_chartClock_of_isEulerLagrangeAt hc old hx
  change ContDiffOn ℝ ∞ (A ∘ x) J₀ at hy₀
  change HasDerivAt (A ∘ x) (1, 0) t at hyt
  change ∀ s ∈ J₀, 0 < (deriv (A ∘ x) s).1 at hpos₀
  obtain ⟨U, hU, htU, hm, hxC, hphase, hEL⟩ :=
    hF.exists_chartEulerLagrangeOn_of_isEulerLagrangeAt hc old hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp ((hU.inter hJ₀).mem_nhds ⟨htU, ht₀⟩)
  let I := Ioo (t - r) (t + r)
  have hI : IsOpen I := isOpen_Ioo
  have htI : t ∈ I := ⟨by linarith, by linarith⟩
  have hsub : I ⊆ U ∩ J₀ := by
    simpa only [Real.ball_eq_Ioo] using hball
  have hxI : ContDiffOn ℝ ∞ x I := hxC.mono (hsub.trans inter_subset_left)
  have hyI : ContDiffOn ℝ ∞ (A ∘ x) I := hy₀.mono (hsub.trans inter_subset_right)
  let clock := fun s ↦ (A (x s)).1
  have hclockC : ContDiffOn ℝ ∞ clock I := hyI.fst
  have hclockD (s : ℝ) (hs : s ∈ I) : deriv clock s = (deriv (A ∘ x) s).1 := by
    have hd : HasDerivAt (A ∘ x) (deriv (A ∘ x) s) s :=
      ((hyI.contDiffAt (hI.mem_nhds hs)).differentiableAt (by simp)).hasDerivAt
    have hd₁ : HasDerivAt clock (deriv (A ∘ x) s).1 s := hd.fst
    exact hd₁.deriv
  have hclockPos (s : ℝ) (hs : s ∈ I) : 0 < deriv clock s := by
    rw [hclockD s hs]
    exact hpos₀ s (hsub hs).2
  obtain ⟨e, he, htE, heI, hτC, hτpos⟩ :=
    exists_smooth_positive_clock_inverse hI htI hclockC hclockPos
  have hτI : MapsTo e.symm e.target I := fun _ hs ↦ heI (e.map_target hs)
  have hclock (s : ℝ) (hs : s ∈ e.target) : (A (x (e.symm s))).1 = s := by
    exact (congrFun he (e.symm s)).symm.trans (e.right_inv hs)
  have hAv : A (deriv x t) = (1, 0) := by
    have hxD := ((hxI.contDiffAt (hI.mem_nhds htI)).differentiableAt (by simp)).hasDerivAt
    exact (A.hasFDerivAt.comp_hasDerivAt t hxD).unique hyt
  refine ⟨hdim, A, I, e, hAv, hI, isPreconnected_Ioo, htI,
    hm.mono_left (hsub.trans inter_subset_left), hxI, he, htE, heI, ?_, ?_, hτC,
    hτI, hτpos, ?_, ?_, ?_, ?_⟩
  · change clock t ∈ e.target
    rw [← congrFun he t]
    exact e.map_source htE
  · change e.symm (clock t) = t
    rw [← congrFun he t]
    exact e.left_inv htE
  · exact (A.contDiff.comp_contDiffOn (hxI.comp hτC hτI)).snd
  · intro s hs
    exact Prod.ext (hclock s hs) rfl
  · exact hF.adaptedGraph_eulerLagrange_reparam old A hI isPreconnected_Ioo
      (hxI.of_le (by simp)) (fun s hs ↦ hphase s (hsub hs).1)
      (fun s hs ↦ hEL s (hsub hs).1) e.open_target (hτC.of_le (by simp)) hτI hτpos hclock
  · let y := fun s ↦ (A (x (e.symm s))).2
    have hyC : ContDiffOn ℝ ∞ y e.target :=
      (A.contDiff.comp_contDiffOn (hxI.comp hτC hτI)).snd
    have heq : EqOn (fun s ↦ A (x (e.symm s))) (fun s ↦ (s, y s)) e.target :=
      fun s hs ↦ Prod.ext (hclock s hs) rfl
    intro s hs
    have hxD := ((hxI.contDiffAt (hI.mem_nhds (hτI hs))).differentiableAt
      (by simp)).hasDerivAt
    have hτD := ((hτC.contDiffAt (e.open_target.mem_nhds hs)).differentiableAt
      (by simp)).hasDerivAt
    have hyD := ((hyC.contDiffAt (e.open_target.mem_nhds hs)).differentiableAt
      (by simp)).hasDerivAt
    have hd := A.hasFDerivAt.comp_hasDerivAt s (hxD.scomp s hτD)
    have hdg := (hasDerivAt_id s).prodMk hyD
    have hv : A (deriv e.symm s • deriv x (e.symm s)) = (1, deriv y s) :=
      hd.deriv.symm.trans ((heq.eventuallyEq_of_mem (e.open_target.mem_nhds hs)).deriv_eq
        |>.trans hdg.deriv)
    have hp : tangentLift A.symm ((s, y s), (1, deriv y s)) =
        (x (e.symm s), deriv e.symm s • deriv x (e.symm s)) := by
      rw [tangentLift_linearEquiv]
      change (A.symm (s, y s), A.symm (1, deriv y s)) = _
      have hbase : A (x (e.symm s)) = (s, y s) := heq hs
      rw [← hbase, ← hv]
      simp only [ContinuousLinearEquiv.symm_apply_apply]
    refine ⟨hp, ?_, ?_⟩
    · rw [F.adaptedGraphLagrangian_eq_pullback, pullbackEnergy, hp]
      exact F.chartLength_pos_smul old (hphase _ (hsub (hτI hs)).1).1 (hτpos s hs) _
    · rw [pullbackEnergy, hp]
      exact F.chartEnergy_smul old (hphase _ (hsub (hτI hs)).1).1 _ _

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
