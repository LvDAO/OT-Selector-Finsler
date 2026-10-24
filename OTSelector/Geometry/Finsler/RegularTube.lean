import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.TangentReadout
import OTSelector.Geometry.Manifold.ManifoldInjectiveTube
import OTSelector.Geometry.Manifold.ManifoldPositionRank
import OTSelector.Geometry.Manifold.TangentFamilyPosition

/-!
# Geometry.Finsler.RegularTube

* **Conditions:** A complete C2 actual family with Gauss normality and injective position variation on a compact set of regular central times; central distance isometry separates time.
* **Objects:** Invertible actual time–label differential and one genuine C2 manifold tube inverse over the compact regular set.
* **Proof detail:** Separate time/label columns using actual momentum, apply the inverse function theorem locally and use compact injectivity/tube assembly.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.

Source relation (derived): Regularity on the chosen compact time set is an internal localization premise; this module is not a proof of global absence of focal times.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerRegularTube.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerRegularTube`; the selected original proof blocks follow. -/
section

/-!
# Common regular tubes for the original Finsler family

Gauss normality and the nonzero actual Euler--Lagrange velocity turn injectivity of
position variations into invertibility of the full time-parameter differential.
On a compact set of regular times, central distance isometry then constructs a
common C2 tube inverse of the same manifold-valued family, across arbitrary charts.
The compact set is chosen away from the previously proved finite focal set. Its
regularity is an internal localization requirement, not a final geometric assumption.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}

/-- The full actual time-parameter derivative is invertible at each regular central
point. Its time column is separated from the parameter columns by the original momentum. -/
theorem isInvertible_fderiv_timeLabel_chartPosition (hF : F.IsSmoothStronglyConvex)
    (hdim : Module.finrank ℝ W + 1 = Module.finrank ℝ E)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w₀ : W} (hw : w₀ ∈ B) (old : M) (t : ℝ)
    (hx : Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hnormal : ∀ ξ : W, (F.chartMomentumFamily old Γ (w₀, t)).2
      (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ w t)) w₀ ξ) = 0)
    (hregular : HasInjectiveManifoldPosition (E := E) (fun w ↦ Γ w t) w₀) :
    (fderiv ℝ (fun q : ℝ × W ↦ extChartAt 𝓘(ℝ, E) old (Γ q.2 q.1))
      (t, w₀)).IsInvertible := by
  let γ := fun q : ℝ × W ↦ extChartAt 𝓘(ℝ, E) old (Γ q.2 q.1)
  let D := fderiv ℝ γ (t, w₀)
  let p := (F.chartMomentumFamily old Γ (w₀, t)).2
  have hp := (contMDiffOn_positionFamily_of_tangentFamily hG).contMDiffAt
    ((hB.prod isOpen_univ).mem_nhds
      (show (w₀, t) ∈ B ×ˢ univ from ⟨hw, mem_univ _⟩))
  have hs : ContMDiffAt 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) 2
      (fun q ↦ Γ q.2 q.1) (t, w₀) :=
    hp.comp (t, w₀) ((contDiffAt_snd.prodMk contDiffAt_fst).contMDiffAt)
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 2 (extChartAt 𝓘(ℝ, E) old)
      (Γ w₀ t) := contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hx)
  have hd : HasFDerivAt γ D (t, w₀) :=
    ((hc.comp (t, w₀) hs).contDiffAt.differentiableAt (by norm_num)).hasFDerivAt
  have htime : D (1, 0) = deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w₀) t := by
    exact (hd.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t w₀))).deriv.symm
  have hlabel (ξ : W) :
      D (0, ξ) = fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ w t)) w₀ ξ := by
    have hl := hd.comp w₀ ((hasFDerivAt_const t w₀).prodMk (hasFDerivAt_id w₀))
    simpa [γ, Function.comp_def] using congrArg (fun A : W →L[ℝ] E ↦ A ξ) hl.fderiv.symm
  have hpt : p (D (1, 0)) ≠ 0 := by
    rw [htime]
    have hz := (hF.chartTangent_of_isEulerLagrangeAt
      (hEL w₀ hw t (mem_univ _)) old hx).2
    change fiberLegendre (F.chartEnergy old)
      ((extChartAt 𝓘(ℝ, E) old ∘ Γ w₀) t,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w₀) t)
      (deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w₀) t) ≠ 0
    rw [hF.chartLegendre_self_eq_chartLength_sq old hz]
    exact pow_ne_zero _ (NNReal.coe_pos.mpr (F.chartLength_pos old hz)).ne'
  have hker (q : ℝ × W) (hq : D q = 0) : q = 0 := by
    have hsplit : D q = q.1 • D (1, 0) + D (0, q.2) := by
      rw [← _root_.map_smul, ← map_add]
      congr 1
      simp
    have hτ : q.1 = 0 := by
      have h := congrArg p hq
      rw [hsplit, map_add, _root_.map_smul, _root_.map_zero, hlabel, hnormal, add_zero] at h
      exact (mul_eq_zero.mp h).resolve_right hpt
    have hξ : q.2 = 0 := by
      apply hregular old hx
      change fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ w t)) w₀ q.2 =
        fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ w t)) w₀ 0
      rw [_root_.map_zero, ← hlabel]
      simpa only [hsplit, hτ, zero_smul, zero_add] using hq
    exact Prod.ext hτ hξ
  have hi : Function.Injective D := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, hxy, sub_self]
  have hdim' : Module.finrank ℝ (ℝ × W) = Module.finrank ℝ E := by
    simpa only [Module.finrank_prod, Module.finrank_self, add_comm] using hdim
  let A := (D.toLinearMap.linearEquivOfInjective hi hdim').toContinuousLinearEquiv
  exact ⟨A, rfl⟩

/-- A compact regular portion of the same original distance-isometric central curve
has a common C2 manifold tube inverse. No single chart need contain that portion. -/
theorem exists_regular_manifoldTube_of_completeFamily [T2Space M] [PreconnectedSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hdim : Module.finrank ℝ W + 1 = Module.finrank ℝ E)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w₀ : W} (hw : w₀ ∈ B) {a b : ℝ}
    (hiso : letI : MetricSpace M := F.metricSpace; Isometry (fun t : Icc a b ↦ Γ w₀ t))
    {K : Set ℝ} (hK : IsCompact K) (hKIcc : K ⊆ Icc a b)
    (hnormal : ∀ (t : ℝ), t ∈ K → ∀ (old : M),
      Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source → ∀ ξ : W,
      (F.chartMomentumFamily old Γ (w₀, t)).2
        (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ w t)) w₀ ξ) = 0)
    (hregular : ∀ t ∈ K, HasInjectiveManifoldPosition (E := E) (fun w ↦ Γ w t) w₀) :
    ∃ (T : Set ℝ) (V : Set W) (e : OpenPartialHomeomorph (ℝ × W) M),
      IsOpen T ∧ IsOpen V ∧ K ⊆ T ∧ w₀ ∈ V ∧ T ×ˢ V ⊆ univ ×ˢ B ∧
      (e : ℝ × W → M) = (fun q ↦ Γ q.2 q.1) ∧ e.source = T ×ˢ V ∧
      e.target = (fun q : ℝ × W ↦ Γ q.2 q.1) '' (T ×ˢ V) ∧
      ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) 2 e e.source ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) 2 e.symm e.target := by
  have hp : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) 2
      (fun q ↦ Γ q.2 q.1) (univ ×ˢ B) :=
    (contMDiffOn_positionFamily_of_tangentFamily hG).comp
      ((contDiff_snd.prodMk contDiff_fst).contMDiff.contMDiffOn)
      (fun _ hq ↦ ⟨hq.2, hq.1⟩)
  have hi : InjOn (Γ w₀) K := by
    have hi' : Function.Injective (fun t : Icc a b ↦ Γ w₀ t) := by
      let : MetricSpace M := F.metricSpace
      exact hiso.injective
    intro s hs t ht hst
    exact congrArg Subtype.val (hi' (a₁ := ⟨s, hKIcc hs⟩) (a₂ := ⟨t, hKIcc ht⟩) hst)
  apply exists_manifold_common_tube_inverse hK (isOpen_univ.prod hB) (by norm_num) hp
    (by rintro ⟨t, w⟩ ⟨_, hw'⟩; exact ⟨mem_univ _, mem_singleton_iff.mp hw' ▸ hw⟩) hi
  intro t ht
  exact hF.isInvertible_fderiv_timeLabel_chartPosition hdim hB hEL hG hw (Γ w₀ t) t
    (mem_extChartAt_source (Γ w₀ t)) (hnormal t ht (Γ w₀ t)
      (mem_extChartAt_source (Γ w₀ t))) (hregular t ht)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
