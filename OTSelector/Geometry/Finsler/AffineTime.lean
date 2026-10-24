import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Coordinates.NormalData
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.SmoothMinimizer
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.LengthMetric

/-!
# Geometry.Finsler.AffineTime

* **Conditions:** The actual original energy dynamics and a positive affine change of time; nondegenerate time endpoints for the fixed-time minimizing existence theorem.
* **Objects:** Affine-time preservation of Euler–Lagrange, exact speed scaling and smooth actual minimizers on the prescribed time interval.
* **Proof detail:** Use degree-two energy, degree-one momentum and degree-two base derivatives with the chain rule, then rescale the unit minimizing curve.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): Only positive affine changes preserve this energy equation; general positive time changes are handled for length equations separately.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerAffineTime.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerAffineTime`; the selected original proof blocks follow. -/
section

/-!
# Positive affine time changes of the original Finsler energy dynamics

Degree-two homogeneity of the actual energy gives degree-one momentum and degree-two
base differential. Their actual chain rules preserve energy Euler--Lagrange under a
positive affine time change. This is an energy equation statement, independent of the
more general reparameterization invariance of the length equation.

The original unit-speed minimizing curve can consequently be placed on any prescribed
nondegenerate time interval, preserving the original endpoint and path-length identities.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem affineTime_hasDerivAt (s a t : ℝ) :
    HasDerivAt (fun r ↦ s * (r - a)) s t := by
  simpa using ((hasDerivAt_id t).sub_const a).const_mul s

private theorem affineTime_contDiff (s a : ℝ) :
    ContDiff ℝ ∞ (fun r ↦ s * (r - a)) :=
  contDiff_const.mul (contDiff_id.sub contDiff_const)

set_option backward.isDefEq.respectTransparency false in
/-- Actual original tangent speed scales by the positive affine time slope. -/
theorem speed_affine (F : ContinuousFinslerNorm E M) {c : ℝ → M}
    {s a t : ℝ} (hs : 0 < s)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (s * (t - a))) :
    (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (c ∘ (fun r ↦ s * (r - a))) ⟨t, (1 : ℝ)⟩) : ℝ) =
      s * (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c
        ⟨s * (t - a), (1 : ℝ)⟩) : ℝ) := by
  have hd := affineTime_hasDerivAt s a t
  rw [tangentMap_comp_at ⟨t, (1 : ℝ)⟩ hc hd.differentiableAt.mdifferentiableAt]
  have ht : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r ↦ s * (r - a))
      ⟨t, (1 : ℝ)⟩ = ⟨s * (t - a), s⟩ := by
    simp only [tangentMap, mfderiv_eq_fderiv]
    congr 1
    exact (fderiv_apply_one_eq_deriv (𝕜 := ℝ)).trans hd.deriv
  rw [ht]
  change (F.toFun ⟨c (s * (t - a)),
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (s * (t - a)) s⟩ : ℝ) = _
  have hv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (s * (t - a)) s =
      s • mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (s * (t - a)) 1 := by
    simpa only [smul_eq_mul, mul_one] using
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (s * (t - a))).map_smul s (1 : ℝ)
  rw [hv, F.map_smul]
  simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, abs_of_pos hs, tangentMap]

namespace IsSmoothStronglyConvex
variable {F : ContinuousFinslerNorm E M}

/-- The actual base energy differential has degree two in velocity. -/
theorem chartBaseEnergy_smul (hF : F.IsSmoothStronglyConvex) (old : M)
    {z : E × E} (hz : z ∈ chartEnergyDomain old) (s : ℝ) :
    baseEnergyDifferential (F.chartEnergy old) (z.1, s • z.2) =
      s ^ 2 • baseEnergyDifferential (F.chartEnergy old) z := by
  have hd := ((hF.contDiffOn_chartEnergy old).contDiffAt
    ((isOpen_chartEnergyDomain old).mem_nhds hz)).differentiableAt (by simp)
  have hi : DifferentiableAt ℝ (fun x : E ↦ (x, z.2)) z.1 :=
    differentiableAt_id.prodMk (differentiableAt_const z.2)
  have hb := hd.comp z.1 hi
  have heq : (fun x ↦ F.chartEnergy old (x, s • z.2)) =ᶠ[𝓝 z.1]
      (fun x ↦ s ^ 2 * F.chartEnergy old (x, z.2)) := by
    filter_upwards [(isOpen_extChartAt_target old).mem_nhds hz.1] with x hx
    exact F.chartEnergy_smul old hx s z.2
  change fderiv ℝ (fun x ↦ F.chartEnergy old (x, s • z.2)) z.1 = _
  rw [heq.fderiv_eq]
  exact (hb.hasFDerivAt.const_mul (s ^ 2)).fderiv

/-- The actual chart energy equation survives a positive affine change of time. -/
theorem chartEnergy_eulerLagrange_affine (hF : F.IsSmoothStronglyConvex) (old : M)
    {x : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hx : ContDiffOn ℝ 2 x I)
    (hphase : ∀ t ∈ I, (x t, deriv x t) ∈ chartEnergyDomain old)
    (hEL : ∀ t ∈ I, HasDerivAt
      (fun r ↦ fiberLegendre (F.chartEnergy old) (x r, deriv x r))
      (baseEnergyDifferential (F.chartEnergy old) (x t, deriv x t)) t)
    {s a t : ℝ} (hs : 0 < s) (ht : s * (t - a) ∈ I) :
    HasDerivAt
      (fun r ↦ fiberLegendre (F.chartEnergy old)
        ((x ∘ (fun v ↦ s * (v - a))) r, deriv (x ∘ (fun v ↦ s * (v - a))) r))
      (baseEnergyDifferential (F.chartEnergy old)
        ((x ∘ (fun v ↦ s * (v - a))) t, deriv (x ∘ (fun v ↦ s * (v - a))) t)) t := by
  have hd (r : ℝ) (hr : s * (r - a) ∈ I) :
      deriv (x ∘ (fun v ↦ s * (v - a))) r = s • deriv x (s * (r - a)) := by
    exact (((hx.contDiffAt (hI.mem_nhds hr)).differentiableAt (by norm_num)).hasDerivAt.scomp
      r (affineTime_hasDerivAt s a r)).deriv
  have hforce : baseEnergyDifferential (F.chartEnergy old)
      ((x ∘ (fun v ↦ s * (v - a))) t, deriv (x ∘ (fun v ↦ s * (v - a))) t) =
      s ^ 2 • baseEnergyDifferential (F.chartEnergy old) (x (s * (t - a)),
        deriv x (s * (t - a))) := by
    rw [hd t ht]
    exact hF.chartBaseEnergy_smul old (hphase _ ht) s
  rw [hforce]
  have h := ((hEL _ ht).scomp t (affineTime_hasDerivAt s a t)).const_smul s
  simp only [smul_smul, ← pow_two] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [((affineTime_contDiff s a).continuous.continuousAt.preimage_mem_nhds
    (hI.mem_nhds ht))] with r hr
  rw [hd r hr]
  exact hF.chartLegendre_pos_smul old (hphase _ hr).1 (hphase _ hr).2 hs

/-- Positive affine reparameterization preserves the intrinsic original energy equation. -/
theorem isEulerLagrangeAt_affine (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {s a t : ℝ} (hs : 0 < s)
    (hc : F.IsEulerLagrangeAt c (s * (t - a))) :
    F.IsEulerLagrangeAt (c ∘ (fun r ↦ s * (r - a))) t := by
  obtain ⟨old, I, hI, ht, hmap, hx, hphase, hEL⟩ := hc
  let τ : ℝ → ℝ := fun r ↦ s * (r - a)
  let J := τ ⁻¹' I
  have hτ : ContDiff ℝ ∞ τ := affineTime_contDiff s a
  have hJ : IsOpen J := hI.preimage hτ.continuous
  have hderiv (r : ℝ) (hr : r ∈ J) :
      deriv ((extChartAt 𝓘(ℝ, E) old ∘ c) ∘ τ) r =
        s • deriv (extChartAt 𝓘(ℝ, E) old ∘ c) (τ r) :=
    (((hx.contDiffAt (hI.mem_nhds hr)).differentiableAt (by norm_num)).hasDerivAt.scomp
      r (affineTime_hasDerivAt s a r)).deriv
  refine ⟨old, J, hJ, ht, (fun r hr ↦ hmap hr),
    hx.comp (hτ.of_le (by simp)).contDiffOn (fun _ hr ↦ hr), ?_, ?_⟩
  · intro r hr
    change (((extChartAt 𝓘(ℝ, E) old ∘ c) ∘ τ) r,
      deriv ((extChartAt 𝓘(ℝ, E) old ∘ c) ∘ τ) r) ∈ chartEnergyDomain old
    rw [hderiv r hr]
    exact ⟨(hphase _ hr).1, smul_ne_zero hs.ne' (hphase _ hr).2⟩
  · intro r hr
    exact hF.chartEnergy_eulerLagrange_affine old hI hx hphase hEL hs hr

/-- The same positive affine time change preserves the intrinsic equation on its
whole preimage time domain, including complete curves. -/
theorem isEulerLagrangeOn_affine (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {I : Set ℝ} (hc : F.IsEulerLagrangeOn c I) {s a : ℝ} (hs : 0 < s) :
    F.IsEulerLagrangeOn (c ∘ (fun r ↦ s * (r - a)))
      ((fun r ↦ s * (r - a)) ⁻¹' I) :=
  fun _ ht ↦ hF.isEulerLagrangeAt_affine hs (hc _ ht)

variable [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]

/-- Distinct endpoints admit a complete original energy Euler--Lagrange minimizer on
any prescribed nondegenerate time interval. Its actual speed is distance divided by time. -/
theorem exists_smooth_lengthMetric_minimizer_fixedTime (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {a b : ℝ} (hab : a < b) {x y : M} (hxy : x ≠ y) :
    letI : MetricSpace M := F.metricSpace
    letI : ∀ z : M, ENorm (TangentSpace 𝓘(ℝ, E) z) := F.enorm
    ∃ c : ℝ → M, c a = x ∧ c b = y ∧
      F.IsEulerLagrangeOn c univ ∧ ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c ∧
      (∀ t : ℝ, (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) : ℝ) =
        dist x y / (b - a)) ∧
      ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v →
        F.lengthEDist (c u) (c v) = Manifold.pathELength 𝓘(ℝ, E) c u v := by
  let : MetricSpace M := F.metricSpace
  let : ∀ z : M, ENorm (TangentSpace 𝓘(ℝ, E) z) := F.enorm
  let : ∀ z : M, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) z) := F.enormSMulClass
  let s := dist x y / (b - a)
  have hs : 0 < s := div_pos (dist_pos.mpr hxy) (sub_pos.mpr hab)
  let τ : ℝ → ℝ := fun t ↦ s * (t - a)
  have hτa : τ a = 0 := by simp [τ]
  have hτb : τ b = dist x y := by
    exact div_mul_cancel₀ (dist x y) (sub_pos.mpr hab).ne'
  have hτmono : Monotone τ := fun u v huv ↦
    mul_le_mul_of_nonneg_left (sub_le_sub_right huv a) hs.le
  have hτmap : MapsTo τ (Icc a b) (Icc (0 : ℝ) (dist x y)) := by
    intro t ht
    constructor
    · rw [← hτa]
      exact hτmono ht.1
    · rw [← hτb]
      exact hτmono ht.2
  have hτsmooth : ContDiff ℝ ∞ τ := affineTime_contDiff s a
  obtain ⟨g, hg0, hgy, hgEL, hgsmooth, hgspeed, _, hgmin⟩ :=
    hF.exists_smooth_lengthMetric_minimizer hcomplete hxy
  refine ⟨g ∘ τ, ?_, ?_, ?_, hgsmooth.comp hτsmooth.contMDiff, ?_, ?_⟩
  · simpa only [Function.comp_apply, hτa] using hg0
  · simpa only [Function.comp_apply, hτb] using hgy
  · simpa only [preimage_univ] using hF.isEulerLagrangeOn_affine hgEL (a := a) hs
  · intro t
    have h := F.speed_affine hs
      ((hgsmooth (s * (t - a))).mdifferentiableAt (by simp))
    simpa only [hgspeed _, NNReal.coe_one, mul_one] using h
  · intro u hu v hv huv
    rw [Manifold.pathELength_comp_of_monotoneOn huv (hτmono.monotoneOn _)
      (hτsmooth.differentiable (by simp)).differentiableOn
      ((hgsmooth.mdifferentiable (by simp)).mdifferentiableOn)]
    exact hgmin (τ u) (hτmap hu) (τ v) (hτmap hv) (hτmono huv)

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
