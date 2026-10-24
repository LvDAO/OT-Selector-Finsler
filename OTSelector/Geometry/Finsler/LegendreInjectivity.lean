import OTSelector.Analysis.Convex.HomogeneousEnergy
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerLegendreInjectivity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerLegendreInjectivity`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.LegendreInjectivity

* **Conditions:** For the generic lemma, C2 regularity off zero, positive radial pairing and positive Hessian; smooth strong convexity supplies these for Finsler energy.
* **Objects:** Injectivity of the fiber derivative on nonzero velocities and of the parametric Finsler Legendre map.
* **Proof detail:** If endpoint covectors agree their common positive pairing excludes zero from the joining segment; positive Hessian then forces strict derivative growth unless the velocities agree.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): Shen states invertible Legendre duality; the generic slit-domain injectivity argument is proved locally without differentiability at zero or an assumed inverse branch.
-/

/-!
# Injectivity of the actual nonlinear Finsler Legendre map

Positive radial pairing and positive actual Hessian force the fiber differential to
be injective away from zero. If two covectors agree, that covector is positive on
the entire segment joining their velocities, so this segment avoids zero. The
Hessian gives strict growth along the segment, contradicting equal endpoint
covectors unless the velocities coincide. Euler homogeneity supplies the positive
radial pairing for the actual Finsler energy, in both fiber and chart coordinates.
No differentiability at zero or assumed choice of an inverse branch is needed.
-/

open Set Filter AffineMap Manifold
open scoped Topology ContDiff

noncomputable section

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Positive radial pairing and actual Hessian positivity give nonlinear Legendre
injectivity on the nonzero fiber, without differentiability at zero. -/
theorem fderiv_injOn_of_radial_pos_hessian_pos {L : E → ℝ}
    (hL : ∀ v : E, v ≠ 0 → ContDiffAt ℝ 2 L v)
    (hrad : ∀ v : E, v ≠ 0 → 0 < fderiv ℝ L v v)
    (hH : ∀ v : E, v ≠ 0 → ∀ w : E, w ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ L) v w w) :
    InjOn (fderiv ℝ L) {v : E | v ≠ 0} := by
  intro v hv w hw heq
  by_contra hvw
  have hd : w - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hvw)
  let z : ℝ → E := lineMap v w
  have hz : ∀ t ∈ Icc (0 : ℝ) 1, z t ≠ 0 := by
    intro t ht htzero
    have hpv := hrad v hv
    have hpw : 0 < fderiv ℝ L v w := by rw [heq]; exact hrad w hw
    have hp : 0 < fderiv ℝ L v (z t) := by
      dsimp only [z]
      rw [lineMap_apply_module]
      simp only [map_add, map_smul, smul_eq_mul]
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) hpv.le,
        mul_nonneg ht.1 hpw.le]
    rw [htzero, map_zero] at hp
    exact lt_irrefl _ hp
  let g : ℝ → ℝ := fun t ↦ fderiv ℝ L (z t) (w - v)
  have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt g (fderiv ℝ (fderiv ℝ L) (z t) (w - v) (w - v)) t := by
    have hD := ((hL _ (hz t ht)).fderiv_right (m := 1) (by norm_num)).differentiableAt_one
    have hc := hD.hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_lineMap (a := v) (b := w) (x := t))
    have hh := hc.clm_apply (hasDerivAt_const t (w - v))
    simpa only [map_zero, add_zero, Function.comp_def] using hh
  have hmono : StrictMonoOn g (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t ht ↦ (hg t ht).continuousAt.continuousWithinAt)
    intro t ht
    rw [(hg t (interior_subset ht)).deriv]
    exact hH _ (hz t (interior_subset ht)) _ hd
  have hlt := hmono (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
    zero_lt_one
  have hends : g 0 = g 1 := by simp only [g, z, lineMap_apply_zero, lineMap_apply_one, heq]
  exact (ne_of_lt hlt) hends

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}

/-- The actual nonlinear differential of each Finsler fiber energy is injective
on all nonzero velocities, with no common-energy premise. -/
theorem injOn_fiberEnergy_legendre (hF : F.IsSmoothStronglyConvex) (x : M) :
    InjOn (fderiv ℝ (F.fiberEnergyModel x)) {v : E | v ≠ 0} := by
  apply fderiv_injOn_of_radial_pos_hessian_pos
    (fun v hv ↦ (hF.contDiffAt_fiberEnergyModel x hv).of_le (by simp))
  · intro v hv
    rw [hF.fiberEnergy_euler x hv]
    exact mul_pos (by norm_num) (F.fiberEnergyModel_pos x hv)
  · exact hF.hessian_pos x

/-- The actual chart Legendre map is fiberwise injective on every nonzero velocity;
this removes ambiguity between different local inverse branches. -/
theorem injOn_chartEnergy_legendre (hF : F.IsSmoothStronglyConvex) (old : M)
    {u : E} (hu : u ∈ (extChartAt 𝓘(ℝ, E) old).target) :
    InjOn (fun v ↦ fiberLegendre (F.chartEnergy old) (u, v)) {v : E | v ≠ 0} := by
  let L : E → ℝ := fun v ↦ F.chartEnergy old (u, v)
  have hL (v : E) (hv : v ≠ 0) : ContDiffAt ℝ 2 L v := by
    exact ((hF.contDiffOn_chartEnergy old).contDiffAt
      ((isOpen_chartEnergyDomain old).mem_nhds (show (u, v) ∈ chartEnergyDomain old from ⟨hu, hv⟩))).of_le (by simp) |>.comp v
        (contDiffAt_const.prodMk contDiffAt_id)
  apply fderiv_injOn_of_radial_pos_hessian_pos hL
  · intro v hv
    rw [twoHomogeneous_fderiv_euler
      (fun r _ ↦ F.chartEnergy_smul old hu r v) ((hL v hv).differentiableAt (by norm_num))]
    apply mul_pos (by norm_num)
    change 0 < F.chartEnergy old (u, v)
    rw [F.chartEnergy_eq_fiberEnergyModel old hu]
    apply F.fiberEnergyModel_pos
    exact (chartFiberEquiv old hu).map_ne_zero_iff.mpr hv
  · intro v hv w hw
    exact hF.chartEnergy_hessian_pos old (show (u, v) ∈ chartEnergyDomain old from ⟨hu, hv⟩) hw


/-- Retaining the base coordinate makes the actual parametric Legendre map injective
on its entire chart slit domain, even when local inverse neighborhoods overlap. -/
theorem injOn_parametricLegendre_chartEnergy (hF : F.IsSmoothStronglyConvex) (old : M) :
    InjOn (parametricLegendre (F.chartEnergy old)) (chartEnergyDomain old) := by
  rintro ⟨u, v⟩ hz ⟨u', v'⟩ hw heq
  have hb : u = u' := congrArg Prod.fst heq
  subst u'
  have hp := congrArg Prod.snd heq
  have hv : v = v' := hF.injOn_chartEnergy_legendre old hz.1 hz.2 hw.2 hp
  exact Prod.ext rfl hv

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
