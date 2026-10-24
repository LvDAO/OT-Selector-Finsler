import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.FamilyFrechetFirstVariation
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.TangentReadout

/-!
# Geometry.Finsler.InitialPhaseMomentum

* **Conditions:** A prescribed actual initial tangent family at a legal original chart state.
* **Objects:** Intrinsic initial length momentum on actual parameter variations equal to original chart momentum on the initial-position component.
* **Proof detail:** Read the exact initial position map, apply actual chart length covariance and differentiate the inverse-chart identity.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).

Source relation (derived): No unit-speed or independent parameter-regularity premise is needed for this initial readout identity.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerInitialPhaseMomentum.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerInitialPhaseMomentum`; the selected original proof blocks follow. -/
section

/-!
# Initial length momentum of the original phase family

The prescribed initial tangent fixes the initial position map in its original chart.
The actual chart length covariance then identifies intrinsic initial length momentum
on parameter variations with chart length momentum on the initial position component.
No parameter regularity or unit-speed hypothesis is needed for this identity.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}

/-- The actual initial length covector on phase variations is its chart length covector
on the position component. Initial endpoint differentiability follows from the tangent data. -/
theorem initial_lengthMomentum_comp_parameterDeriv
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {Φ : (E × E) → ℝ → M} {t₀ : ℝ}
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z) ⟨t₀, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {z₀ : E × E} (hz₀ : z₀ ∈ chartEnergyDomain old)
    (hc : F.IsEulerLagrangeAt (Φ z₀) t₀) :
    let p₀ := fderiv ℝ
      (fun v : TangentSpace 𝓘(ℝ, E) (Φ z₀ t₀) ↦ (F.toFun ⟨Φ z₀ t₀, v⟩ : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z₀) t₀ 1)
    p₀.comp (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E) (fun z ↦ Φ z t₀) z₀) =
      (fiberLegendre (fun z ↦ (F.chartLength old z : ℝ)) z₀).comp
        (ContinuousLinearMap.fst ℝ E E) := by
  let χ := extChartAt 𝓘(ℝ, E) old
  have hbase (z : E × E) (hz : z ∈ chartEnergyDomain old) :
      Φ z t₀ = χ.symm z.1 := by
    have h := congrArg (fun q : TangentBundle 𝓘(ℝ, E) M ↦ q.1) (hinit z hz)
    rw [tangentChart_symm_eq old hz.1 z.2] at h
    exact h
  have hx : Φ z₀ t₀ ∈ χ.source := by
    rw [hbase z₀ hz₀]
    exact χ.map_target hz₀.1
  have he : (fun z ↦ Φ z t₀) =ᶠ[𝓝 z₀] χ.symm ∘ Prod.fst := by
    filter_upwards [(isOpen_chartEnergyDomain old).mem_nhds hz₀] with z hz
    exact hbase z hz
  have hi : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ χ.symm z₀.1 :=
    (contMDiffOn_extChartAt_symm (n := ∞) old).contMDiffAt
      ((isOpen_extChartAt_target old).mem_nhds hz₀.1)
  have hd : MDifferentiableAt 𝓘(ℝ, E × E) 𝓘(ℝ, E) (fun z ↦ Φ z t₀) z₀ :=
    ((hi.comp z₀ (contDiffAt_fst (𝕜 := ℝ) (n := ∞)).contMDiffAt).mdifferentiableAt
      (by simp)).congr_of_eventuallyEq he
  have hχ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) χ (Φ z₀ t₀) :=
    (contMDiffAt_extChartAt' (n := ∞)
      (by simpa only [χ, extChartAt_source] using hx)).mdifferentiableAt (by simp)
  have hread : χ ∘ (fun z ↦ Φ z t₀) =ᶠ[𝓝 z₀] Prod.fst := by
    filter_upwards [(isOpen_chartEnergyDomain old).mem_nhds hz₀] with z hz
    change χ (Φ z t₀) = z.1
    rw [hbase z hz, χ.right_inv hz.1]
  have hD : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) χ (Φ z₀ t₀)).comp
      (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E) (fun z ↦ Φ z t₀) z₀) =
        ContinuousLinearMap.fst ℝ E E := by
    rw [← mfderiv_comp z₀ hχ hd, hread.mfderiv_eq, mfderiv_eq_fderiv]
    exact hasFDerivAt_fst.fderiv
  have hcurve := (hF.contMDiffAt_of_isEulerLagrangeAt hc).mdifferentiableAt (by simp)
  have hvel : deriv (χ ∘ Φ z₀) t₀ =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) χ (Φ z₀ t₀))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z₀) t₀ 1) := by
    have h := mfderiv_comp_apply t₀ hχ hcurve (1 : ℝ)
    rw [mfderiv_eq_fderiv] at h
    exact h
  have hphase := hF.chartPhase_of_tangent_eq hc old hz₀ (hinit z₀ hz₀)
  have hphase' : (χ (Φ z₀ t₀), (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) χ (Φ z₀ t₀))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z₀) t₀ 1)) = z₀ := by
    rw [← hvel]
    exact hphase
  have hp := hF.chartLength_fderiv_comp_mfderiv old hx
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z₀) t₀ 1) (by
      change (χ (Φ z₀ t₀), _) ∈ chartEnergyDomain old
      rw [hphase']
      exact hz₀)
  rw [hphase'] at hp
  dsimp only
  rw [← hp, ContinuousLinearMap.comp_assoc, hD]

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
