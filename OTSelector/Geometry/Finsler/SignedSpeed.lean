import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.ConstantSpeedDistance
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Energy
import OTSelector.Geometry.Finsler.TubeCoordinateFirstVariation

/-!
# Geometry.Finsler.SignedSpeed

* **Conditions:** The actual complete prescribed tangent family and any two ordered or reversed real times.
* **Objects:** Frechet first variation of signed elapsed time times original speed as actual endpoint length-momentum pairings.
* **Proof detail:** Evaluate original constant-speed lengths for each time order, apply across-chart endpoint first variation and reverse the sign when time order reverses.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerSignedSpeed.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerSignedSpeed`; the selected original proof blocks follow. -/
section

/-!
# Signed speed first variation for the actual complete family

The original constant speed evaluates every ordered path length. Across-chart
first variation and reversal of the time order give one endpoint derivative identity
for signed elapsed time, retaining the actual prescribed initial tangent family.
-/

open Set Filter Manifold
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}

/-- For the actual complete initial-tangent family, signed elapsed time times the
original chart speed has derivative equal to terminal minus initial length momentum.
The identity holds in both time directions without a minimizing or unit-speed premise. -/
theorem hasFDerivAt_signed_speed_of_complete_tangentFamily
    (hF : F.IsSmoothStronglyConvex) (old : M) (t₀ : ℝ)
    {Phi : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Phi z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi z) ⟨t₀, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hC2 : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ)
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {z₀ : E × E} (hz₀ : z₀ ∈ chartEnergyDomain old) (t : ℝ) :
    let p : (r : ℝ) → TangentSpace 𝓘(ℝ, E) (Phi z₀ r) →L[ℝ] ℝ := fun r ↦
      fderiv ℝ (fun v : TangentSpace 𝓘(ℝ, E) (Phi z₀ r) ↦
        (F.toFun ⟨Phi z₀ r, v⟩ : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi z₀) r 1)
    HasFDerivAt (fun z ↦ (t - t₀) * (F.chartLength old z : ℝ))
      ((p t).comp (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E) (fun z ↦ Phi z t) z₀) -
        (p t₀).comp (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E) (fun z ↦ Phi z t₀) z₀)) z₀
 := by
  let _instSignedSpeedENorm : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  have hspeed (z : E × E) (hz : z ∈ chartEnergyDomain old) (r : ℝ) :
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi z) ⟨r, (1 : ℝ)⟩) =
        F.chartLength old z := by
    rw [hF.speed_eq_of_isEulerLagrangeOn (hEL z hz) isPreconnected_univ
      (mem_univ r) (mem_univ t₀), hinit z hz]
    rfl
  have hlength (a b : ℝ) (hab : a ≤ b) :
      (fun z ↦ (pathELength 𝓘(ℝ, E) (Phi z) a b).toReal) =ᶠ[𝓝 z₀]
        (fun z ↦ (b - a) * (F.chartLength old z : ℝ)) := by
    filter_upwards [(isOpen_chartEnergyDomain old).mem_nhds hz₀] with z hz
    rw [F.pathELength_eq_of_constant_speed (fun r _ ↦ hspeed z hz r),
      ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab), mul_comm]
  rcases le_total t₀ t with hforward | hbackward
  · have hd := hF.hasFDerivAt_family_pathELength_mfderiv_across_charts
      (isOpen_chartEnergyDomain old) isOpen_univ hC2 hz₀ hforward
      (subset_univ _) (hEL z₀ hz₀)
    exact hd.congr_of_eventuallyEq (hlength t₀ t hforward).symm
  · have hd := hF.hasFDerivAt_family_pathELength_mfderiv_across_charts
      (isOpen_chartEnergyDomain old) isOpen_univ hC2 hz₀ hbackward
      (subset_univ _) (hEL z₀ hz₀)
    have h := hd.congr_of_eventuallyEq (hlength t t₀ hbackward).symm
    have hn := h.neg
    have hf : -(fun z : E × E ↦ (t₀ - t) * (F.chartLength old z : ℝ)) =
        (fun z ↦ (t - t₀) * (F.chartLength old z : ℝ)) := by
      funext z
      dsimp
      ring
    rw [hf, neg_sub] at hn
    exact hn

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
