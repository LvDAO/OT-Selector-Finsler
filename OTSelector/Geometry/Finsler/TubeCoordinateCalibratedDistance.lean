import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.EndpointInverse
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Uniqueness
import OTSelector.Geometry.Finsler.LengthHessian
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.TubeCoordinateDistance
import OTSelector.Geometry.Finsler.TubeCoordinateEndpoint
import OTSelector.Geometry.Manifold.ManifoldFlowTimePotential

/-!
# Geometry.Finsler.TubeCoordinateCalibratedDistance

* **Conditions:** A genuine calibrated unit-speed manifold tube and the original globally minimizing saturated central branch.
* **Objects:** Smooth original distance in actual tube coordinates and its intrinsic endpoint first variation.
* **Proof detail:** Derive endpoint invertibility from the actual calibrated tube and feed that result into the already proved original-distance branch theorem.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [J. C. Álvarez Paiva; A. C. Thompson, Volumes on Normed and Finsler Spaces, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/02AT.pdf#page=22): Section 4.2, Definition 4.11 and Proposition 4.12, p. 22.

Source relation (derived): Second-order compliance is separate; this closes the internal nonconjugacy input for the first-order distance branch.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerTubeCoordinateCalibratedDistance.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerTubeCoordinateCalibratedDistance`; the selected original proof blocks follow. -/
section

/-!
# Original distance regularity on an actual calibrated tube

The genuine calibrated unit-speed tube proves invertibility of the original complete
family's endpoint differential. Feeding that proved result into the original minimizing
distance branch gives actual distance smoothness and its intrinsic first variation in Y.
No endpoint nonconjugacy, coordinate velocity, Hessian-block or initial-rank premise remains.
The globally minimizing saturated branch is retained, and second-order compliance is separate.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- The original globally minimizing distance is smooth in the genuine calibrated tube,
with value equal to elapsed time and the original intrinsic endpoint momentum first jet.
The tube itself proves full endpoint nonconjugacy; no such hypothesis is supplied. -/
theorem tubeCoordinateDistance_smooth_of_calibrated_manifoldTube
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (initial terminal : M)
    {Y : OpenPartialHomeomorph (ℝ × W) M} {Λ : W → ℝ → M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target)
    (heq : (Y : ℝ × W → M) = fun q ↦ Λ q.2 q.1)
    (hhalf : ∀ q ∈ Y.source,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2)
    (t₀ : ℝ)
    (hbound : ∀ x ∈ Y.target, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 t₀) x v)
        (F.toFun ⟨x, v⟩ : ℝ))
    {a b : ℝ} (hab : a < b) {Γ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain initial, F.IsEulerLagrangeOn (Γ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain initial,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {z : E × E} (hz : z ∈ chartEnergyDomain initial) {w : W}
    (hΛ : F.IsEulerLagrangeOn (Λ w) univ)
    (hseed : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ w) ⟨a, (1 : ℝ)⟩ =
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hstay : ∀ t ∈ Icc a b, (t, w) ∈ Y.source)
    (hterminal : Λ w b ∈ (extChartAt 𝓘(ℝ, E) terminal).source)
    (hmin : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      F.lengthEDist (Γ z a) (Γ z b) = Manifold.pathELength 𝓘(ℝ, E) (Γ z) a b)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hsat : letI : MetricSpace M := F.metricSpace
      u (Γ z b) - u (Γ z a) = dist (Γ z a) (Γ z b))
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (Γ z a)) :
    let qa : ℝ × W := (a, w)
    let qb : ℝ × W := (b, w)
    let p : (t : ℝ) → TangentSpace 𝓘(ℝ, E) (Γ z t) →L[ℝ] ℝ := fun t ↦
      fderiv ℝ (fun v : TangentSpace 𝓘(ℝ, E) (Γ z t) ↦
        (F.toFun ⟨Γ z t, v⟩ : ℝ)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) t 1)
    ContDiffAt ℝ ∞ (F.tubeCoordinateDistance Y) (qa, qb) ∧
      F.tubeCoordinateDistance Y (qa, qb) = b - a ∧
      HasFDerivAt (F.tubeCoordinateDistance Y)
        ((p b).comp (mfderiv 𝓘(ℝ, (ℝ × W) × (ℝ × W)) 𝓘(ℝ, E)
          (fun q ↦ Y q.2) (qa, qb)) -
        (p a).comp (mfderiv 𝓘(ℝ, (ℝ × W) × (ℝ × W)) 𝓘(ℝ, E)
          (fun q ↦ Y q.1) (qa, qb))) (qa, qb) := by
  have hsame : Γ z = Λ w := by
    funext t
    exact hF.eqOn_of_isEulerLagrangeOn isOpen_univ isPreconnected_univ
      (hEL z hz) hΛ (mem_univ a) ((hinit z hz).trans hseed.symm) (mem_univ t)
  have hYval (t : ℝ) : Y (t, w) = Γ z t := (congrFun heq (t, w)).trans
    (congrFun hsame t).symm
  have hinv := hF.isInvertible_chartEndpointMap_of_calibrated_manifoldTube
    initial terminal hY hi heq hhalf t₀ hbound hab hEL hinit hz hΛ hseed hstay hterminal
  have hx : Γ z b ∈ (extChartAt 𝓘(ℝ, E) terminal).source := by
    simpa only [hsame] using hterminal
  have henergy : F.chartEnergy initial z = 1 / 2 :=
    (congrArg F.energy hseed).symm.trans (hhalf (a, w) (hstay a (left_mem_Icc.mpr hab.le)))
  have hunit : (F.chartLength initial z : ℝ) = 1 := by
    rw [F.chartLength_eq_sqrt_energy, henergy]
    norm_num
  have h := hF.tubeCoordinateDistance_smooth_of_nonconjugate hcomplete initial terminal
    hab hEL hinit hz hmin hu hsat hdu hx hinv Y hY
    (hstay a (left_mem_Icc.mpr hab.le)) (hstay b (right_mem_Icc.mpr hab.le))
    (hYval a) (hYval b)
  simpa only [hunit, one_mul] using h

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
