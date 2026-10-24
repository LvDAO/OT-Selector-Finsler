import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11PositionRank
import OTSelector.Geometry.Finsler.C11PotentialFamily
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialLevelPositionRank
import OTSelector.Geometry.Symplectic.PotentialConormal
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.C11LevelPositionRank

* **Conditions:** Actual C1,1 potential-family good points with ambient density one and extension Hessian, plus the stated complete ambient family on a calibrated reach.
* **Objects:** Ordinary position comparison for every complete family with the same normalized initial phase jet, on one AE good set.
* **Proof detail:** Construct the ambient lower derivative bound, apply ordinary same-jet matching and restrict it to the true level kernel while retaining selected family witnesses.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=22): Theorem 472D, pp. 22–23 (Besicovitch Density Theorem).
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=39): Section 4.3, Lemma 4.21(i)–(iii), p. 39, and proof pp. 40–42.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11LevelPositionRank.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11LevelPositionRank`; the selected original proof blocks follow. -/
section

/-!
# Ordinary position comparison for every matched complete level family

The original potential-family good points already carry ambient density one and the
actual extension Hessian. The constructed ambient position lower bound therefore
controls every complete family with the same ordinary initial phase jet. The existing
potential-level witnesses are retained, and one good set works for every such family,
all legal charts and all times strictly inside the calibrated reach.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- Every actual complete family with the normalized initial phase jet has the
ambient position derivative restricted to the original covector kernel, with a positive
lower norm bound. This property preserves any previously constructed level family. -/
def HasC11LevelPositionComparisonAt (F : ContinuousFinslerNorm E M) (old : M)
    (G : E → ℝ) (A : E → ℝ → M) (δ : ℝ) (x : E) : Prop :=
  let p := fderiv ℝ G x
  let H := fderiv ℝ (fderiv ℝ G) x
  ∀ (B : Set p.ker) (Γ : p.ker → ℝ → M), IsOpen B → (0 : p.ker) ∈ B →
    (∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ) →
    (∀ w ∈ B, Γ w 0 ∈ (extChartAt 𝓘(ℝ, E) old).source) →
    HasFDerivAt (fun w ↦ F.chartMomentumFamily old Γ (w, 0))
      (p.ker.subtypeL.prod (H.comp p.ker.subtypeL)) 0 →
    F.chartMomentumFamily old Γ (0, 0) = (x, p) →
    A x = Γ 0 ∧ ∀ (terminal : M) (t : ℝ), |t| < δ →
      Γ 0 t ∈ (extChartAt 𝓘(ℝ, E) terminal).source →
      fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) terminal (Γ w t)) 0 =
        (fderiv ℝ (fun y ↦ extChartAt 𝓘(ℝ, E) terminal (A y t)) x).comp
          p.ker.subtypeL ∧
      HasFDerivAt (fun w ↦ extChartAt 𝓘(ℝ, E) terminal (Γ w t))
        ((fderiv ℝ (fun y ↦ extChartAt 𝓘(ℝ, E) terminal (A y t)) x).comp
          p.ker.subtypeL) 0 ∧
      ∃ c : ℝ, 0 < c ∧
        (∀ w : p.ker, c * ‖w‖ ≤
          ‖fderiv ℝ (fun z ↦ extChartAt 𝓘(ℝ, E) terminal (Γ z t)) 0 w‖) ∧
        Function.Injective
          (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) terminal (Γ w t)) 0)

namespace IsSmoothStronglyConvex
variable [T2Space M] [PreconnectedSpace M]

/-- The existing potential-family good point supplies exactly the density and Hessian
needed for the ambient geometric lower bound. Ordinary initial jets then pass that bound
to every matching complete family, including the already constructed level witnesses. -/
theorem levelPositionComparison_of_C11PotentialFamily (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {m : Measure E} [IsAddHaarMeasure m]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUt : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : let _instLevelPositionLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    (hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) K)
    {A : E → ℝ → M} (hEL : ∀ y ∈ U, F.IsEulerLagrangeOn (A y) univ)
    (hinit : ∀ y ∈ U, A y 0 = (extChartAt 𝓘(ℝ, E) old).symm y)
    (hp : ∀ y ∈ U, F.chartMomentumFamily old A (y, 0) = (y, fderiv ℝ G y))
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : let _instLevelPositionPartners : MetricSpace M := F.metricSpace
      ∀ y ∈ K, ∃ a b : M,
        dist a ((extChartAt 𝓘(ℝ, E) old).symm y) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm y) - u a = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm y) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) old).symm y) = δ)
    {x : E} (hx : F.HasC11PotentialFamilyAt m old 0 u G K x) :
    F.HasC11LevelPositionComparisonAt old G A δ x := by
  intro B Γ hB h0 hΓEL hsource hjet hvalue
  have hσ : HasFDerivAt (fun w : (fderiv ℝ G x).ker ↦ x + (w : E))
      (fderiv ℝ G x).ker.subtypeL 0 := by
    exact (fderiv ℝ G x).ker.subtypeL.hasFDerivAt.const_add x
  apply hF.potentialLevel_position_rank_of_initial_phase_jet hcomplete old hU hUt
    hEL hinit hp (hKU hx.1) hx.2.2.2.1 (by simp) hσ hB h0 hΓEL hsource hjet hvalue
  intro terminal t ht hlegal
  exact hF.exists_pos_fderiv_lower_bound_of_calibrated_C11_translation hcomplete old
    terminal m hK hU hKU hUt hu hG hLip hmatch hEL hinit hp hδ hpartners hx.1
    hx.2.1 hx.2.2.2.1.differentiableAt ht hlegal

/-- One full-measure set retains the actual potential-level family and controls every
complete family with its ordinary initial phase jet. All geometric lower bounds are
derived from the original calibrated core; no rank premise is supplied. -/
theorem ae_levelPositionComparison_of_calibrated_C11_core (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {m ν : Measure E} [IsAddHaarMeasure m] (hν : ν ≪ m)
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUt : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : let _instAELevelPositionLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (hinterior : let _instAELevelPositionInterior : MetricSpace M := F.metricSpace
      MapsTo (extChartAt 𝓘(ℝ, E) old).symm K (OTSelector.Geometry.calibratedInterior u))
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) K)
    (hactual : ∀ x ∈ K,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G x) x)
    {A : E → ℝ → M} (hEL : ∀ y ∈ U, F.IsEulerLagrangeOn (A y) univ)
    (hinit : ∀ y ∈ U, A y 0 = (extChartAt 𝓘(ℝ, E) old).symm y)
    (hp : ∀ y ∈ U, F.chartMomentumFamily old A (y, 0) = (y, fderiv ℝ G y))
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : let _instAELevelPositionPartners : MetricSpace M := F.metricSpace
      ∀ y ∈ K, ∃ a b : M,
        dist a ((extChartAt 𝓘(ℝ, E) old).symm y) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm y) - u a = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm y) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) old).symm y) = δ) :
    ∀ᵐ x ∂ν.restrict K, F.HasC11PotentialFamilyAt m old 0 u G K x ∧
      F.HasC11LevelPositionComparisonAt old G A δ x := by
  filter_upwards [hF.ae_complete_potentialFamily_of_calibrated_C11_core hcomplete old 0
    hν hK (hKU.trans hUt) hu hinterior hG hLip hval hactual] with x hx
  exact ⟨hx, hF.levelPositionComparison_of_C11PotentialFamily hcomplete old hK hU hKU hUt
    hu hG hLip (fun y hy ↦ (hactual y hy).fderiv.symm) hEL hinit hp hδ hpartners hx⟩

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
