import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11LevelPositionRank
import OTSelector.Geometry.Finsler.C11PotentialFamily
import OTSelector.Geometry.Finsler.C11PotentialTube
import OTSelector.Geometry.Finsler.CalibratedTranslation
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Symplectic.PotentialConormal
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.C11SmoothTubeCore

* **Conditions:** Original potential differential and two calibrated partners on an actual contact core, together with its derived ordinary position comparison.
* **Objects:** Exact central potential clock/isometry and an actual selected smooth tube family, pointwise or almost everywhere.
* **Proof detail:** Identify the actual central complete curve from original covector data, derive its calibrated isometry and invoke same-family smooth tube construction.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11SmoothTubeCore.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11SmoothTubeCore`; the selected original proof blocks follow. -/
section

/-!
# Smooth potential-level tubes from original calibrated core data

The actual original potential differential and two calibrated partners identify the
central complete curve as a distance-preserving segment with its original potential
clock. Together with the ordinary position comparison, these original data construct
one smooth level family admitting calibrated tubes around every compact subinterval.
No central isometry, tube regularity or new family is supplied to the core producer.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

omit [BorelSpace E] in
/-- Original calibrated partners and the actual initial potential differential derive
central isometry and its exact potential clock. The existing selected potential-level
family therefore admits smooth calibrated tubes, without an isometry premise. -/
theorem smoothTubeFamily_of_calibrated_initial_data (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {u : M → ℝ} (hu : let _instTubeCoreLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {m : Measure E} {G : E → ℝ} {K : Set E} {x : E}
    (hxt : x ∈ (extChartAt 𝓘(ℝ, E) old).target)
    {A : E → ℝ → M} (hEL : F.IsEulerLagrangeOn (A x) univ)
    (hinit : A x 0 = (extChartAt 𝓘(ℝ, E) old).symm x)
    (hp : F.chartMomentumFamily old A (x, 0) = (x, fderiv ℝ G x))
    {δ : ℝ} (hδ : 0 < δ) {a b : M}
    (ha : let _instTubeCorePre : MetricSpace M := F.metricSpace
      dist a ((extChartAt 𝓘(ℝ, E) old).symm x) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm x) - u a = δ)
    (hb : let _instTubeCorePost : MetricSpace M := F.metricSpace
      dist ((extChartAt 𝓘(ℝ, E) old).symm x) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) old).symm x) = δ)
    (hx : F.HasC11PotentialFamilyAt m old 0 u G K x)
    (hcmp : F.HasC11LevelPositionComparisonAt old G A δ x) :
    let _instTubeCoreResult : MetricSpace M := F.metricSpace
    (∀ t ∈ Icc (-δ) δ,
      u (A x t) = u ((extChartAt 𝓘(ℝ, E) old).symm x) + t) ∧
      Isometry (fun t : Icc (-δ) δ ↦ A x t) ∧
      F.HasC11SmoothTubeFamilyAt old u G A δ x := by
  let _instTubeCoreProof : MetricSpace M := F.metricSpace
  have hcoord := hx.2.2.1
  have hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u
      ((extChartAt 𝓘(ℝ, E) old).symm x) := by
    have hs : (extChartAt 𝓘(ℝ, E) old).symm x ∈ (chartAt E old).source := by
      simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ, E) old).map_target hxt
    apply (mdifferentiableAt_iff_source_of_mem_source
      (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, ℝ)) hs).2
    simpa only [(extChartAt 𝓘(ℝ, E) old).right_inv hxt,
      modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] using
      hcoord.differentiableAt.mdifferentiableAt
  have hmomentum : F.chartMomentumFamily old A (x, 0) =
      (x, fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) x) :=
    hp.trans (Prod.ext rfl hcoord.fderiv.symm)
  obtain ⟨_, _, _, hclock, hiso, _⟩ :=
    hF.calibrated_translation_of_chartMomentum hcomplete old hu hxt hEL hinit
      hmomentum hdu hδ ha hb
  exact ⟨hclock, hiso, hF.smoothTubeFamily_of_C11PotentialFamily hx hcmp hiso⟩

/-- The same full-measure potential-family set carries smooth calibrated tubes and
the original central potential clock. All rank and isometry data are derived from the
actual compact calibrated core, its C1,1 extension and its complete ambient family. -/
theorem ae_smoothTubeFamily_of_calibrated_C11_core (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {m ν : Measure E} [IsAddHaarMeasure m] (hν : ν ≪ m)
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUt : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : let _instAETubeCoreLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (hinterior : let _instAETubeCoreInterior : MetricSpace M := F.metricSpace
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
    (hpartners : let _instAETubeCorePartners : MetricSpace M := F.metricSpace
      ∀ y ∈ K, ∃ a b : M,
        dist a ((extChartAt 𝓘(ℝ, E) old).symm y) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm y) - u a = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm y) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) old).symm y) = δ) :
    let _instAETubeCoreResult : MetricSpace M := F.metricSpace
    ∀ᵐ x ∂ν.restrict K, F.HasC11PotentialFamilyAt m old 0 u G K x ∧
      F.HasC11LevelPositionComparisonAt old G A δ x ∧
      (∀ t ∈ Icc (-δ) δ,
        u (A x t) = u ((extChartAt 𝓘(ℝ, E) old).symm x) + t) ∧
      Isometry (fun t : Icc (-δ) δ ↦ A x t) ∧
      F.HasC11SmoothTubeFamilyAt old u G A δ x := by
  let _instAETubeCoreProof : MetricSpace M := F.metricSpace
  filter_upwards [hF.ae_levelPositionComparison_of_calibrated_C11_core hcomplete old
    hν hK hU hKU hUt hu hinterior hG hLip hval hactual hEL hinit hp hδ hpartners]
    with x hx
  obtain ⟨a, b, ha, hua, hb, hub⟩ := hpartners x hx.1.1
  exact ⟨hx.1, hx.2, hF.smoothTubeFamily_of_calibrated_initial_data hcomplete old hu
    (hUt (hKU hx.1.1)) (hEL x (hKU hx.1.1)) (hinit x (hKU hx.1.1))
    (hp x (hKU hx.1.1)) hδ ⟨ha, hua⟩ ⟨hb, hub⟩ hx.1 hx.2⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
