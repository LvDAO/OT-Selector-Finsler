import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedCovector
import OTSelector.Geometry.Finsler.CalibratedInterior
import OTSelector.Geometry.Finsler.Coordinates.NormalData
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Manifold.RegularLevelChart
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.C11LevelCoordinates

* **Conditions:** An actual C1,1 contact extension with nonzero original covector forced by calibrated partners.
* **Objects:** C1 implicit level coordinates using that very extension as time coordinate and exact original-potential level images on the core.
* **Proof detail:** Apply the regular level inverse theorem to the actual nonzero extension differential, retain its kernel section and restrict the value-matching identity to the core.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).

Source relation (derived): These are exact coordinate/set identities without density or flow-saturation hypotheses.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11LevelCoordinates.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11LevelCoordinates`; the selected original proof blocks follow. -/
section

/-!
# Actual level coordinates for the original calibrated contact core

The original calibrated partners make the actual extension covector nonzero. Its
C1 implicit coordinates therefore use the given extension itself as first coordinate.
On the original contact core this coordinate equals the original potential, and the
inverse section has exactly the original potential level as its image in that core.
These are coordinate and set identities; no density or flow saturation is assumed.
-/

open Set Metric Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The original calibrated core has actual C1 level coordinates whose first
coordinate is the given extension and agrees with the original potential on the
whole core. The inverse section parametrizes exactly the original level in that
core, without imposing any measure or density condition on its labels. -/
theorem exists_original_levelCoordinates_of_calibrated_core (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {K : Set E} (hKt : K ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : let _instOriginalLevelLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {G : E → ℝ} (hG : ContDiff ℝ 1 G)
    (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) K)
    (hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) K)
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : let _instOriginalLevelPartners : MetricSpace M := F.metricSpace
      ∀ y ∈ K, ∃ a b : M,
        dist a ((extChartAt 𝓘(ℝ, E) old).symm y) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm y) - u a = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm y) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) old).symm y) = δ)
    {x : E} (hx : x ∈ K) :
    let p := fderiv ℝ G x
    p ≠ 0 ∧ ∃ e : OpenPartialHomeomorph E (ℝ × p.ker),
      x ∈ e.source ∧ e.source ⊆ (extChartAt 𝓘(ℝ, E) old).target ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      e x = (u ((extChartAt 𝓘(ℝ, E) old).symm x), 0) ∧
      (∀ y : E, (e y).1 = G y) ∧
      EqOn (fun y ↦ (e y).1) (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) K ∧
      HasFDerivAt (fun w : p.ker ↦ e.symm (G x, w)) p.ker.subtypeL 0 ∧
      Module.finrank ℝ p.ker + 1 = Module.finrank ℝ E ∧
      let σ := fun w : p.ker ↦ e.symm (G x, w)
      let B := {w : p.ker | (G x, w) ∈ e.target}
      IsOpen B ∧ (0 : p.ker) ∈ B ∧ ContDiffOn ℝ 1 σ B ∧ σ 0 = x ∧
      σ '' (B ∩ σ ⁻¹' K) = e.source ∩ K ∩
        {y | u ((extChartAt 𝓘(ℝ, E) old).symm y) =
          u ((extChartAt 𝓘(ℝ, E) old).symm x)} := by
  let _instOriginalLevelMetric : MetricSpace M := F.metricSpace
  obtain ⟨a, b, hax, ha, hxb, hb⟩ := hpartners x hx
  have hinterior : (extChartAt 𝓘(ℝ, E) old).symm x ∈
      OTSelector.Geometry.calibratedInterior u := by
    refine ⟨⟨a, ?_, ha.trans hax.symm⟩, ⟨b, ?_, hb.trans hxb.symm⟩⟩
    · exact dist_pos.mp (hax.symm ▸ hδ)
    · exact dist_pos.mp (hxb.symm ▸ hδ)
  have hd := hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu hinterior
  have hneq : (extChartAt 𝓘(ℝ, E) old).symm x ≠ b :=
    dist_pos.mp (hxb.symm ▸ hδ)
  have hc := hF.exists_chart_unit_legendre_of_calibrated_endpoints hcomplete old
    ((extChartAt 𝓘(ℝ, E) old).map_target (hKt hx)) hu hneq (hb.trans hxb.symm) hd
  obtain ⟨v, hv, hcov, _⟩ := hc
  simp only [(extChartAt 𝓘(ℝ, E) old).right_inv (hKt hx)] at hv hcov
  have hp : fderiv ℝ G x ≠ 0 := by
    intro hzero
    have he := hF.chartEnergy_euler old hv
    rw [hcov, ← hmatch hx, hzero, _root_.zero_apply] at he
    linarith [F.chartEnergy_pos old hv]
  obtain ⟨e, hxe, hsource, he, hei, hex, hfirst, hsection, hdim⟩ :=
    exists_contDiff_levelCoordinates (by rfl : (1 : ℕ∞ω) ≤ 1)
      (isOpen_extChartAt_target old) hG.contDiffOn (hKt hx) hp
  refine ⟨hp, e, hxe, hsource, he, hei, ?_, hfirst, ?_, hsection, hdim, ?_⟩
  · simpa only [hval hx, Function.comp_apply] using hex
  · intro y hy
    exact (hfirst y).trans (hval hy)
  · let σ := fun w : (fderiv ℝ G x).ker ↦ e.symm (G x, w)
    let B := {w : (fderiv ℝ G x).ker | (G x, w) ∈ e.target}
    have h0 : (0 : (fderiv ℝ G x).ker) ∈ B := by
      change (G x, 0) ∈ e.target
      rw [← hex]
      exact e.map_source hxe
    refine ⟨e.open_target.preimage (continuous_const.prodMk continuous_id), h0,
      hei.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hw ↦ hw), ?_, ?_⟩
    · change e.symm (G x, 0) = x
      rw [← hex, e.left_inv hxe]
    · change σ '' (B ∩ σ ⁻¹' K) = _
      ext y
      constructor
      · rintro ⟨w, ⟨hw, hwK⟩, rfl⟩
        have hlevel : G (σ w) = G x := by
          simpa only [hfirst] using congrArg Prod.fst (e.right_inv hw)
        exact ⟨⟨e.map_target hw, hwK⟩,
          (hval hwK).symm.trans (hlevel.trans (hval hx))⟩
      · rintro ⟨⟨hyS, hyK⟩, hlevel⟩
        have hGy : G y = G x := (hval hyK).trans (hlevel.trans (hval hx).symm)
        have hey : e y = (G x, (e y).2) := Prod.ext ((hfirst y).trans hGy) rfl
        have hlabel : (e y).2 ∈ B := by
          change (G x, (e y).2) ∈ e.target
          rw [← hey]
          exact e.map_source hyS
        have hσ : σ (e y).2 = y := by
          change e.symm (G x, (e y).2) = y
          rw [← hey, e.left_inv hyS]
        refine ⟨(e y).2, ⟨hlabel, ?_⟩, hσ⟩
        change σ (e y).2 ∈ K
        rwa [hσ]

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
