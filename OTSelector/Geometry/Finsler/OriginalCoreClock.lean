import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Calibration.PhaseIsometry
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerOriginalCoreClock.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerOriginalCoreClock`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.OriginalCoreClock

* **Conditions:** An original C1,1 core agreeing with the potential/covector, a supplied inverse Legendre branch and complete family, and two calibrated partners at a common positive reach.
* **Objects:** Unit actual energy, original potential clock, isometry and exact ordered distance throughout that same closed core interval.
* **Proof detail:** Identify the true initial inverse-covector state with the calibrated unit curve, retain its common clock and convert the resulting isometry to ordered distance.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.

Source relation (derived): All four conclusions concern the given family and branch; no independent unit normalization is substituted.
-/

/-!
# Unit energy and the original potential clock on a calibrated core

The actual coordinate differential and two calibrated partners determine unit
speed on the same inverse Legendre branch. The original potential then increases
by elapsed time along the prescribed complete curves.
-/

open Set Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The same actual calibrated core gives unit energy, its original clock, and
distance preservation on each whole closed trimmed curve. -/
theorem original_core_unit_energy_clock_and_isometry (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {u : M → ℝ} (hu : let _instCoreClockLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {C : Set E} (hCt : C ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {G : E → ℝ} (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) C)
    (hactual : ∀ y ∈ C,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G y) y)
    {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Φ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hlegal : ∀ y ∈ C, (y, fderiv ℝ G y) ∈ eL.target)
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : let _instCoreClockPartners : MetricSpace M := F.metricSpace
      ∀ y ∈ C, ∃ l r : M,
        dist l ((extChartAt 𝓘(ℝ, E) old).symm y) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm y) - u l = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm y) r = δ ∧
        u r - u ((extChartAt 𝓘(ℝ, E) old).symm y) = δ) :
    let _instCoreIsometryResult : MetricSpace M := F.metricSpace
    ∀ y ∈ C, let z := eL.symm (y, fderiv ℝ G y)
      (F.chartLength old z : ℝ) = 1 ∧ F.chartEnergy old z = 1 / 2 ∧
        (∀ t ∈ Icc (-δ) δ, u (Φ z t) = G y + t) ∧
        Isometry (fun t : Icc (-δ) δ ↦ Φ z t) := by
  let _instCoreClockMetric : MetricSpace M := F.metricSpace
  dsimp only
  intro y hy
  have hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u
      ((extChartAt 𝓘(ℝ, E) old).symm y) := by
    have hs : (extChartAt 𝓘(ℝ, E) old).symm y ∈ (chartAt E old).source := by
      simpa only [extChartAt_source] using
        (extChartAt 𝓘(ℝ, E) old).map_target (hCt hy)
    apply (mdifferentiableAt_iff_source_of_mem_source
      (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, ℝ)) hs).2
    simpa only [(extChartAt 𝓘(ℝ, E) old).right_inv (hCt hy),
      modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] using
      (hactual y hy).differentiableAt.mdifferentiableAt
  have hgrad := (hactual y hy).fderiv
  have htarget : (y, fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) y) ∈
      eL.target := by simpa only [hgrad] using hlegal y hy
  obtain ⟨l, r, hl, hul, hr, hur⟩ := hpartners y hy
  have hdata := hF.calibrated_phase_isometry_data_of_original_covector hcomplete old hu
    hEL hinit heL hsource htarget hdu hδ ⟨hl, hul⟩ ⟨hr, hur⟩
  rw [hgrad] at hdata
  refine ⟨hdata.1, ?_, ?_, hdata.2.2⟩
  · rw [F.chartEnergy_eq_chartLength_sq, hdata.1]
    norm_num
  · intro t ht
    have hvalue : u ((extChartAt 𝓘(ℝ, E) old).symm y) = G y := (hval hy).symm
    simpa only [hvalue] using hdata.2.1 t ht

/-- Actual original covectors on a calibrated core give unit chart length,
half energy, and the exact original potential clock on the same supplied flow. -/
theorem original_core_unit_energy_and_clock (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {u : M → ℝ} (hu : let _instCoreClockLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {C : Set E} (hCt : C ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {G : E → ℝ} (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) C)
    (hactual : ∀ y ∈ C,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G y) y)
    {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Φ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hlegal : ∀ y ∈ C, (y, fderiv ℝ G y) ∈ eL.target)
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : let _instCoreClockPartners : MetricSpace M := F.metricSpace
      ∀ y ∈ C, ∃ l r : M,
        dist l ((extChartAt 𝓘(ℝ, E) old).symm y) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm y) - u l = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm y) r = δ ∧
        u r - u ((extChartAt 𝓘(ℝ, E) old).symm y) = δ) :
    ∀ y ∈ C, let z := eL.symm (y, fderiv ℝ G y)
      (F.chartLength old z : ℝ) = 1 ∧ F.chartEnergy old z = 1 / 2 ∧
        ∀ t ∈ Icc (-δ) δ, u (Φ z t) = G y + t := by
  have hdata := hF.original_core_unit_energy_clock_and_isometry hcomplete old hu
    hCt hval hactual hEL hinit heL hsource hlegal hδ hpartners
  intro y hy
  exact ⟨(hdata y hy).1, (hdata y hy).2.1, (hdata y hy).2.2.1⟩

/-- Each original core curve preserves the actual Finsler length distance on its
whole closed calibrated interval. -/
theorem original_core_isometry (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {u : M → ℝ} (hu : let _instCoreClockLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {C : Set E} (hCt : C ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {G : E → ℝ} (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) C)
    (hactual : ∀ y ∈ C,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G y) y)
    {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Φ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hlegal : ∀ y ∈ C, (y, fderiv ℝ G y) ∈ eL.target)
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : let _instCoreClockPartners : MetricSpace M := F.metricSpace
      ∀ y ∈ C, ∃ l r : M,
        dist l ((extChartAt 𝓘(ℝ, E) old).symm y) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm y) - u l = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm y) r = δ ∧
        u r - u ((extChartAt 𝓘(ℝ, E) old).symm y) = δ) :
    let _instCoreIsometryResult : MetricSpace M := F.metricSpace
    ∀ y ∈ C, Isometry (fun t : Icc (-δ) δ ↦ Φ (eL.symm (y, fderiv ℝ G y)) t) := by
  have hdata := hF.original_core_unit_energy_clock_and_isometry hcomplete old hu
    hCt hval hactual hEL hinit heL hsource hlegal hδ hpartners
  exact fun y hy ↦ (hdata y hy).2.2.2

/-- Ordered times on each original calibrated core curve have actual length
distance equal to their elapsed time. -/
theorem original_core_ordered_distance (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {u : M → ℝ} (hu : let _instCoreClockLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {C : Set E} (hCt : C ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {G : E → ℝ} (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) C)
    (hactual : ∀ y ∈ C,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G y) y)
    {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Φ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hlegal : ∀ y ∈ C, (y, fderiv ℝ G y) ∈ eL.target)
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : let _instCoreClockPartners : MetricSpace M := F.metricSpace
      ∀ y ∈ C, ∃ l r : M,
        dist l ((extChartAt 𝓘(ℝ, E) old).symm y) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm y) - u l = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm y) r = δ ∧
        u r - u ((extChartAt 𝓘(ℝ, E) old).symm y) = δ) :
    ∀ y ∈ C, ∀ a ∈ Icc (-δ) δ, ∀ b ∈ Icc (-δ) δ, a ≤ b →
      (F.lengthEDist (Φ (eL.symm (y, fderiv ℝ G y)) a)
        (Φ (eL.symm (y, fderiv ℝ G y)) b)).toReal = b - a := by
  let _instCoreDistanceMetric : MetricSpace M := F.metricSpace
  have hiso := hF.original_core_isometry hcomplete old hu
    hCt hval hactual hEL hinit heL hsource hlegal hδ hpartners
  intro y hy a ha b hb hab
  have hd := (hiso y hy).dist_eq ⟨a, ha⟩ ⟨b, hb⟩
  change (F.lengthEDist (Φ (eL.symm (y, fderiv ℝ G y)) a)
    (Φ (eL.symm (y, fderiv ℝ G y)) b)).toReal = dist a b at hd
  simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab), neg_sub] using hd

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
