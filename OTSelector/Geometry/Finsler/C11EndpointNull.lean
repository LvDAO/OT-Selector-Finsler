import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11FiniteTimeLipschitz
import OTSelector.Geometry.Finsler.C11ScalarAbsoluteContinuity
import OTSelector.Geometry.Finsler.CalibratedInterior
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.HopfRinow
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Geometry.Manifold.ChartLabelClockEmbedding
import OTSelector.Geometry.Manifold.ChartLipschitzNull
import OTSelector.Transport.Calibration.EndpointScalarSection
import OTSelector.Transport.Kantorovich.CalibratedEndpoints
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.C11EndpointNull

* **Conditions:** An actual compact contact core with ordered geometric labels, scalar joint AC and actual finite-time Lipschitz complete-family readouts.
* **Objects:** Zero original chartwise-AC measure of fixed-time backward images of calibrated initial-endpoint slices.
* **Proof detail:** Show each label has at most one clock on the slice, apply product-null Fubini and transfer Haar nullity through the actual Lipschitz readout.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=38): Proposition 262D, p. 11; Corollary 262N, p. 17; Proposition 264G, pp. 38–39; Theorem 264I, pp. 40–41.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11EndpointNull.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11EndpointNull`; the selected original proof blocks follow. -/
section

/-!
# Null original endpoint images of actual C1,1 families

A fixed backward time selects at most one potential value per actual geometric label
on a contact core. Core Haar absolute continuity makes this section Haar null. The
same original complete flow has locally Lipschitz readouts at that backward time,
so the actual endpoint image is null for every chartwise absolutely continuous measure.
-/

open Set Filter Metric Manifold MeasureTheory MeasureTheory.Measure
open OTSelector.Reconstruction
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M}

private theorem measurableSet_endpoint_slice
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    {K : Set X} (hK : MeasurableSet K)
    {φ R : X → Y} (hφ : ContinuousOn φ K) (hR : ContinuousOn R K)
    {u : Y → ℝ} (hu : Continuous u) {N P : Set Y}
    (hN : MeasurableSet N) (hP : MeasurableSet P) (t : ℝ)
    :
    MeasurableSet (K ∩ {x | R x ∈ P ∩ N ∧ u (φ x) - u (R x) = t ∧
      dist (R x) (φ x) = t}) := by
  have hφK := (continuousOn_iff_continuous_domRestrict.mp hφ).measurable
  have hRK := (continuousOn_iff_continuous_domRestrict.mp hR).measurable
  have hm : MeasurableSet {x : K | R x.val ∈ P ∩ N ∧
      u (φ x.val) - u (R x.val) = t ∧ dist (R x.val) (φ x.val) = t} :=
    ((hP.inter hN).preimage hRK).inter
      ((measurableSet_eq_fun ((hu.measurable.comp hφK).sub
        (hu.measurable.comp hRK)) measurable_const).inter
        (measurableSet_eq_fun (hRK.dist hφK) measurable_const))
  have heq : K ∩ {x | R x ∈ P ∩ N ∧ u (φ x) - u (R x) = t ∧
      dist (R x) (φ x) = t} =
      ((↑) : K → X) '' {x : K | R x.val ∈ P ∩ N ∧
        u (φ x.val) - u (R x.val) = t ∧ dist (R x.val) (φ x.val) = t} := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_image, Subtype.exists]
    aesop
  rw [heq]
  exact (MeasurableEmbedding.subtype_coe hK).measurableSet_image.mpr hm

/-- A fixed-time backward endpoint slice in an actual C1,1 contact core has a null
original image. The original flow is retained even beyond its short calibration time. -/
theorem measure_backward_initial_endpoint_image_eq_zero_on_C11_core
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    (m : Measure E) [IsAddHaarMeasure m] (ν : Measure M)
    (hchart : ∀ terminal : M,
      (ν.restrict (extChartAt 𝓘(ℝ, E) terminal).source).map
        (extChartAt 𝓘(ℝ, E) terminal) ≪ m)
    {K B : Set E} (hK : IsCompact K) (hKB : K ⊆ B) (hB : IsOpen B)
    (hBtarget : B ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : let _instEndpointCoreLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    (hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) K)
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : let _instEndpointCorePartners : MetricSpace M := F.metricSpace
      ∀ x ∈ K, ∃ b c : M,
        dist b ((extChartAt 𝓘(ℝ, E) old).symm x) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm x) - u b = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm x) c = δ ∧
        u c - u ((extChartAt 𝓘(ℝ, E) old).symm x) = δ)
    {Γ : E → ℝ → M} (hEL : ∀ x ∈ B, F.IsEulerLagrangeOn (Γ x) univ)
    (hinit : ∀ x ∈ B, Γ x 0 = (extChartAt 𝓘(ℝ, E) old).symm x)
    (hp : ∀ x ∈ B, F.chartMomentumFamily old Γ (x, 0) = (x, fderiv ℝ G x))
    {a : M → Z} (ha : Measurable a)
    (horder : let _instEndpointCoreOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (t : ℝ) :
    let _instEndpointCoreStatement : MetricSpace M := F.metricSpace
    ν ((fun x ↦ Γ x (-t)) '' (K ∩ {x |
      Γ x (-t) ∈ calibratedInitialEndpoints u ∩ F.potentialRegularDomain u ∧
      u ((extChartAt 𝓘(ℝ, E) old).symm x) - u (Γ x (-t)) = t ∧
      dist (Γ x (-t)) ((extChartAt 𝓘(ℝ, E) old).symm x) = t})) = 0 := by
  let _instEndpointCoreMetric : MetricSpace M := F.metricSpace
  let _instEndpointCoreProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let χ := extChartAt 𝓘(ℝ, E) old
  let R : E → M := fun x ↦ Γ x (-t)
  let N := F.potentialRegularDomain u
  let S := K ∩ {x | R x ∈ calibratedInitialEndpoints u ∩ N ∧
    u (χ.symm x) - u (R x) = t ∧ dist (R x) (χ.symm x) = t}
  have hKtarget : K ⊆ χ.target := hKB.trans hBtarget
  have hφ : ContinuousOn χ.symm K := (continuousOn_extChartAt_symm old).mono hKtarget
  have hR : ContinuousOn R B := hF.continuousOn_of_C11_initial_momentum
    hcomplete old hG hLip hB hBtarget hEL hinit hp (-t)
  have hS : MeasurableSet S := measurableSet_endpoint_slice hK.measurableSet hφ
    (hR.mono hKB) hu.continuous (hF.measurableSet_potentialRegularDomain hcomplete u)
    (F.measurableSet_calibratedInitialEndpoints hcomplete hu) t
  have hcore : ∀ x ∈ K, χ.symm x ∈ calibratedInterior u := by
    intro x hx
    obtain ⟨b, c, hbx, hb, hxc, hc⟩ := hpartners x hx
    exact ⟨⟨b, dist_pos.mp (hbx.symm ▸ hδ), hb.trans hbx.symm⟩,
      ⟨c, dist_pos.mp (hxc.symm ▸ hδ), hc.trans hxc.symm⟩⟩
  have hKN : MapsTo χ.symm K N := fun x hx ↦
    hF.mem_potentialRegularDomain_of_mem_calibratedInterior hcomplete hu (hcore x hx)
  have hinj : Function.Injective (fun x : N ↦ (a x.val, u x.val)) := by
    intro x y he
    apply Subtype.ext
    have hl := congrArg Prod.fst he
    have ht : u x.val = u y.val := congrArg Prod.snd he
    have hs := (horder x.val x.property y.val y.property).mp ⟨hl, le_of_eq ht⟩
    exact dist_eq_zero.mp (by rw [← hs, ht, sub_self])
  have hemb := measurableEmbedding_chart_labelClock old hK.measurableSet hKtarget
    (hF.measurableSet_potentialRegularDomain hcomplete u) hKN ha hu.continuous.measurable hinj
  have hinv : ∀ x ∈ calibratedInterior u, ∀ y ∈ calibratedInterior u,
      |u y - u x| = dist x y → a y = a x := by
    intro x hx y hy hcal
    have hxr := hF.mem_potentialRegularDomain_of_mem_calibratedInterior hcomplete hu hx
    have hyr := hF.mem_potentialRegularDomain_of_mem_calibratedInterior hcomplete hu hy
    rcases le_total (u x) (u y) with hxy | hyx
    · exact ((horder x hxr y hyr).mpr
        (by simpa only [abs_of_nonneg (sub_nonneg.mpr hxy)] using hcal)).1.symm
    · exact ((horder y hyr x hxr).mpr
        (by simpa only [abs_sub_comm (u y) (u x),
          abs_of_nonneg (sub_nonneg.mpr hyx), dist_comm x y] using hcal)).1
  have hjoint := hF.map_label_potential_absolutelyContinuous_on_C11_core
    hcomplete old m m Measure.AbsolutelyContinuous.rfl hK hKtarget hu hG hLip hmatch
    hδ hpartners ha hinv
  have hi : AEMeasurable χ.symm (m.restrict K) := hφ.aemeasurable hK.measurableSet
  have hz : (m.restrict K) S = 0 := by
    apply measure_eq_zero_of_backward_initial_endpoint_section (m.restrict K)
      (ha.comp_aemeasurable hi) (hu.continuous.measurable.comp_aemeasurable hi)
      hjoint hS inter_subset_left hemb horder
    · intro x hx
      exact hF.mem_potentialRegularDomain_of_mem_calibratedInterior hcomplete hu (hcore x hx.1)
    · intro x hx
      exact hx.2.1
    · intro x hx
      exact hx.2.2.1
    · intro x hx
      exact hx.2.2.1.trans hx.2.2.2.symm
  have hmS : m S = 0 := by
    have hSK : S ⊆ K := inter_subset_left
    simpa only [Measure.restrict_apply hS, inter_eq_left.mpr hSK] using hz
  apply measure_image_eq_zero_of_locally_chart_lipschitz m ν hchart hmS
  intro x hx
  obtain ⟨r, C, hr, _, hlegal, hread⟩ :=
    hF.exists_lipschitz_chart_readout_of_C11_initial_momentum hcomplete old hG hLip
      hB hBtarget hEL hinit hp (hKB hx.1) (R x) (-t) (mem_extChartAt_source (R x))
  exact ⟨r, C, R x, hr, hlegal, hread⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
