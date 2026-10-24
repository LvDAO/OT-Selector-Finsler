import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11EndpointNull
import OTSelector.Geometry.Finsler.C11FamilyCover
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.InitialEndpointCover
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Geometry.Finsler.PotentialNegation
import OTSelector.Geometry.Finsler.PotentialRegularMass
import OTSelector.Geometry.Finsler.Rademacher
import OTSelector.Transport.Kantorovich.CalibratedEndpoints
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.EndpointNull

* **Conditions:** The actual countable C1,1 families, ordered labels and an original chartwise absolutely continuous measure.
* **Objects:** Zero measure of both genuine calibrated initial and terminal endpoint sets.
* **Proof detail:** Cover regular endpoints by rational null backward images, remove nonregular exceptions with Rademacher and apply potential reversal for terminal endpoints.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=38): Proposition 262D, p. 11; Corollary 262N, p. 17; Proposition 264G, pp. 38–39; Theorem 264I, pp. 40–41.

Source relation (derived): The endpoint nullity is proved through actual core maps rather than assumed from the geometric reference.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerEndpointNull.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerEndpointNull`; the selected original proof blocks follow. -/
section

/-!
# Original volume nullity of genuine calibrated endpoints

The constructed countable C1,1 families cover every regular initial endpoint by
rational backward-time images of scalar-null interior sections. Actual finite-time
Lipschitz readouts preserve their Haar-nullity, and original chartwise absolute
continuity gives endpoint nullity. Rademacher removes nonregular endpoints. Reversing
the original potential proves terminal endpoint nullity with the same labels.
-/

open Set Filter Metric Manifold MeasureTheory MeasureTheory.Measure
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M}

/-- Genuine initial endpoints of the original calibration are null for every
chartwise absolutely continuous measure. All covering families and volume estimates
are constructed; the labels use the original ordered calibration relation. -/
theorem measure_calibratedInitialEndpoints_eq_zero (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [IsAddHaarMeasure m] (ν : Measure M)
    (hchart : ∀ old : M,
      (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {u : M → ℝ} (hu : let _instInitialNullLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) {a : M → Z} (ha : Measurable a)
    (horder : let _instInitialNullOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y) :
    let _instInitialNullStatement : MetricSpace M := F.metricSpace
    ν (calibratedInitialEndpoints u) = 0 := by
  let _instInitialNullMetric : MetricSpace M := F.metricSpace
  obtain ⟨ι, hcount, old, K, U, G, L, δ, B, Γ, hdata, hcover, hreach, hfamily⟩ :=
    hF.exists_countable_calibrated_C11_family_cover hcomplete hu
  let _instInitialNullCountable : Countable ι := hcount
  have hcov := hF.calibratedInitialEndpoints_regular_subset_iUnion_backward hcomplete hu
    old K Γ (fun i ↦ (hdata i).2.1) (by rw [hcover]) (by
      intro i x hx
      obtain ⟨hinit, hEL, _, hp⟩ := (hfamily i).2.2.2 x ((hfamily i).2.1 hx)
      refine ⟨hEL, hinit, ?_⟩
      rw [hp, (hdata i).2.2.2.2.2.2.1 hx])
  have hnull : ν (calibratedInitialEndpoints u ∩ F.potentialRegularDomain u) = 0 := by
    apply measure_mono_null hcov
    apply (measure_iUnion_null_iff).mpr
    intro i
    apply (measure_iUnion_null_iff).mpr
    intro q
    obtain ⟨hK, _, hG, _, hLip, _, hmatch, _⟩ := hdata i
    obtain ⟨hU, hKU, hUt, hfam⟩ := hfamily i
    apply hF.measure_backward_initial_endpoint_image_eq_zero_on_C11_core
      hcomplete (old i) m ν hchart hK hKU hU hUt hu hG hLip hmatch (hreach i).1
      (Γ := Γ i) ?_ (fun x hx ↦ (hfam x hx).2.1) (fun x hx ↦ (hfam x hx).1)
      (fun x hx ↦ (hfam x hx).2.2.2) ha horder (q : ℝ)
    dsimp only
    intro x hx
    obtain ⟨b, _, c, _, hb, hub, hc, huc⟩ := (hreach i).2.2 x hx
    exact ⟨b, c, hb, hub, hc, huc⟩
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [F.ae_mdifferentiableAt_scalar_of_lipschitz_of_complete m ν
    hcomplete hchart hu, measure_eq_zero_iff_ae_notMem.mp hnull] with x hdx hx
  intro he
  obtain ⟨y, hxy, hsat⟩ := he.1
  exact hx ⟨he, hF.mem_potentialRegularDomain_of_calibrated_partner
    hcomplete hu hxy (.inl hsat) hdx⟩

/-- Genuine terminal endpoints are also null for the original measure. Potential
negation preserves the actual regular domain and reverses the same ordered labels. -/
theorem measure_calibratedTerminalEndpoints_eq_zero (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [IsAddHaarMeasure m] (ν : Measure M)
    (hchart : ∀ old : M,
      (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {u : M → ℝ} (hu : let _instTerminalNullLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) {a : M → Z} (ha : Measurable a)
    (horder : let _instTerminalNullOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y) :
    let _instTerminalNullStatement : MetricSpace M := F.metricSpace
    ν (calibratedTerminalEndpoints u) = 0 := by
  let _instTerminalNullMetric : MetricSpace M := F.metricSpace
  dsimp only
  rw [calibratedTerminalEndpoints_eq_initial_neg]
  apply hF.measure_calibratedInitialEndpoints_eq_zero hcomplete m ν hchart hu.neg ha
  dsimp only
  rw [F.potentialRegularDomain_neg]
  intro x hx y hy
  constructor
  · rintro ⟨he, hle⟩
    have hs := (horder y hy x hx).mp ⟨he.symm, neg_le_neg_iff.mp hle⟩
    simpa only [Pi.neg_apply, neg_sub_neg, dist_comm x y] using hs
  · intro hs
    have hh := (horder y hy x hx).mpr
      (by simpa only [Pi.neg_apply, neg_sub_neg, dist_comm x y] using hs)
    exact ⟨hh.1.symm, neg_le_neg hh.2⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
