import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedPartnerOrientation
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Energy
import OTSelector.Geometry.Finsler.LegendreInjectivity
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Geometry.Finsler.PotentialRegularMass
import OTSelector.Transport.Calibration.CompactPartners
import OTSelector.Transport.Coupling.CostEquivalence
import OTSelector.Transport.Coupling.OptimalPlanExistence

/-!
# Geometry.Finsler.PotentialRegularSpeed

* **Conditions:** The same original potential and compact separated partner carriers, with actual calibration and regular-domain data.
* **Objects:** A Borel full-marginal partner domain on which every recovered actual potential tangent and complete curve has unit speed.
* **Proof detail:** Use either partner orientation to construct a unit Legendre tangent, identify all recovered tangents by injectivity and propagate unit energy.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6](https://arxiv.org/pdf/2409.08001v6#page=47): Section 5.1, Theorem 5.1 (Kantorovich duality), p. 47, and Lemma 5.2 with proof, p. 48 (attained potential).
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [OT-Selector project authors, Project manuscript main.tex (local provenance)](/data/lyuwt/OT-Selector-smooth-length/main.tex): main.tex, proposition label prop:general-optimal-face, lines 422–483, equation eq:general-optimal-face.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerPotentialRegularSpeed.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerPotentialRegularSpeed`; the selected original proof blocks follow. -/
section

/-!
# Unit original potential covectors on measurable full-marginal partner domains

Existing original-distance calibration gives a unit covector from either endpoint
orientation. Actual Legendre injectivity forces every recovered potential tangent at
that point to be unit, and energy conservation propagates this along its complete
curve. Intersecting the intrinsic regular domain with the concrete compact-carrier
partner domains gives a Borel domain with full mass for both original marginals.
The potential is constructed from the original laws and still describes the entire
original distance-optimal face.
-/

open Set Filter Metric MeasureTheory Manifold
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]

/-- Regular original points having a calibrated partner in the opposite compact carrier.
The two alternatives retain the original source and target endpoint orientations. -/
def potentialPartnerDomain (F : ContinuousFinslerNorm E M) (u : M → ℝ)
    (A B : Set M) : Set M :=
  let _instPotentialPartnerDomainMetric : MetricSpace M := F.metricSpace
  F.potentialRegularDomain u ∩
    ({x | x ∈ A ∧ ∃ y ∈ B, u y - u x = dist x y} ∪
      {y | y ∈ B ∧ ∃ x ∈ A, u y - u x = dist x y})

namespace IsSmoothStronglyConvex

variable {F : ContinuousFinslerNorm E M}

/-- At a nontrivially calibrated differentiability point, every actual nonzero inverse
energy-Legendre tangent of the potential differential has original speed exactly one. -/
theorem fiber_speed_eq_one_of_calibrated_partner (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instPartnerUnitFiberLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {x y : M} (hxy : x ≠ y)
    (hsat : let _instPartnerUnitFiberSat : MetricSpace M := F.metricSpace
      u y - u x = dist x y ∨ u x - u y = dist x y)
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x)
    {v : TangentSpace 𝓘(ℝ, E) x} (hv : v ≠ 0)
    (hp : fderiv ℝ (F.fiberEnergy x) v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x) :
    F.toFun ⟨x, v⟩ = 1 := by
  let _instPartnerUnitFiberNorm : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
    inferInstanceAs (NormedAddCommGroup E)
  let _instPartnerUnitFiberSpace : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    inferInstanceAs (NormedSpace ℝ E)
  obtain ⟨g, ⟨hg0, _, _, hunit, hcov⟩, _⟩ :=
    hF.existsUnique_oriented_curve_of_calibrated_partner hcomplete hu hxy hsat hdu
  have hex : ∃ w : TangentSpace 𝓘(ℝ, E) (g 0), F.toFun ⟨g 0, w⟩ = 1 ∧
      fderiv ℝ (F.fiberEnergy (g 0)) w = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (g 0) :=
    ⟨mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g 0 1, hunit 0, hcov.symm⟩
  obtain ⟨w, hw, hwp⟩ := hg0 ▸ hex
  have hw0 : w ≠ 0 := by
    intro hz
    rw [hz, F.map_zero] at hw
    exact zero_ne_one hw
  have heq : v = w := hF.injOn_fiberEnergy_legendre x hv hw0 (hp.trans hwp.symm)
  simpa only [heq] using hw

/-- The same actual potential-covector curve is unit speed at every real time whenever
its initial point has a nontrivial calibrated partner in either direction. -/
theorem speed_eq_one_of_calibrated_partner (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instPartnerUnitCurveLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {x y : M} (hxy : x ≠ y)
    (hsat : let _instPartnerUnitCurveSat : MetricSpace M := F.metricSpace
      u y - u x = dist x y ∨ u x - u y = dist x y)
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x)
    {c : ℝ → M} (hc : F.IsEulerLagrangeOn c univ)
    {v : TangentSpace 𝓘(ℝ, E) x} (hv : v ≠ 0)
    (hinit : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨0, (1 : ℝ)⟩ = ⟨x, v⟩)
    (hp : fderiv ℝ (F.fiberEnergy x) v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x) (t : ℝ) :
    F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1 := by
  rw [hF.speed_eq_of_isEulerLagrangeOn hc isPreconnected_univ (mem_univ t) (mem_univ 0),
    hinit]
  exact hF.fiber_speed_eq_one_of_calibrated_partner hcomplete hu hxy hsat hdu hv hp

/-- Every point in the concrete partner domain has an actual unit energy-Legendre
preimage of the original potential differential. Disjointness supplies nontriviality. -/
theorem exists_unit_legendre_of_mem_potentialPartnerDomain
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instUnitPartnerDomainLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {A B : Set M} (hAB : Disjoint A B) {x : M}
    (hx : x ∈ F.potentialPartnerDomain u A B) :
    ∃ v : TangentSpace 𝓘(ℝ, E) x, F.toFun ⟨x, v⟩ = 1 ∧
      fderiv ℝ (F.fiberEnergy x) v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x := by
  let _instUnitPartnerDomainMetric : MetricSpace M := F.metricSpace
  obtain ⟨v, hv, hp⟩ := hx.1.2
  refine ⟨v, ?_, hp⟩
  rcases hx.2 with ⟨hxA, y, hyB, hcal⟩ | ⟨hxB, y, hyA, hcal⟩
  · have hxy : x ≠ y := fun heq ↦ Set.disjoint_left.mp hAB hxA (heq.symm ▸ hyB)
    exact hF.fiber_speed_eq_one_of_calibrated_partner hcomplete hu hxy (.inl hcal)
      hx.1.1 hv hp
  · have hxy : x ≠ y := fun heq ↦ Set.disjoint_left.mp hAB hyA (heq ▸ hxB)
    exact hF.fiber_speed_eq_one_of_calibrated_partner hcomplete hu hxy
      (.inr (by rwa [dist_comm])) hx.1.1 hv hp

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]

/-- The actual regular partner domain is Borel, by compact partner projection and the
intrinsic regular-domain theorem. No measurable partner selector is needed. -/
theorem measurableSet_potentialPartnerDomain (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : Continuous u) {A B : Set M}
    (hA : IsCompact A) (hB : IsCompact B) :
    MeasurableSet (F.potentialPartnerDomain u A B) := by
  let _instPartnerDomainMeasurableMetric : MetricSpace M := F.metricSpace
  exact (hF.measurableSet_potentialRegularDomain hcomplete u).inter
    ((Reconstruction.isCompact_forward_calibrated_domain hu hA hB).measurableSet.union
      (Reconstruction.isCompact_backward_calibrated_domain hu hA hB).measurableSet)

omit [MeasurableSpace E] [BorelSpace E] in
/-- An original calibrated coupling gives full mass of the concrete partner domain
for both original marginals whenever its intrinsic regular domain has full mass. -/
theorem ae_mem_potentialPartnerDomain_of_isCoupling
    {u : M → ℝ} (hu : Continuous u) {A B : Set M}
    (hA : IsCompact A) (hB : IsCompact B) {μ ν : Measure M}
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    {π : Measure (M × M)} (hπ : Vlasov.IsCoupling π μ ν)
    (hcal : let _instPartnerDomainLawSat : MetricSpace M := F.metricSpace
      ∀ᵐ p ∂π, u p.2 - u p.1 = dist p.1 p.2) :
    (∀ᵐ x ∂μ, x ∈ F.potentialPartnerDomain u A B) ∧
      ∀ᵐ y ∂ν, y ∈ F.potentialPartnerDomain u A B := by
  let _instPartnerDomainLawMetric : MetricSpace M := F.metricSpace
  constructor
  · filter_upwards [hμreg, hμ,
      Reconstruction.ae_exists_forward_calibrated_partner_of_isCoupling hu hB hν hπ hcal]
        with x hreg hx hp
    exact ⟨hreg, Or.inl ⟨hx, hp⟩⟩
  · filter_upwards [hνreg, hν,
      Reconstruction.ae_exists_backward_calibrated_partner_of_isCoupling hu hA hμ hπ hcal]
        with y hreg hy hp
    exact ⟨hreg, Or.inr ⟨hy, hp⟩⟩

/-- Original chartwise absolutely continuous probabilities on disjoint compact carriers
construct the same optimal potential and a Borel domain of actual unit covectors with
full mass for both colors. Its definition retains both endpoint partner relations,
and calibration with that potential still characterizes the entire original optimal face. -/
theorem exists_optimal_calibration_with_full_unit_partner_domain
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (μ ν : Measure M)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμchart : ∀ old : M,
      (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M,
      (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) :
    let _instFullUnitPartnerDomainStatementMetric : MetricSpace M := F.metricSpace
    ∃ u : M → ℝ, LipschitzWith 1 u ∧ MeasurableSet (F.potentialPartnerDomain u A B) ∧
      (∀ᵐ x ∂μ, x ∈ F.potentialPartnerDomain u A B) ∧
      (∀ᵐ y ∂ν, y ∈ F.potentialPartnerDomain u A B) ∧
      (∀ x ∈ F.potentialPartnerDomain u A B,
        ∃ v : TangentSpace 𝓘(ℝ, E) x, F.toFun ⟨x, v⟩ = 1 ∧
          fderiv ℝ (F.fiberEnergy x) v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x) ∧
      ∀ π : Measure (M × M), Vlasov.IsCoupling π μ ν →
        (IsOptimalCoupling edist μ ν π ↔
          ∀ᵐ p ∂π, u p.2 - u p.1 = dist p.1 p.2) := by
  let _instFullUnitPartnerDomainProofMetric : MetricSpace M := F.metricSpace
  obtain ⟨u, hu, hμreg, hνreg, hface⟩ :=
    hF.exists_optimal_calibration_with_full_regular_domain hcomplete m μ ν
      hμchart hνchart hA hB hAB hμ hν
  obtain ⟨π, hπ⟩ := Reconstruction.exists_isOptimalCoupling_edist_of_compact_carrier μ ν
    (hA.union hB) (hμ.mono fun _ hx ↦ Or.inl hx) (hν.mono fun _ hy ↦ Or.inr hy)
  have hcal := (hface π hπ.1).mp hπ
  obtain ⟨hμN, hνN⟩ := ae_mem_potentialPartnerDomain_of_isCoupling hu.continuous
    hA hB hμ hν hμreg hνreg hπ.1 hcal
  exact ⟨u, hu, hF.measurableSet_potentialPartnerDomain hcomplete hu.continuous hA hB,
    hμN, hνN, fun _ hx ↦
      hF.exists_unit_legendre_of_mem_potentialPartnerDomain hcomplete hu hAB hx, hface⟩

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
