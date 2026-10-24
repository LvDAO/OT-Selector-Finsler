import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedPartnerOrientation
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Geometry.Finsler.Rademacher
import OTSelector.Transport.Calibration.CompactPartners
import OTSelector.Transport.Coupling.CostEquivalence

/-!
# Geometry.Finsler.PotentialRegularMass

* **Conditions:** Two compactly carried chartwise absolutely continuous populations with a nontrivial calibrated partner almost everywhere in complete Finsler geometry.
* **Objects:** An actual optimal potential with a common full-marginal regular domain and calibration characterization of the entire original optimal face.
* **Proof detail:** Construct a dual optimal potential, use Rademacher and partner saturation to recover nonzero Legendre tangents and transfer through the calibrated coupling.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6](https://arxiv.org/pdf/2409.08001v6#page=47): Section 5.1, Theorem 5.1 (Kantorovich duality), p. 47, and Lemma 5.2 with proof, p. 48 (attained potential).
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [OT-Selector project authors, Project manuscript main.tex (local provenance)](/data/lyuwt/OT-Selector-smooth-length/main.tex): main.tex, proposition label prop:general-optimal-face, lines 422–483, equation eq:general-optimal-face.

Source relation (derived): The full regular-domain result is assembled locally from original populations and duality; it does not yet assert conditional clock AC.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerPotentialRegularMass.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerPotentialRegularMass`; the selected original proof blocks follow. -/
section

/-!
# Full original marginal mass on the intrinsic regular potential domain

A nontrivial calibrated partner on either side supplies the actual nonzero energy
Legendre preimage of the potential differential. Original chartwise absolute
continuity and metric Rademacher then put both original marginals on the same
intrinsic regular domain of an actually constructed optimal potential.
-/

open Set Filter Metric MeasureTheory Manifold
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Either orientation of an actual nontrivial calibrated partner puts an actual
potential differentiability point in the intrinsic regular potential domain. -/
theorem mem_potentialRegularDomain_of_calibrated_partner
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instRegularMassPartnerLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {x y : M} (hxy : x ≠ y)
    (hsat : let _instRegularMassPartnerSat : MetricSpace M := F.metricSpace
      u y - u x = dist x y ∨ u x - u y = dist x y)
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x) :
    x ∈ F.potentialRegularDomain u := by
  obtain ⟨g, ⟨hg0, _, _, hunit, hcov⟩, _⟩ :=
    hF.existsUnique_oriented_curve_of_calibrated_partner hcomplete hu hxy hsat hdu
  have hex : ∃ v : TangentSpace 𝓘(ℝ, E) (g 0), v ≠ 0 ∧
      fderiv ℝ (F.fiberEnergy (g 0)) v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (g 0) := by
    refine ⟨mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g 0 1, ?_, hcov.symm⟩
    intro hz
    have hv := hunit 0
    change F.toFun ⟨g 0, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g 0 1⟩ = 1 at hv
    rw [hz, F.map_zero] at hv
    exact zero_ne_one hv
  exact ⟨hdu, hg0 ▸ hex⟩


variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]

/-- Original chartwise absolutely continuous probability marginals on disjoint
compact carriers determine an actual optimal potential whose intrinsic regular
potential domain has full mass under both marginals. Calibration with this same
potential describes every original distance-optimal coupling. -/
theorem exists_optimal_calibration_with_full_regular_domain
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
    let _instFullRegularDomainStatementMetric : MetricSpace M := F.metricSpace
    ∃ u : M → ℝ, LipschitzWith 1 u ∧
      (∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u) ∧
      (∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u) ∧
      ∀ π : Measure (M × M), Vlasov.IsCoupling π μ ν →
        (IsOptimalCoupling edist μ ν π ↔
          ∀ᵐ p ∂π, u p.2 - u p.1 = dist p.1 p.2) := by
  let _instFullRegularDomainProofMetric : MetricSpace M := F.metricSpace
  obtain ⟨u, hu, hforward, hbackward, hface⟩ :=
    Reconstruction.exists_optimal_calibration_with_partners_of_disjoint_compact_carriers
      μ ν hA hB hAB hμ hν
  have hdμ := F.ae_mdifferentiableAt_scalar_of_lipschitz_of_complete m μ
    hcomplete hμchart hu
  have hdν := F.ae_mdifferentiableAt_scalar_of_lipschitz_of_complete m ν
    hcomplete hνchart hu
  refine ⟨u, hu, ?_, ?_, hface⟩
  · filter_upwards [hdμ, hforward] with x hdx hx
    obtain ⟨y, _, hxy, hcal⟩ := hx.2
    exact hF.mem_potentialRegularDomain_of_calibrated_partner hcomplete hu hxy (.inl hcal) hdx
  · filter_upwards [hdν, hbackward] with y hdy hy
    obtain ⟨x, _, hxy, hcal⟩ := hy.2
    exact hF.mem_potentialRegularDomain_of_calibrated_partner hcomplete hu hxy.symm
      (.inr (by rwa [dist_comm])) hdy

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
