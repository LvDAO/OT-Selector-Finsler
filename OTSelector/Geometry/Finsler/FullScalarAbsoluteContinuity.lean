import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedReach
import OTSelector.Geometry.Finsler.EndpointNull
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.HopfRinow
import OTSelector.Geometry.Finsler.InteriorScalarAbsoluteContinuity
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Probability.ConditionalScalarAbsoluteContinuity
import OTSelector.Transport.Calibration.InteriorFullMass
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.FullScalarAbsoluteContinuity

* **Conditions:** Two original chartwise absolutely continuous marginals, a calibrated coupling and disjoint carriers, with ordered actual labels.
* **Objects:** Full calibrated-interior mass and unrestricted joint/conditional scalar absolute continuity for both original laws.
* **Proof detail:** Remove initial/terminal endpoint nullity, apply the constructed interior joint AC and disintegrate its actual label–clock law.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009)](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=25): 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary.
- [D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009)](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=20): 452E, p. 20: consistency and strong consistency; 452G(a)–(c), p. 21: probability kernels and concentration on fibers.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerFullScalarAbsoluteContinuity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerFullScalarAbsoluteContinuity`; the selected original proof blocks follow. -/
section

/-!
# Full original scalar conditional absolute continuity

Original chartwise absolutely continuous marginals with a calibrated coupling and
disjoint carriers give full mass to the actual calibrated interior: the endpoint
nullity theorems discharge both one-sided exceptions. The constructed interior scalar
absolute continuity therefore holds for the unrestricted original joint laws. Their
actual direct scalar conditionals and the scalar pushforwards of their original
conditional position laws are Lebesgue absolutely continuous at almost every label.
-/

open Set Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Reconstruction
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M}

/-- Endpoint nullity gives both original calibrated marginals full interior mass.
All geometric endpoint estimates are discharged from the original chart laws. -/
theorem ae_calibratedInterior_of_calibrated_coupling (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (μ ν : Measure M)
    (hμchart : ∀ old : M,
      (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M,
      (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {u : M → ℝ} (hu : let _instFullInteriorLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) {a : M → Z} (ha : Measurable a)
    (horder : let _instFullInteriorOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {π : Measure (M × M)} (hπ : Vlasov.IsCoupling π μ ν)
    (hcal : let _instFullInteriorCalibration : MetricSpace M := F.metricSpace
      ∀ᵐ p ∂π, u p.2 - u p.1 = dist p.1 p.2)
    {A B : Set M} (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) :
    let _instFullInteriorStatement : MetricSpace M := F.metricSpace
    (∀ᵐ x ∂μ, x ∈ calibratedInterior u) ∧
      ∀ᵐ y ∂ν, y ∈ calibratedInterior u := by
  let _instFullInteriorProofMetric : MetricSpace M := F.metricSpace
  exact ae_calibratedInterior_of_disjoint_carriers hπ hcal hAB hμ hν
    (F.measurableSet_calibratedInterior hcomplete hu)
    (hF.measure_calibratedInitialEndpoints_eq_zero hcomplete m μ hμchart hu ha horder)
    (hF.measure_calibratedTerminalEndpoints_eq_zero hcomplete m ν hνchart hu ha horder)

/-- Both unrestricted original label-potential laws are absolutely continuous with
respect to their own original label marginals times Lebesgue measure. -/
theorem map_label_potential_absolutelyContinuous_of_calibrated_coupling
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (μ ν : Measure M)
    (hμchart : ∀ old : M,
      (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M,
      (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {u : M → ℝ} (hu : let _instFullJointLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) {a : M → Z} (ha : Measurable a)
    (horder : let _instFullJointOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {π : Measure (M × M)} (hπ : Vlasov.IsCoupling π μ ν)
    (hcal : let _instFullJointCalibration : MetricSpace M := F.metricSpace
      ∀ᵐ p ∂π, u p.2 - u p.1 = dist p.1 p.2)
    {A B : Set M} (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) :
    μ.map (fun x ↦ (a x, u x)) ≪ (μ.map a).prod volume ∧
      ν.map (fun x ↦ (a x, u x)) ≪ (ν.map a).prod volume := by
  let _instFullJointProofMetric : MetricSpace M := F.metricSpace
  obtain ⟨hμI, hνI⟩ := hF.ae_calibratedInterior_of_calibrated_coupling
    hcomplete m μ ν hμchart hνchart hu ha horder hπ hcal hAB hμ hν
  have hμjoint := hF.map_label_potential_absolutelyContinuous_of_ordered_labels
    hcomplete m μ hμchart hu ha horder
  have hνjoint := hF.map_label_potential_absolutelyContinuous_of_ordered_labels
    hcomplete m ν hνchart hu ha horder
  dsimp only at hμjoint hνjoint
  rw [Measure.restrict_eq_self_of_ae_mem hμI] at hμjoint
  rw [Measure.restrict_eq_self_of_ae_mem hνI] at hνjoint
  exact ⟨hμjoint, hνjoint⟩

/-- Each original probability has absolutely continuous direct scalar conditionals
and scalar pushforwards of its original conditional position laws, at its own labels. -/
theorem ae_scalarConditionals_absolutelyContinuous_of_calibrated_coupling
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (μ ν : Measure M)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμchart : ∀ old : M,
      (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M,
      (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {u : M → ℝ} (hu : let _instFullConditionalLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) {a : M → Z} (ha : Measurable a)
    (horder : let _instFullConditionalOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {π : Measure (M × M)} (hπ : Vlasov.IsCoupling π μ ν)
    (hcal : let _instFullConditionalCalibration : MetricSpace M := F.metricSpace
      ∀ᵐ p ∂π, u p.2 - u p.1 = dist p.1 p.2)
    {A B : Set M} (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) :
    let _instFullConditionalStatementMetric : MetricSpace M := F.metricSpace
    let _instFullConditionalStatementProper : ProperSpace M :=
      F.properSpace_of_complete hcomplete
    let _instFullConditionalStatementBorel : StandardBorelSpace M := inferInstance
    let _instFullConditionalStatementNonempty : Nonempty M :=
      nonempty_of_isProbabilityMeasure μ
    (∀ᵐ z ∂μ.map a, condDistrib u a μ z ≪ volume ∧
      (condDistrib id a μ z).map u ≪ volume) ∧
      ∀ᵐ z ∂ν.map a, condDistrib u a ν z ≪ volume ∧
        (condDistrib id a ν z).map u ≪ volume := by
  let _instFullConditionalProofMetric : MetricSpace M := F.metricSpace
  let _instFullConditionalProofProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instFullConditionalProofBorel : StandardBorelSpace M := inferInstance
  let _instFullConditionalProofNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  obtain ⟨hμjoint, hνjoint⟩ :=
    hF.map_label_potential_absolutelyContinuous_of_calibrated_coupling
      hcomplete m μ ν hμchart hνchart hu ha horder hπ hcal hAB hμ hν
  exact ⟨(ae_condDistrib_clock_absolutelyContinuous_of_joint μ
      hu.continuous.measurable hμjoint).and
      (ae_condDistrib_map_clock_absolutelyContinuous_of_joint μ
        hu.continuous.measurable hμjoint),
    (ae_condDistrib_clock_absolutelyContinuous_of_joint ν
      hu.continuous.measurable hνjoint).and
      (ae_condDistrib_map_clock_absolutelyContinuous_of_joint ν
        hu.continuous.measurable hνjoint)⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
