import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.FullScalarAbsoluteContinuity
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerPotentialClockLaw.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerPotentialClockLaw`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.PotentialClockLaw

* **Conditions:** Two original chartwise absolutely continuous marginals coupled by actual calibration, with disjoint carriers in the stated complete Finsler geometry.
* **Objects:** Lebesgue absolute continuity and hence atomlessness of both original potential-clock laws.
* **Proof detail:** Use the constructed actual joint label–clock AC laws and project their null clock cylinders; transfer Lebesgue singleton nullity to the original scalar laws.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=52): Section 5.3, Theorem 5.9(i)–(iv), pp. 52–53, equations (5.12)–(5.14); balance proof p. 56.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.

Source relation (derived): A consequence for the same supplied calibrated potential and original marginals; no reselected scalar law is introduced.
-/

/-!
# Original potential-clock laws

The label-potential laws constructed from a calibrated coupling are absolutely continuous
with respect to their own label marginals times Lebesgue measure. Projecting those actual
joint laws gives Lebesgue absolutely continuous potential-clock laws for both original
marginals, and therefore atomlessness for the same supplied calibrated potential.
-/

open Set MeasureTheory Manifold
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M}

/-- Both original potential-clock laws are Lebesgue absolutely continuous. The potential,
labels, coupling and marginals are the supplied original geometric data. -/
theorem map_potential_absolutelyContinuous_of_calibrated_coupling
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (μ ν : Measure M)
    (hμchart : ∀ old : M,
      (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M,
      (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {u : M → ℝ} (hu : let _instPotentialClockLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) {a : M → Z} (ha : Measurable a)
    (horder : let _instPotentialClockOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {π : Measure (M × M)} (hπ : Vlasov.IsCoupling π μ ν)
    (hcal : let _instPotentialClockCalibration : MetricSpace M := F.metricSpace
      ∀ᵐ p ∂π, u p.2 - u p.1 = dist p.1 p.2)
    {A B : Set M} (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) :
    μ.map u ≪ volume ∧ ν.map u ≪ volume := by
  let _instPotentialClockProofMetric : MetricSpace M := F.metricSpace
  obtain ⟨hμjoint, hνjoint⟩ :=
    hF.map_label_potential_absolutelyContinuous_of_calibrated_coupling
      hcomplete m μ ν hμchart hνchart hu ha horder hπ hcal hAB hμ hν
  have hproject (η : Measure M)
      (hη : η.map (fun x ↦ (a x, u x)) ≪ (η.map a).prod volume) :
      η.map u ≪ volume := by
    have hsnd := hη.map measurable_snd
    rw [Measure.map_map measurable_snd (ha.prodMk hu.continuous.measurable),
      Measure.map_snd_prod] at hsnd
    exact hsnd.trans Measure.smul_absolutelyContinuous
  exact ⟨hproject μ hμjoint, hproject ν hνjoint⟩

/-- Both original potential-clock laws have no atoms, with the same supplied potential
and coupling used to construct the original scalar absolute continuity. -/
theorem nullSingletonClass_map_potential_of_calibrated_coupling
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (μ ν : Measure M)
    (hμchart : ∀ old : M,
      (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M,
      (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {u : M → ℝ} (hu : let _instPotentialClockAtomLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) {a : M → Z} (ha : Measurable a)
    (horder : let _instPotentialClockAtomOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {π : Measure (M × M)} (hπ : Vlasov.IsCoupling π μ ν)
    (hcal : let _instPotentialClockAtomCalibration : MetricSpace M := F.metricSpace
      ∀ᵐ p ∂π, u p.2 - u p.1 = dist p.1 p.2)
    {A B : Set M} (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) :
    NullSingletonClass (μ.map u) ∧ NullSingletonClass (ν.map u) := by
  obtain ⟨hμclock, hνclock⟩ :=
    hF.map_potential_absolutelyContinuous_of_calibrated_coupling
      hcomplete m μ ν hμchart hνchart hu ha horder hπ hcal hAB hμ hν
  exact ⟨⟨fun r ↦ hμclock (s := {r}) Real.volume_singleton⟩,
    ⟨fun r ↦ hνclock (s := {r}) Real.volume_singleton⟩⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
