import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.MeasurableGeodesic
import OTSelector.Geometry.Finsler.MeasurableLegendre
import OTSelector.Geometry.Finsler.PotentialInitialState
import OTSelector.Geometry.Finsler.PotentialMeasurablePhase

/-!
# Geometry.Finsler.PotentialChartFamily

* **Conditions:** The actual good chart domain of the original potential in complete Finsler geometry.
* **Objects:** One jointly measurable actual complete curve family with the original point and intrinsic covector as its initial state.
* **Proof detail:** Compose the constructed complete covector family with the actual measurable derivative/range inverse and read its true tangent chart.

Mathematical sources:
- [Sébastien Gouëzel; Yury Kudryashov, mathlib: Derivative is measurable (pinned formal primary source)](https://github.com/leanprover-community/mathlib4/blob/d77ef0741c6da1ff12df68fb4145ea0ae0850c54/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean#L380): Mathlib/Analysis/Calculus/FDeriv/Measurable.lean, module proof description lines 17–55; measurableSet_of_differentiableAt_of_isComplete lines 362–367; measurableSet_of_differentiableAt lines 374–377; measurable_fderiv lines 380–390; measurable_fderiv_apply_const lines 393–395.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerPotentialChartFamily.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerPotentialChartFamily`; the selected original proof blocks follow. -/
section

/-!
# Actual measurable geodesic families from the original potential in each chart

The original coordinate differential, its actual Legendre inverse and the constructed
complete flow give one jointly measurable curve family on the good chart domain.
Its actual initial point and intrinsic energy covector are the original point and
potential differential. No differentiability, measurable velocity or curve-family
assumption is supplied on that domain.
-/

open Set MeasureTheory Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The original potential constructs an actual jointly measurable complete curve family
on its good chart domain, with the original intrinsic initial state and covector. -/
theorem exists_measurable_potential_chart_family (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M) (u : M → ℝ) :
    ∃ G : F.potentialLegendreDomain old u → ℝ → M,
      (∀ x, F.IsEulerLagrangeOn (G x) univ) ∧ Measurable (Function.uncurry G) ∧
      ∀ x, G x 0 = x.val ∧ ∃ v : TangentSpace 𝓘(ℝ, E) x.val, v ≠ 0 ∧
        tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (G x) ⟨0, (1 : ℝ)⟩ = ⟨x.val, v⟩ ∧
        fderiv ℝ (F.fiberEnergy x.val) v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x.val := by
  obtain ⟨Γ, hEL, hi, _, hm⟩ :=
    hF.exists_complete_measurable_geodesic_family hcomplete old
  let G : F.potentialLegendreDomain old u → ℝ → M :=
    fun x ↦ Γ (hF.potentialLegendrePhase old u x)
  refine ⟨G, fun x ↦ hEL _, ?_, ?_⟩
  · exact hm.comp (((hF.measurable_potentialLegendrePhase old u).comp measurable_fst).prodMk
      measurable_snd)
  · intro x
    exact hF.initialState_of_potential_covector_curve old x.property.1
      (hF.mdifferentiableAt_of_mem_potentialLegendreDomain old u x.property)
      x.property.2 (hi (hF.potentialLegendrePhase old u x))

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
