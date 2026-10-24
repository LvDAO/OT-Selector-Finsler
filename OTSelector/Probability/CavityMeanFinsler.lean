import OTSelector.Geometry.FinslerCavityCells
import OTSelector.Probability.CavityMeanPlan

/-!
# Original Finsler mean plans through exact cavity allocations

For complete smooth strongly convex Finsler geometry in dimension at least two, chartwise
absolute continuity and almost surely distinct retained targets supply unique insertion cells.
The resulting full endpoint test identity holds for every optimal fractional assignment,
including an arbitrary data-dependent choice from the whole optimal face.
-/

open Set Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Probability
open scoped BigOperators ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [OpensMeasurableSpace M] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} {W Ω : Type*} [MeasurableSpace W] [MeasurableSpace Ω]
  {F : ContinuousFinslerNorm E M}

/-- The original Finsler row of every optimal fractional matrix has exactly the mean
cell-allocation law, tested against any integrable function of both physical endpoints.
No atomlessness oracle or measurable optimizer choice is assumed. -/
theorem integral_distance_optimalFractional_row (hF : F.IsSmoothStronglyConvex)
    (m : Measure E) [m.IsAddHaarMeasure] (μ : Measure M)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (P : Measure Ω) [IsFiniteMeasure P]
    (W₀ : Ω → W) (X : Ω → M) (hW : Measurable W₀) (hX : Measurable X)
    (hindep : IndepFun W₀ X P) (hlaw : P.map X = μ)
    (Y : W → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (hinj : ∀ᵐ w ∂P.map W₀, Function.Injective (Y w))
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (hret : ∀ k l, Measurable (fun w ↦ retained w k l)) (i : Fin (n + 1))
    (A : Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : ∀ᵐ ω₀ ∂P, OptimalFractionalAssignment
      (Function.update (retained (W₀ ω₀)) i (F.distanceCavityRow Y (W₀ ω₀, X ω₀))) (A ω₀))
    (g : M × M → ℝ)
    (hg : ∀ j, Integrable (fun z : W × M ↦ g (z.2, Y z.1 j)) ((P.map W₀).prod μ)) :
    Integrable (fun ω₀ ↦ ∑ j, A ω₀ i j * g (X ω₀, Y (W₀ ω₀) j)) P ∧
      (∫ ω₀, ∑ j, A ω₀ i j * g (X ω₀, Y (W₀ ω₀) j) ∂P) =
        ∫ w, ∑ j, ∫ x in {x | (w, x) ∈ cavityCell retained (F.distanceCavityRow Y) i j},
          g (x, Y w j) ∂μ ∂P.map W₀ := by
  have : IsFiniteMeasure μ := by
    rw [← hlaw]
    exact Measure.isFiniteMeasure_map P X
  exact integral_optimalFractional_row_eq_cavityMeanReadout_of_unique P μ W₀ X hW hX
    hindep hlaw retained (F.distanceCavityRow Y) hret
    (F.measurable_distanceCavityRow hcomplete Y hY) i
    (hF.ae_existsUnique_distanceCavityCell m μ hdim hchart hcomplete P W₀ X hW hX
      hindep hlaw Y hY hinj retained hret i) A hA (fun z j ↦ g (z.2, Y z.1 j)) hg

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
