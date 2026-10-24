import OTSelector.Reconstruction.OriginalCountingRoughField
import OTSelector.Topology.MetricSpace.McShaneEverywhereLipschitz

/-!
# Uniform ambient Lipschitz bounds for the actual node field

The same literal original occupied-node field is Lipschitz on every ambient locally
finite measure. This closes the global contraction input for measurable inverse curves;
actual full matching and rough-cycle estimates remain relevant to the separate node error.
-/

open Set Function MeasureTheory
open scoped NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {X Y : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] [PseudoMetricSpace Y]

/-- The same actual scalar infimum field is Lipschitz for every ambient measure. -/
theorem lipschitzWith_originalCountingRoughField_everywhere
    (base : X) (L : ℝ≥0) (z : X→Y) (p : X→ℝ) (μ : LocalFiniteMeasure X) :
    LipschitzWith L (originalCountingRoughField base L z p μ) := by
  by_cases ha : μ∈originalCountingSupportActive base
  · have heq : originalCountingRoughField base L z p μ=
        roughMcShane L (z∘originalCountingCompletedAtom base μ)
          (p∘originalCountingCompletedAtom base μ) := by
      funext x
      exact ite_eq_left ha
    rw [heq]
    exact lipschitzWith_roughMcShane_everywhere L _ _
  · have heq : originalCountingRoughField base L z p μ=fun _ ↦ 0 := by
      funext x
      exact ite_eq_right ha
    rw [heq]
    exact (LipschitzWith.const (0:ℝ)).weaken (bot_le : (0:ℝ≥0)≤L)

/-- Coordinatewise actual infima give the same uniform sup-norm Lipschitz bound without
an actual-node legality or rough-bound premise on the ambient scene. -/
theorem lipschitzWith_originalCountingRoughField_vector_everywhere
    {ι : Type*} [Fintype ι]
    (base : X) (L : ℝ≥0) (z : X→Y) (p : X→ι→ℝ) (μ : LocalFiniteMeasure X) :
    LipschitzWith L (fun x ↦ fun i ↦ originalCountingRoughField base L z (fun e ↦ p e i) μ x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg L.coe_nonneg dist_nonneg)).mpr
  intro i
  exact (lipschitzWith_originalCountingRoughField_everywhere base L z (fun e ↦ p e i) μ).dist_le_mul x y

end OTSelector.Reconstruction
