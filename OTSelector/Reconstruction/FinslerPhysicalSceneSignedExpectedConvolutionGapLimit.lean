import OTSelector.Reconstruction.FinslerPhysicalSceneSignedExpectedFiniteRootGap
import Mathlib.Topology.Algebra.Monoid

/-!
# Original convolution gaps vanish under common root-law convergence

The index filter may be the sample-before-tilt curried filter. Finite root
summation preserves this filter and does not select a diagonal.
-/
open Set Function Filter MeasureTheory OTSelector.Probability
open scoped Topology CompactlySupported ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι M I : Type*} [Fintype ι] [MeasurableSpace M]
local notation "V" => (ι → ℝ)

/-- Common convergence of the original probability-root readout gaps implies
convergence of the original same-plan convolution gap on the very same filter.
The original experiment spaces may change with the index. -/
theorem tendsto_expected_real_macroProbe_convolution_gap_zero_of_root_gaps
    {Ω : I → Type*} [∀ i, MeasurableSpace (Ω i)] {L : Filter I}
    (R : ∀ i, Measure (Ω i))
    (Γp Γm : ∀ i, Ω i → Measure (M × M))
    [∀ i ω, IsFiniteMeasure (Γp i ω)] [∀ i ω, IsFiniteMeasure (Γm i ω)]
    (hΓp : ∀ i, Measurable (Γp i)) (hΓm : ∀ i, Measurable (Γm i))
    (coord : I → M → V) (hcoord : ∀ i, Measurable (coord i))
    (u : M → ℝ) (hu : Measurable u)
    (scale N : I → ℝ) (hscale : ∀ i, 0 < scale i) (hN : ∀ i, 0 < N i)
    (hpower : ∀ i, scale i ^ Fintype.card ι = N i)
    (η : C_c(V, ℝ)) (hη : ∀ v, 0 ≤ η v)
    (g : C_c(V × (ℝ × ℝ), ℝ))
    (hgap : ∀ ν : ι → ℤ,
      Tendsto (fun i ↦ ∫⁻ ω, ∫⁻ z, ENNReal.ofReal
        |physicalSceneRealMacroClockProbe (physicalSceneRootedPlan (Γp i ω) (coord i) u (N i) z)
            ((scale i)⁻¹ • z) η g -
          physicalSceneRealMacroClockProbe (physicalSceneRootedPlan (Γm i ω) (coord i) u (N i) z)
            ((scale i)⁻¹ • z) η g|
        ∂cavityRootMeasure volume (physicalSceneRootGridDomain (scale i) ν) (N i) ∂R i)
        L (𝓝 0)) :
    Tendsto (fun i ↦ ∫⁻ ω, ENNReal.ofReal
      |(∫ p, ∫ v, η v * g ((scale i)⁻¹ • (coord i p.1 - v), (u p.1, u p.2)) ∂volume ∂Γp i ω) -
        ∫ p, ∫ v, η v * g ((scale i)⁻¹ • (coord i p.1 - v), (u p.1, u p.2)) ∂volume ∂Γm i ω| ∂R i)
      L (𝓝 0) := by
  classical
  obtain ⟨cells, hc⟩ := exists_finite_expected_original_real_macroProbe_convolution_gap_bound
    (M := M) g
  have hs := tendsto_finsetSum cells (fun ν _ ↦ hgap ν)
  simp only [Finset.sum_const_zero] at hs
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hs ε hε] with i hi
  exact (hc (R i) (Γp i) (Γm i) (hΓp i) (hΓm i) (coord i) (hcoord i) u hu
    (scale i) (N i) (hscale i) (hN i) (hpower i) η hη).trans hi

end OTSelector.Reconstruction
