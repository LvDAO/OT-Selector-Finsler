import LeanLevy.RandomMeasure.PoissonRandomMeasure
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.SubFinite
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.MetricSpace.HausdorffDimension
import OTSelector.Finite.HierarchicalAssignment
import OTSelector.Finite.PartialMatching
import OTSelector.Finite.PartitionCount
import OTSelector.Finite.PartitionCountTotal

/-!
Conditions: Finite partial matchings whose every source endpoint bears its literal unique family tag; separately, integrable value/energy/defect readouts, positive sample count, rho<1 and the displayed deterministic expectation bounds.

Objects: No inflation of the total family edge count beyond the original source count, and the actual normalized value expectation bounded by normalized energy, bounded probe and priced defect.

Proof detail: Different tags force disjoint source images, so sum their finite cardinalities. Integrate the explicit pointwise energy-defect inequality and divide by the positive sample size and 1−rho.

References: Reinhard Diestel: Chapter 2 opening matching definition and Section 2.1, first three chapter pages; Terence Tao: Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.
Relation: Finite endpoint accounting plus linear integration. The result requires the actual pointwise repair estimate and supplied energy/defect means; no concentration theorem supplies them automatically.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerConcreteUpperTaggedFamilyBudget.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerConcreteUpperTaggedFamilyBudget`; the selected original proof blocks follow. -/
section

/-! Literal source tags prevent inflation of the total matched probe cost. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- A family spending distinct source tags uses at most the original rows. -/
theorem sum_card_le_of_original_source_tags {C : Type*} [Fintype C] {m n : ℕ}
    (tag : Fin m → Option C) (family : C → OTSelector.PartialMatching m n)
    (hs : ∀ c e, e ∈ (family c).edges → tag e.1 = some c) :
    (∑ c, ((family c).card : ℝ)) ≤ m := by
  classical
  have hcard (c) : ((family c).card : ℝ) ≤ partitionCount tag (some c) := by
    rw [OTSelector.partitionCount_eq_card_filter, ← (family c).card_rows]
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro j hj
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs c e he⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ ↦ hcard c)
  have htotal := sum_partitionCount_eq_card tag
  rw [Fintype.sum_option, Fintype.card_fin] at htotal
  have hnone : 0 ≤ partitionCount tag none := by
    unfold partitionCount partitionIndicator
    positivity
  exact hsum.trans (by linarith only [htotal, hnone])

/-- Integrating a samplewise total-energy comparison needs no measurable choice
of the witnesses that established it. -/
theorem integral_normalized_value_le_of_energy_defect
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (value energy defect : Ω → ℝ)
    (hVI : Integrable value P) (hEI : Integrable energy P) (hDI : Integrable defect P)
    {scale ρ probe price energyBound defectBound : ℝ}
    (hρ : ρ < 1) (hprice : 0 ≤ price)
    (hpoint : ∀ᵐ sample ∂P, value sample ≤
      scale * energy sample / (1 - ρ) + (n : ℝ) * probe + price * defect sample)
    (henergy : scale / n * (∫ sample, energy sample ∂P) ≤ energyBound)
    (hdefect : (∫ sample, defect sample ∂P) ≤ defectBound) :
    (∫ sample, value sample ∂P) / n ≤ energyBound / (1 - ρ) + probe + price * defectBound / n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hden : 0 < 1 - ρ := sub_pos.mpr hρ
  have hupperI := (((hEI.const_mul scale).div_const (1 - ρ)).add
    (integrable_const ((n : ℝ) * probe))).add (hDI.const_mul price)
  have hi := integral_mono_ae hVI hupperI hpoint
  change (∫ sample, value sample ∂P) ≤ ∫ sample,
    (scale * energy sample / (1 - ρ) + (n : ℝ) * probe) + price * defect sample ∂P at hi
  rw [integral_add (f := fun sample ↦ scale * energy sample / (1 - ρ) + (n : ℝ) * probe)
    (g := fun sample ↦ price * defect sample)
    (((hEI.const_mul scale).div_const (1 - ρ)).add (integrable_const ((n : ℝ) * probe)))
    (hDI.const_mul price)] at hi
  rw [integral_add (f := fun sample ↦ scale * energy sample / (1 - ρ))
    (g := fun _ : Ω ↦ (n : ℝ) * probe)
    ((hEI.const_mul scale).div_const (1 - ρ))
    (integrable_const ((n : ℝ) * probe)), integral_div, integral_const_mul,
    integral_const_mul, integral_const] at hi
  simp only [integral_const_mul, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hi
  have hscaled := div_le_div_of_nonneg_right hi hnR.le
  have he : scale * (∫ sample, energy sample ∂P) / (1 - ρ) / n ≤ energyBound / (1 - ρ) := by
    calc _ = (scale / n * (∫ sample, energy sample ∂P)) / (1 - ρ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right henergy hden.le
  have hd := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdefect hprice) hnR.le
  calc _ ≤ (scale * (∫ sample, energy sample ∂P) / (1 - ρ) + (n : ℝ) * probe +
        price * (∫ sample, defect sample ∂P)) / n := hscaled
    _ = scale * (∫ sample, energy sample ∂P) / (1 - ρ) / n + probe +
        price * (∫ sample, defect sample ∂P) / n := by field_simp
    _ ≤ _ := add_le_add (add_le_add he (le_refl _)) hd

end OTSelector.Reconstruction

end
end
