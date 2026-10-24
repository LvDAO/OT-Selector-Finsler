import OTSelector.Reconstruction.FinslerPhysicalSceneRealFiniteRootRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The original signed convolution gap is controlled by finite root gaps

The same finite collection of original probability root laws controls both
plans. This estimate preserves absolute values before averaging the input law.
-/
open Set Function MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology CompactlySupported ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]
local notation "V" => (ι → ℝ)

/-- Original signed convolution gaps are bounded by the sum of the absolute
gaps on finitely many unchanged probability root laws. -/
theorem exists_finite_original_real_macroProbe_convolution_gap_bound
    (g : C_c(V × (ℝ × ℝ), ℝ)) :
    ∃ cells : Finset (ι → ℤ), ∀ (Γp Γm : Measure (M × M))
      [IsFiniteMeasure Γp] [IsFiniteMeasure Γm]
      (coord : M → V), Measurable coord →
      ∀ (u : M → ℝ), Measurable u →
      ∀ (scale N : ℝ), 0 < scale → 0 < N → scale ^ Fintype.card ι = N →
      ∀ (η : C_c(V, ℝ)), (∀ v, 0 ≤ η v) →
      ENNReal.ofReal |(∫ p, ∫ v, η v * g (scale⁻¹ • (coord p.1 - v), (u p.1, u p.2))
          ∂volume ∂Γp) -
        ∫ p, ∫ v, η v * g (scale⁻¹ • (coord p.1 - v), (u p.1, u p.2)) ∂volume ∂Γm| ≤
      ∑ ν ∈ cells, ∫⁻ z, ENNReal.ofReal
        |physicalSceneRealMacroClockProbe (physicalSceneRootedPlan Γp coord u N z)
            (scale⁻¹ • z) η g -
          physicalSceneRealMacroClockProbe (physicalSceneRootedPlan Γm coord u N z)
            (scale⁻¹ • z) η g|
        ∂cavityRootMeasure volume (physicalSceneRootGridDomain scale ν) N := by
  classical
  obtain ⟨cells, hc⟩ := exists_finite_original_real_macroProbe_root_convolution (M := M) g
  refine ⟨cells, ?_⟩
  intro Γp Γm _ _ coord hcoord u hu scale N hscale hN hpower η hη
  let fp : V → ℝ := fun z ↦ physicalSceneRealMacroClockProbe
    (physicalSceneRootedPlan Γp coord u N z) (scale⁻¹ • z) η g
  let fm : V → ℝ := fun z ↦ physicalSceneRealMacroClockProbe
    (physicalSceneRootedPlan Γm coord u N z) (scale⁻¹ • z) η g
  have hip := integrable_physicalSceneRealMacroClockProbe_haar
    Γp coord hcoord u hu N hN.le scale η hη g
  have him := integrable_physicalSceneRealMacroClockProbe_haar
    Γm coord hcoord u hu N hN.le scale η hη g
  have hi (ν : ι → ℤ) : Integrable fp
      (cavityRootMeasure volume (physicalSceneRootGridDomain scale ν) N) ∧
      Integrable fm (cavityRootMeasure volume (physicalSceneRootGridDomain scale ν) N) := by
    exact ⟨hip.integrableOn.smul_measure (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hN))),
      him.integrableOn.smul_measure (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hN)))⟩
  rw [← (hc Γp coord hcoord u hu scale N hscale hN hpower η hη).2,
    ← (hc Γm coord hcoord u hu scale N hscale hN hpower η hη).2,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ENNReal.ofReal (∑ ν ∈ cells,
        |(∫ z, fp z ∂cavityRootMeasure volume (physicalSceneRootGridDomain scale ν) N) -
          ∫ z, fm z ∂cavityRootMeasure volume (physicalSceneRootGridDomain scale ν) N|) :=
      ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ ν ∈ cells, ENNReal.ofReal
        |(∫ z, fp z ∂cavityRootMeasure volume (physicalSceneRootGridDomain scale ν) N) -
          ∫ z, fm z ∂cavityRootMeasure volume (physicalSceneRootGridDomain scale ν) N| := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ abs_nonneg _)]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ν hν
      rw [← integral_sub (hi ν).1 (hi ν).2]
      simpa only [Real.enorm_eq_ofReal_abs] using
        enorm_integral_le_lintegral_enorm (μ := cavityRootMeasure volume
          (physicalSceneRootGridDomain scale ν) N) (fun z ↦ fp z - fm z)

end OTSelector.Reconstruction
