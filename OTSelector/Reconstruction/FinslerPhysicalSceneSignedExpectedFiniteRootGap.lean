import OTSelector.Reconstruction.FinslerPhysicalSceneSignedFiniteRootGap
import OTSelector.Reconstruction.FinslerPhysicalSceneMacroClockProbeCutoffGapExpectation

/-!
# Finite original root gaps control the original expected convolution gap

All readouts are measurable from the same finite-plan fields. Absolute gaps
are averaged on the unchanged experiment before finite root summation.
-/
open Set Function Filter MeasureTheory OTSelector.Probability
open scoped Topology CompactlySupported ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω]
local notation "V" => (ι → ℝ)
local notation "Edge" => ((V × ℝ) × (V × ℝ))

/-- A finite original plan field supplies the measurability of the absolute
gap under each unchanged normalized root law. -/
theorem measurable_lintegral_real_macroProbe_root_gap
    (Γp Γm : Ω → Measure (M × M))
    [∀ ω, IsFiniteMeasure (Γp ω)] [∀ ω, IsFiniteMeasure (Γm ω)]
    (hΓp : Measurable Γp) (hΓm : Measurable Γm)
    (coord : M → V) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u)
    (scale N : ℝ) (hscale : 0 < scale) (hN : 0 < N)
    (hpower : scale ^ Fintype.card ι = N)
    (η : C_c(V, ℝ)) (g : C_c(V × (ℝ × ℝ), ℝ)) (ν : ι → ℤ) :
    Measurable (fun ω ↦ ∫⁻ z, ENNReal.ofReal
      |physicalSceneRealMacroClockProbe (physicalSceneRootedPlan (Γp ω) coord u N z)
          (scale⁻¹ • z) η g -
        physicalSceneRealMacroClockProbe (physicalSceneRootedPlan (Γm ω) coord u N z)
          (scale⁻¹ • z) η g|
      ∂cavityRootMeasure volume (physicalSceneRootGridDomain scale ν) N) := by
  let rootMeasure := cavityRootMeasure volume (physicalSceneRootGridDomain scale ν) N
  let _inst : IsProbabilityMeasure rootMeasure := isProbabilityMeasure_cavityRootMeasure volume _ N hN
    ((volume_physicalSceneRootGridDomain scale hscale ν).trans (congrArg ENNReal.ofReal hpower))
  let πp : Ω × V → Measure Edge := fun v ↦ physicalSceneRootedPlan (Γp v.1) coord u N v.2
  let πm : Ω × V → Measure Edge := fun v ↦ physicalSceneRootedPlan (Γm v.1) coord u N v.2
  let _instP (v : Ω × V) : IsFiniteMeasure (πp v) :=
    isFiniteMeasure_physicalSceneRootedPlan (Γp v.1) coord u N v.2
  let _instM (v : Ω × V) : IsFiniteMeasure (πm v) :=
    isFiniteMeasure_physicalSceneRootedPlan (Γm v.1) coord u N v.2
  have hp : Measurable πp := measurable_joint_physicalSceneRootedPlan Γp hΓp coord hcoord u hu N
  have hm : Measurable πm := measurable_joint_physicalSceneRootedPlan Γm hΓm coord hcoord u hu N
  have hg := measurable_ofReal_abs_macro_clock_probe_gap πp πm hp hm
    (fun v : Ω × V ↦ scale⁻¹ • v.2)
    ((measurable_const_smul _).comp measurable_snd) η g
  exact hg.lintegral_prod_right

/-- Compact macro support fixes a finite original root family before the
experiment or plans are chosen; its expected absolute gaps bound the original
same-plan convolution gap. -/
theorem exists_finite_expected_original_real_macroProbe_convolution_gap_bound
    (g : C_c(V × (ℝ × ℝ), ℝ)) :
    ∃ cells : Finset (ι → ℤ), ∀ {Ω : Type*} [MeasurableSpace Ω] (R : Measure Ω)
      (Γp Γm : Ω → Measure (M × M))
      [∀ ω, IsFiniteMeasure (Γp ω)] [∀ ω, IsFiniteMeasure (Γm ω)],
      Measurable Γp → Measurable Γm →
      ∀ (coord : M → V), Measurable coord → ∀ (u : M → ℝ), Measurable u →
      ∀ (scale N : ℝ), 0 < scale → 0 < N → scale ^ Fintype.card ι = N →
      ∀ (η : C_c(V, ℝ)), (∀ v, 0 ≤ η v) →
      (∫⁻ ω, ENNReal.ofReal
        |(∫ p, ∫ v, η v * g (scale⁻¹ • (coord p.1 - v), (u p.1, u p.2)) ∂volume ∂Γp ω) -
          ∫ p, ∫ v, η v * g (scale⁻¹ • (coord p.1 - v), (u p.1, u p.2)) ∂volume ∂Γm ω| ∂R) ≤
      ∑ ν ∈ cells, ∫⁻ ω, ∫⁻ z, ENNReal.ofReal
        |physicalSceneRealMacroClockProbe (physicalSceneRootedPlan (Γp ω) coord u N z)
            (scale⁻¹ • z) η g -
          physicalSceneRealMacroClockProbe (physicalSceneRootedPlan (Γm ω) coord u N z)
            (scale⁻¹ • z) η g|
        ∂cavityRootMeasure volume (physicalSceneRootGridDomain scale ν) N ∂R := by
  obtain ⟨cells, hc⟩ := exists_finite_original_real_macroProbe_convolution_gap_bound (M := M) g
  refine ⟨cells, ?_⟩
  intro Ω _ R Γp Γm _ _ hΓp hΓm coord hcoord u hu scale N hscale hN hpower η hη
  calc
    _ ≤ ∫⁻ ω, ∑ ν ∈ cells, ∫⁻ z, ENNReal.ofReal
        |physicalSceneRealMacroClockProbe (physicalSceneRootedPlan (Γp ω) coord u N z)
            (scale⁻¹ • z) η g -
          physicalSceneRealMacroClockProbe (physicalSceneRootedPlan (Γm ω) coord u N z)
            (scale⁻¹ • z) η g|
        ∂cavityRootMeasure volume (physicalSceneRootGridDomain scale ν) N ∂R :=
      lintegral_mono (fun ω ↦ hc (Γp ω) (Γm ω) coord hcoord u hu scale N hscale hN hpower η hη)
    _ = _ := lintegral_finsetSum cells (fun ν _ ↦
      measurable_lintegral_real_macroProbe_root_gap Γp Γm hΓp hΓm coord hcoord u hu
        scale N hscale hN hpower η g ν)

end OTSelector.Reconstruction
