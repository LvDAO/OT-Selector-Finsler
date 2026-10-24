import OTSelector.Reconstruction.FinslerPhysicalSceneRealHaarConvolution

/-!
# Genuine normalized rooting recovers the signed original macro probe

The real-valued physical readout retains the original plan and both clocks.
Its original mass normalization cancels under full Haar rooting exactly.
-/
open Set Function MeasureTheory OTSelector.Probability
open scoped Topology CompactlySupported ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]
local notation "V" => (ι → ℝ)
local notation "Edge" => (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))

/-- The signed real macro-clock readout of the same whole physical plan. -/
def physicalSceneRealMacroClockProbe (π : Measure Edge) (w : V)
    (η : C_c(V, ℝ)) (g : C_c(V × (ℝ × ℝ), ℝ)) : ℝ :=
  ∫ e, η e.1.1 * g (w, (e.1.2, e.2.2)) ∂π

/-- The actual physical observation reads the unchanged finite plan exactly,
including the original mass factor and the two original clocks. -/
theorem physicalSceneRealMacroClockProbe_eq
    (Γ : Measure (M × M)) (coord : M → V) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 ≤ N) (z w : V)
    (η : C_c(V, ℝ)) (g : C_c(V × (ℝ × ℝ), ℝ)) :
    physicalSceneRealMacroClockProbe (physicalSceneRootedPlan Γ coord u N z) w η g =
      N * ∫ p, η (coord p.1 - z) * g (w, (u p.1, u p.2)) ∂Γ := by
  let f : Edge → ℝ := fun e ↦ η e.1.1 * g (w, (e.1.2, e.2.2))
  have hf : Measurable f := (η.continuous.measurable.comp measurable_fst.fst).mul
    (g.continuous.measurable.comp
      (measurable_const.prodMk (measurable_fst.snd.prodMk measurable_snd.snd)))
  change (∫ e, f e ∂(ENNReal.ofReal N • Γ.map
    (physicalSceneRootedObservation coord u z))) = _
  rw [integral_smul_measure, ENNReal.toReal_ofReal hN, smul_eq_mul,
    integral_map (measurable_physicalSceneRootedObservation coord hcoord u hu z).aemeasurable
      hf.aestronglyMeasurable]
  rfl

/-- The whole signed rooted macro probe is Haar-integrable from the original
finite plan. No nonproper marginal-finiteness premise is required. -/
theorem integrable_physicalSceneRealMacroClockProbe_haar
    (Γ : Measure (M × M)) [IsFiniteMeasure Γ]
    (coord : M → V) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 ≤ N) (scale : ℝ)
    (η : C_c(V, ℝ)) (hη : ∀ v, 0 ≤ η v)
    (g : C_c(V × (ℝ × ℝ), ℝ)) :
    Integrable (fun z ↦ physicalSceneRealMacroClockProbe (physicalSceneRootedPlan Γ coord u N z)
      (scale⁻¹ • z) η g) volume := by
  have hm : Measurable (fun w : V × (M × M) ↦
      g (scale⁻¹ • w.1, (u w.2.1, u w.2.2))) :=
    g.continuous.measurable.comp
      (((measurable_const_smul _).comp measurable_fst).prodMk
        ((hu.comp measurable_snd.fst).prodMk (hu.comp measurable_snd.snd)))
  have hb (z : V) (p : M × M) :
      |g (scale⁻¹ • z, (u p.1, u p.2))| ≤ ‖g.toBoundedContinuousFunction‖ := by
    have h := g.toBoundedContinuousFunction.norm_coe_le_norm (scale⁻¹ • z, (u p.1, u p.2))
    change ‖g (scale⁻¹ • z, (u p.1, u p.2))‖ ≤ _ at h
    simpa only [Real.norm_eq_abs] using h
  have hf := integrable_haar_root_weighted_probe Γ (fun p ↦ coord p.1)
    (hcoord.comp measurable_fst) η hη _ hm ‖g.toBoundedContinuousFunction‖ hb
  simp_rw [physicalSceneRealMacroClockProbe_eq Γ coord hcoord u hu N hN]
  exact hf.integral_prod_left.const_mul N

/-- Full genuine normalized Haar rooting recovers the signed same-plan
convolution at the original macroscopic source and clocks. -/
theorem integral_physicalSceneRealMacroClockProbe_eq_convolution
    (Γ : Measure (M × M)) [IsFiniteMeasure Γ]
    (coord : M → V) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N) (scale : ℝ)
    (η : C_c(V, ℝ)) (hη : ∀ v, 0 ≤ η v)
    (g : C_c(V × (ℝ × ℝ), ℝ)) :
    (∫ z, physicalSceneRealMacroClockProbe (physicalSceneRootedPlan Γ coord u N z)
      (scale⁻¹ • z) η g ∂cavityRootMeasure volume univ N) =
      ∫ p, ∫ v, η v * g (scale⁻¹ • (coord p.1 - v), (u p.1, u p.2)) ∂volume ∂Γ := by
  simp_rw [physicalSceneRealMacroClockProbe_eq Γ coord hcoord u hu N hN.le]
  rw [cavityRootMeasure, Measure.restrict_univ, integral_smul_measure, integral_const_mul]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal hN.le, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul]
  apply integral_haar_root_weighted_probe_convolution Γ (fun p ↦ coord p.1)
    (hcoord.comp measurable_fst) η hη
    (fun w ↦ g (scale⁻¹ • w.1, (u w.2.1, u w.2.2)))
  · exact g.continuous.measurable.comp
      (((measurable_const_smul _).comp measurable_fst).prodMk
        ((hu.comp measurable_snd.fst).prodMk (hu.comp measurable_snd.snd)))
  · intro z p
    have hb := g.toBoundedContinuousFunction.norm_coe_le_norm (scale⁻¹ • z, (u p.1, u p.2))
    change ‖g (scale⁻¹ • z, (u p.1, u p.2))‖ ≤ _ at hb
    simpa only [Real.norm_eq_abs] using hb

end OTSelector.Reconstruction
