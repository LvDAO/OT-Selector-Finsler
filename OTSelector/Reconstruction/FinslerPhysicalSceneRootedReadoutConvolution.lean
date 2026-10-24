import OTSelector.Reconstruction.FinslerPhysicalSceneProbeFreezing

/-!
# Convolution of the actual full rooted readout

The original finite plan and both clocks are preserved. Changing the Haar root
and canceling its actual mass normalization gives the exact readout convolution.
-/
open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped ENNReal Topology CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]
local notation "V" => (ι → ℝ)
local notation "Edge" => (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))

/-- Any jointly measurable full edge readout has an exact same-plan Haar
convolution, including readouts depending on the original macroscopic root. -/
theorem lintegral_physicalSceneRootedPlan_readout_eq_convolution
    (Γ : Measure (M × M)) [SFinite Γ]
    (coord : M → V) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (F : V × Edge → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, ∫⁻ e, F (z, e) ∂physicalSceneRootedPlan Γ coord u N z
      ∂cavityRootMeasure volume univ N) =
      ∫⁻ p, ∫⁻ v, F (coord p.1 - v,
        physicalSceneRootedObservation coord u (coord p.1 - v) p) ∂volume ∂Γ := by
  have hinner (z : V) : (∫⁻ e, F (z, e) ∂physicalSceneRootedPlan Γ coord u N z) =
      ENNReal.ofReal N * ∫⁻ p, F (z, physicalSceneRootedObservation coord u z p) ∂Γ := by
    change (∫⁻ e, F (z, e) ∂(ENNReal.ofReal N • Γ.map
      (physicalSceneRootedObservation coord u z))) = _
    have hfz : Measurable (fun e : Edge ↦ F (z, e)) :=
      hF.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_smul_measure, smul_eq_mul]
    congr 1
    exact lintegral_map hfz
      (measurable_physicalSceneRootedObservation coord hcoord u hu z)
  simp_rw [hinner]
  rw [cavityRootMeasure, Measure.restrict_univ, lintegral_smul_measure,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, smul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hN))
      ENNReal.ofReal_ne_top, one_mul]
  have ho : Measurable (fun w : V × (M × M) ↦
      physicalSceneRootedObservation coord u w.1 w.2) :=
    (((hcoord.comp measurable_snd.fst).sub measurable_fst).prodMk
      (hu.comp measurable_snd.fst)).prodMk
      (((hcoord.comp measurable_snd.snd).sub measurable_fst).prodMk
        (hu.comp measurable_snd.snd))
  have hFm : Measurable (fun w : V × (M × M) ↦
      F (w.1, physicalSceneRootedObservation coord u w.1 w.2)) :=
    hF.comp (measurable_fst.prodMk ho)
  rw [lintegral_lintegral_swap hFm.aemeasurable]
  apply lintegral_congr
  intro p
  have hm : Measurable (fun z : V ↦
      F (z, physicalSceneRootedObservation coord u z p)) :=
    (hF.comp (measurable_fst.prodMk ho)).comp
      (measurable_id.prodMk measurable_const)
  exact ((volume.measurePreserving_sub_left (coord p.1)).lintegral_comp hm).symm

/-- The actual source-localized freezing error is a measurable full rooted
readout. The second probe reconstructs the unchanged original source position. -/
def physicalSceneMacroProbeFreezingError (π : Measure Edge) (z : V) (scale : ℝ)
    (η : C_c(V, ℝ)) (g : C_c(V × (ℝ × ℝ), ℝ)) : ℝ≥0∞ :=
  ∫⁻ e, ENNReal.ofReal (η e.1.1) * ENNReal.ofReal
    |g (scale⁻¹ • z, (e.1.2, e.2.2)) -
      g (scale⁻¹ • (e.1.1 + z), (e.1.2, e.2.2))| ∂π

/-- Literal physical rooting turns the same-plan freezing error into its
localized microscopic shift; no alternative input law is needed. -/
theorem lintegral_physicalSceneMacroProbeFreezingError_eq
    (Γ : Measure (M × M)) [SFinite Γ]
    (coord : M → V) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N) (scale : ℝ)
    (η : C_c(V, ℝ)) (g : C_c(V × (ℝ × ℝ), ℝ)) :
    (∫⁻ z, physicalSceneMacroProbeFreezingError
      (physicalSceneRootedPlan Γ coord u N z) z scale η g
        ∂cavityRootMeasure volume univ N) =
      ∫⁻ p, ∫⁻ v, ENNReal.ofReal (η v) * ENNReal.ofReal
        |g (scale⁻¹ • coord p.1 - scale⁻¹ • v, (u p.1, u p.2)) -
          g (scale⁻¹ • coord p.1, (u p.1, u p.2))| ∂volume ∂Γ := by
  let F : V × Edge → ℝ≥0∞ := fun w ↦
    ENNReal.ofReal (η w.2.1.1) * ENNReal.ofReal
      |g (scale⁻¹ • w.1, (w.2.1.2, w.2.2.2)) -
        g (scale⁻¹ • (w.2.1.1 + w.1), (w.2.1.2, w.2.2.2))|
  have hm : Measurable F := by
    have hη : Measurable η := η.continuous.measurable
    have hg : Measurable g := g.continuous.measurable
    fun_prop
  change (∫⁻ z, ∫⁻ e, F (z, e) ∂physicalSceneRootedPlan Γ coord u N z
    ∂cavityRootMeasure volume univ N) = _
  rw [lintegral_physicalSceneRootedPlan_readout_eq_convolution Γ coord hcoord u hu N hN F hm]
  apply lintegral_congr
  intro p
  apply lintegral_congr
  intro v
  have hadd : v + (coord p.1 - v) = coord p.1 := by abel
  simp only [F, physicalSceneRootedObservation, sub_sub_cancel, hadd, smul_sub]

/-- The actual normalized physical full-root readout freezes at the original
macroscopic source. Original plans and coordinates may vary with the sample. -/
theorem tendsto_lintegral_physicalSceneMacroProbeFreezingError_zero
    (Γ : ℕ → Measure (M × M)) [∀ n, SFinite (Γ n)]
    (hΓ : ∀ n, Γ n univ ≤ 1)
    (coord : ℕ → M → V) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u)
    (N : ℕ → ℝ) (hN : ∀ n, 0 < N n)
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n)
    (hscale : Tendsto scale atTop atTop)
    (η : C_c(V, ℝ)) (hη : ∀ v, 0 ≤ η v)
    (g : C_c(V × (ℝ × ℝ), ℝ)) :
    Tendsto (fun n ↦ ∫⁻ z, physicalSceneMacroProbeFreezingError
      (physicalSceneRootedPlan (Γ n) (coord n) u (N n) z) z (scale n) η g
        ∂cavityRootMeasure volume univ (N n)) atTop (𝓝 0) := by
  have hh := tendsto_lintegral_compact_macro_probe_shift_zero g η hη scale
    hscalePos hscale Γ hΓ (fun n p ↦ (scale n)⁻¹ • coord n p.1)
      (fun p ↦ (u p.1, u p.2))
  apply hh.congr'
  exact Eventually.of_forall fun n ↦
    (lintegral_physicalSceneMacroProbeFreezingError_eq (Γ n) (coord n)
      (hcoord n) u hu (N n) (hN n) (scale n) η g).symm

/-- Any original root domains inherit the same freezing limit. No boundary
regularity or volume normalization hypothesis on the domains is needed. -/
theorem tendsto_lintegral_physicalSceneMacroProbeFreezingError_restricted_zero
    (Γ : ℕ → Measure (M × M)) [∀ n, SFinite (Γ n)]
    (hΓ : ∀ n, Γ n univ ≤ 1)
    (coord : ℕ → M → V) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u)
    (N : ℕ → ℝ) (hN : ∀ n, 0 < N n)
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n)
    (hscale : Tendsto scale atTop atTop)
    (η : C_c(V, ℝ)) (hη : ∀ v, 0 ≤ η v)
    (g : C_c(V × (ℝ × ℝ), ℝ)) (D : ℕ → Set V) :
    Tendsto (fun n ↦ ∫⁻ z, physicalSceneMacroProbeFreezingError
      (physicalSceneRootedPlan (Γ n) (coord n) u (N n) z) z (scale n) η g
        ∂cavityRootMeasure volume (D n) (N n)) atTop (𝓝 0) := by
  have hh := tendsto_lintegral_physicalSceneMacroProbeFreezingError_zero Γ hΓ
    coord hcoord u hu N hN scale hscalePos hscale η hη g
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hh ε hε] with n hn
  have hm : cavityRootMeasure volume (D n) (N n) ≤
      cavityRootMeasure volume univ (N n) := by
    simp only [cavityRootMeasure, Measure.restrict_univ]
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_right (Measure.restrict_le_self A) _
  exact (lintegral_mono' hm le_rfl).trans hn

end OTSelector.Reconstruction
