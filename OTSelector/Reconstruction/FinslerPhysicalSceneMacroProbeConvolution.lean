import OTSelector.Reconstruction.FinslerPhysicalSceneRootedProbeIdentity

/-!
# Exact original macroscopic probe convolution

Haar rooting turns the actual rootTag-tagged readout into a convolution of the
same original physical plan. No new cloud or conditional source law appears.
At the original microscopic scale this is the starting identity for freezing
physical probes while retaining the full source and target clocks.
-/
open Set Function MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Changing only the actual Haar root gives the literal convolution formula
for an arbitrary jointly measurable root-dependent original probe. -/
theorem lintegral_haar_root_weighted_probe_convolution
    {V Z : Type*} [AddCommGroup V] [MeasurableSpace V]
    [MeasurableAdd₂ V] [MeasurableNeg V] [MeasurableSub₂ V] [MeasurableSpace Z]
    (β : Measure V) [SFinite β] [β.IsAddLeftInvariant] [β.IsNegInvariant]
    (π : Measure Z) [SFinite π] (loc : Z → V) (hloc : Measurable loc)
    (η : V → ℝ≥0∞) (hη : Measurable η)
    (g : V × Z → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ z, ∫⁻ p, η (loc p - z) * g (z, p) ∂π ∂β) =
      ∫⁻ p, ∫⁻ v, η v * g (loc p - v, p) ∂β ∂π := by
  have hm : Measurable (fun w : V × Z ↦ η (loc w.2 - w.1) * g w) :=
    (hη.comp ((hloc.comp measurable_snd).sub measurable_fst)).mul hg
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr
  intro p
  have hfp : Measurable (fun v : V ↦ η v * g (loc p - v, p)) :=
    hη.mul (hg.comp ((measurable_const.sub measurable_id).prodMk measurable_const))
  simpa only [sub_sub_cancel] using (β.measurePreserving_sub_left (loc p)).lintegral_comp hfp

variable {ι M W : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace W]
local notation "Point" => ((ι → ℝ) × ℝ)
local notation "Edge" => (Point × Point)

/-- The same physical edge probe with its actual macroscopic root retained. -/
def physicalSceneMacroClockProbe (π : Measure Edge) (w : W)
    (η : (ι → ℝ) → ℝ≥0∞) (g : W × (ℝ × ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  physicalSceneRootedClockProbe π η (fun st ↦ g (w, st))

/-- The true normalized rooted plan gives a macroscopic convolution of
its original finite edge measure. Its physical clocks are unchanged. -/
theorem lintegral_physicalSceneMacroClockProbe_eq_convolution
    (Γ : Measure (M × M)) [SFinite Γ]
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (rootTag : (ι → ℝ) → W) (hrootTag : Measurable rootTag)
    (η : (ι → ℝ) → ℝ≥0∞) (hη : Measurable η)
    (g : W × (ℝ × ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ z, physicalSceneMacroClockProbe (physicalSceneRootedPlan Γ coord u N z)
      (rootTag z) η g ∂cavityRootMeasure volume univ N) =
      ∫⁻ p, ∫⁻ v, η v * g (rootTag (coord p.1 - v), (u p.1, u p.2)) ∂volume ∂Γ := by
  have hgz (z : ι → ℝ) : Measurable (fun st : ℝ × ℝ ↦ g (rootTag z, st)) :=
    hg.comp (measurable_const.prodMk measurable_id)
  simp only [physicalSceneMacroClockProbe]
  simp_rw [physicalSceneRootedClockProbe_eq Γ coord hcoord u hu N _ η hη _ (hgz _)]
  rw [cavityRootMeasure, Measure.restrict_univ, lintegral_smul_measure,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, smul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hN))
      ENNReal.ofReal_ne_top, one_mul]
  exact lintegral_haar_root_weighted_probe_convolution volume Γ (fun p ↦ coord p.1)
    (hcoord.comp measurable_fst) η hη
    (fun w ↦ g (rootTag w.1, (u w.2.1, u w.2.2)))
    (hg.comp ((hrootTag.comp measurable_fst).prodMk
      ((hu.comp measurable_snd.fst).prodMk (hu.comp measurable_snd.snd))))

end OTSelector.Reconstruction
