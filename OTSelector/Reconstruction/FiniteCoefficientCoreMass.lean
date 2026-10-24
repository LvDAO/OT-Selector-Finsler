import OTSelector.Reconstruction.FinslerFiniteCoefficientCores
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Original population mass outside finite coefficient regions

Every measurable family of legal conditional pairings obeys the same localization
bound. The original root law weights each compact coefficient region; no product
coupling or conditional renormalization is used.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

/-- A common conditional loss bound on a countable family of rectangles controls
the omitted joint mass, with its original root weights. -/
theorem compProd_compl_iUnion_prod_le
    {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Countable I]
    (lambda : Measure X) [SFinite lambda] (π : Kernel X Y) [IsMarkovKernel π]
    (K : I → Set X) (T : I → Set Y)
    (hK : ∀ i, MeasurableSet (K i)) (hT : ∀ i, MeasurableSet (T i))
    {δ : ℝ≥0∞} (hsmall : ∀ᵐ z ∂lambda, ∀ i, z ∈ K i → π z (T i)ᶜ ≤ δ) :
    (lambda ⊗ₘ π) (⋃ i, K i ×ˢ T i)ᶜ ≤
      lambda (⋃ i, K i)ᶜ + δ * lambda (⋃ i, K i) := by
  classical
  let H := ⋃ i, K i
  have hH : MeasurableSet H := MeasurableSet.iUnion hK
  have hR : MeasurableSet (⋃ i, K i ×ˢ T i) :=
    MeasurableSet.iUnion fun i ↦ (hK i).prod (hT i)
  rw [Measure.compProd_apply hR.compl]
  calc
    _ ≤ ∫⁻ z, Hᶜ.indicator (fun _ ↦ (1 : ℝ≥0∞)) z +
        H.indicator (fun _ ↦ δ) z ∂lambda := by
      apply lintegral_mono_ae
      filter_upwards [hsmall] with z hz
      by_cases hzH : z ∈ H
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hzH
        have hsub : Prod.mk z ⁻¹' (⋃ i, K i ×ˢ T i)ᶜ ⊆ (T i)ᶜ := by
          intro y hy hyt
          exact hy (mem_iUnion.mpr ⟨i, hi, hyt⟩)
        simpa only [indicator_of_mem hzH,
          indicator_of_notMem (show z ∉ Hᶜ from fun h ↦ h hzH), zero_add]
          using (measure_mono hsub).trans (hz i hi)
      · simpa only [indicator_of_notMem hzH,
          indicator_of_mem (show z ∈ Hᶜ from hzH), add_zero] using
          (measure_mono (subset_univ (Prod.mk z ⁻¹' (⋃ i, K i ×ˢ T i)ᶜ))).trans_eq
            (measure_univ : π z univ = 1)
    _ = _ := by
      rw [lintegral_add_left (measurable_const.indicator hH.compl),
        lintegral_indicator hH.compl, lintegral_indicator hH,
        setLIntegral_const, setLIntegral_const, one_mul]

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  [T2Space Z] [BorelSpace Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z} [SFinite lambda]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]

omit [BorelSpace E] in
/-- Finite actual coefficient cores control the joint mass discarded from any
measurable family of legal conditional couplings of the original two populations. -/
theorem OriginalPopulationCoefficientCore.joint_complement_le
    {N : ℕ} {δ : ℝ≥0∞}
    (C : Fin N → OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (π : Kernel Z (ℝ × ℝ)) [IsMarkovKernel π]
    (hπ : ∀ᵐ z ∂lambda,
      Vlasov.IsCoupling (π z) (condDistrib u a η₀ z) (condDistrib u a η₁ z))
    (horder : ∀ᵐ z ∂lambda, ∀ᵐ p ∂π z, p.1 ≤ p.2) :
    (lambda ⊗ₘ π) (⋃ i, (C i).roots ×ˢ (C i).window.region)ᶜ ≤
      lambda (⋃ i, (C i).roots)ᶜ + δ * lambda (⋃ i, (C i).roots) := by
  apply compProd_compl_iUnion_prod_le lambda π
    (fun i ↦ (C i).roots) (fun i ↦ (C i).window.region)
    (fun i ↦ (C i).roots_compact.measurableSet)
    (fun i ↦ (C i).window.isCompact_region.measurableSet)
  filter_upwards [hπ, horder] with z hz ho
  exact fun i hi ↦ ((C i).coupling_loss z hi (π z) hz ho).le

end OTSelector.Reconstruction
