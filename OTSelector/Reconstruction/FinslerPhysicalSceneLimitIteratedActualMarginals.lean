import OTSelector.MeasureTheory.IteratedWeakExactMarginals
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedSourceCutoffDefect
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedTargetCutoffDefect
import OTSelector.Reconstruction.FinslerPhysicalSceneLimitCompactEscapeExhaustion

/-!
# Actual two-index rooted allocations retain full marginals in iterated limits

The actual finite plans share their physical source exactly. Compact escape
bounds and the vanishing untruncated target defect supply the cutoff bounds
needed by the separate sample and tilt weak limits.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

local instance iteratedActualMarginalPlanPolish : PolishSpace
    (LocalFiniteMeasure ((((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))) :=
  LocalFiniteMeasure.instPolishSpace

/-- Actual source and target escape estimates, with the actual target defect,
produce exact full marginal equality after the sample limit and then the tilt
limit. No target-column law is replaced or assumed equal at finite sample size. -/
theorem ae_common_marginals_of_iterated_actualAllocation_escapes
    (Penv : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (Penv n)]
    (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : ∀ (_ℓ n : ℕ), Ω n → M → Fin (n + 1) → ℝ)
    (hplus : ∀ ℓ n k, Measurable (fun z : Ω n × M ↦ aplus ℓ n z.1 z.2 k))
    (hminus : ∀ ℓ n k, Measurable (fun z : Ω n × M ↦ aminus ℓ n z.1 z.2 k))
    (Y : ∀ n, Ω n → Fin (n + 1) → M)
    (hY : ∀ n k, Measurable (fun w ↦ Y n w k))
    (p : ∀ n, Ω n → Fin (n + 1) → ℝ)
    (hfp : ∀ ℓ n, ∀ᵐ w ∂Penv n, IsSemidiscreteAllocation μ (p n w) (aplus ℓ n w))
    (hfm : ∀ ℓ n, ∀ᵐ w ∂Penv n, IsSemidiscreteAllocation μ (p n w) (aminus ℓ n w))
    (H : Set M) (hH : MeasurableSet H)
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u)
    (rootMass : ℕ → ℝ) (hN : ∀ n, 0 < rootMass n)
    (rootDomain : ℕ → Set (ι → ℝ))
    (hRoot : ∀ n, volume (rootDomain n) = ENNReal.ofReal (rootMass n)) :
    let sceneLaw := fun ℓ n ↦ actualAllocationRootedSceneLaw (Penv n) μ
      (aplus ℓ n) (aminus ℓ n) (hplus ℓ n) (hminus ℓ n) (Y n) (hY n)
      H hH (coord n) (hcoord n) u hu (rootMass n) (hN n) (rootDomain n) (hRoot n)
    let π := fun n (allocation : Ω n → M → Fin (n + 1) → ℝ) w z ↦
      physicalSceneRootedPlan
        ((physicalSceneGlobalAllocationFamily μ allocation (Y n) w).restrict (H ×ˢ univ))
        (coord n) u (rootMass n) z
    let sourceEscape := fun (f : C_c((ι → ℝ) × ℝ, ℝ)) n allocation K ↦
      ∫⁻ w, ∫⁻ z, π n allocation w z (tsupport f ×ˢ Kᶜ)
        ∂cavityRootMeasure volume (rootDomain n) (rootMass n) ∂Penv n
    let targetEscape := fun (f : C_c((ι → ℝ) × ℝ, ℝ)) n allocation K ↦
      ∫⁻ w, ∫⁻ z, π n allocation w z (Kᶜ ×ˢ tsupport f)
        ∂cavityRootMeasure volume (rootDomain n) (rootMass n) ∂Penv n
    let targetDefect := fun (f : C_c((ι → ℝ) × ℝ, ℝ)) ℓ n ↦
      ∫⁻ w, ∫⁻ z, ENNReal.ofReal
        |(∫ e, f e.2 ∂π n (aplus ℓ n) w z) - ∫ e, f e.2 ∂π n (aminus ℓ n) w z|
        ∂cavityRootMeasure volume (rootDomain n) (rootMass n) ∂Penv n
    (∀ f : C_c((ι → ℝ) × ℝ, ℝ), ∃ K : CompactExhaustion ((ι → ℝ) × ℝ),
      ∀ m : ℕ, ∀ᶠ n in atTop, ∀ ℓ,
        (sourceEscape f n (aplus ℓ n) (K m) ≤ (((m + 1 : ℕ) : ℝ≥0∞))⁻¹ ∧
          targetEscape f n (aplus ℓ n) (K m) ≤ (((m + 1 : ℕ) : ℝ≥0∞))⁻¹) ∧
        (sourceEscape f n (aminus ℓ n) (K m) ≤ (((m + 1 : ℕ) : ℝ≥0∞))⁻¹ ∧
          targetEscape f n (aminus ℓ n) (K m) ≤ (((m + 1 : ℕ) : ℝ≥0∞))⁻¹)) →
    (∀ f ℓ, Tendsto (targetDefect f ℓ) atTop (𝓝 0)) →
    ∀ (R : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
      (Q : ℕ → ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
      (φ : ℕ → ℕ → ℕ), (∀ ℓ, Tendsto (φ ℓ) atTop atTop) → ∀ ψ : ℕ → ℕ,
      (∀ ℓ, Tendsto (fun n ↦ sceneLaw ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ))) →
      Tendsto (fun k ↦ Q (ψ k)) atTop (𝓝 R) →
      (∀ᵐ scene ∂(R : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))),
        (IsFiniteMeasureOnCompacts (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).fst ∧
          IsFiniteMeasureOnCompacts (scene.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).fst) ∧
        (IsFiniteMeasureOnCompacts (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).snd ∧
          IsFiniteMeasureOnCompacts (scene.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).snd)) →
      ∀ᵐ scene ∂(R : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))),
        (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).fst = (scene.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).fst ∧
        (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).snd = (scene.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).snd := by
  dsimp only
  intro hescape htarget R Q φ hφ ψ hinner houter hlocal
  let Kbase : CompactExhaustion ((ι → ℝ) × ℝ) := physicalSceneSpatialClockExhaustion 0 0
  let f := LocalFiniteMeasure.separatingTest Kbase
  choose K hK using fun i ↦ hescape (f i)
  let tail := fun i m ↦ 2 * ENNReal.ofReal ‖(f i).toBoundedContinuousFunction‖ *
    (((m + 1 : ℕ) : ℝ≥0∞))⁻¹
  have htail (i) : Tendsto (tail i) atTop (𝓝 0) := by
    have hf : 2 * ENNReal.ofReal ‖(f i).toBoundedContinuousFunction‖ ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
    simpa only [tail, Function.comp_def, mul_zero] using
      (ENNReal.continuousAt_const_mul (Or.inl hf)).tendsto.comp
        tendsto_physicalScene_compact_escape_tolerance_zero
  let defect := fun i (_m ℓ n : ℕ) ↦ ∫⁻ w, ∫⁻ z, ENNReal.ofReal
    |(∫ e, (f i) e.2 ∂physicalSceneRootedPlan
        ((physicalSceneGlobalAllocationFamily μ (aplus ℓ n) (Y n) w).restrict (H ×ˢ univ))
        (coord n) u (rootMass n) z) -
      ∫ e, (f i) e.2 ∂physicalSceneRootedPlan
        ((physicalSceneGlobalAllocationFamily μ (aminus ℓ n) (Y n) w).restrict (H ×ˢ univ))
        (coord n) u (rootMass n) z|
    ∂cavityRootMeasure volume (rootDomain n) (rootMass n) ∂Penv n
  apply ae_common_marginals_of_iterated_weak_eventual_cutoff_bounds R Q
    (fun ℓ n ↦ actualAllocationRootedSceneLaw (Penv n) μ
      (aplus ℓ n) (aminus ℓ n) (hplus ℓ n) (hminus ℓ n) (Y n) (hY n)
      H hH (coord n) (hcoord n) u hu (rootMass n) (hN n) (rootDomain n) (hRoot n)) φ hφ ψ
    hinner houter Kbase Kbase K K hlocal tail tail htail htail
    (fun _ _ _ _ ↦ 0) defect (fun _ _ _ ↦ tendsto_const_nhds)
    (fun i _ ℓ ↦ htarget (f i) ℓ)
  · intro i m ℓ
    filter_upwards [hK i m] with n hn
    have hb := lintegral_actualAllocationRootedSceneLaw_source_cutoff_defect_le_escape
      (Penv n) μ (aplus ℓ n) (aminus ℓ n) (hplus ℓ n) (hminus ℓ n)
      (Y n) (hY n) (p n) (hfp ℓ n) (hfm ℓ n) H hH (coord n) (hcoord n) u hu
      (rootMass n) (hN n) (rootDomain n) (hRoot n) (f i)
      (LocalFiniteMeasure.exhaustionCutoff (K i) m)
      (LocalFiniteMeasure.exhaustionCutoff_bounds _ _) (K i m) ((K i).isCompact m).measurableSet
      (LocalFiniteMeasure.exhaustionCutoff_eq_one _ _)
    apply hb.trans
    simp only [add_zero]
    calc
      _ ≤ ENNReal.ofReal ‖(f i).toBoundedContinuousFunction‖ *
          ((((m + 1 : ℕ) : ℝ≥0∞))⁻¹ + (((m + 1 : ℕ) : ℝ≥0∞))⁻¹) :=
        mul_le_mul_right (add_le_add (hn ℓ).1.1 (hn ℓ).2.1) _
      _ = _ := by dsimp only [tail]; ring
  · intro i m ℓ
    filter_upwards [hK i m] with n hn
    have hb := lintegral_actualAllocationRootedSceneLaw_target_cutoff_defect_le_target_defect_escape
      (Penv n) μ (aplus ℓ n) (aminus ℓ n) (hplus ℓ n) (hminus ℓ n)
      (Y n) (hY n) H hH (coord n) (hcoord n) u hu
      (rootMass n) (hN n) (rootDomain n) (hRoot n)
      (LocalFiniteMeasure.exhaustionCutoff (K i) m) (f i)
      (LocalFiniteMeasure.exhaustionCutoff_bounds _ _) (K i m) ((K i).isCompact m).measurableSet
      (LocalFiniteMeasure.exhaustionCutoff_eq_one _ _)
    apply hb.trans
    calc
      _ ≤ defect i m ℓ n + ENNReal.ofReal ‖(f i).toBoundedContinuousFunction‖ *
          ((((m + 1 : ℕ) : ℝ≥0∞))⁻¹ + (((m + 1 : ℕ) : ℝ≥0∞))⁻¹) :=
        add_le_add (le_refl _) (mul_le_mul_right (add_le_add (hn ℓ).1.2 (hn ℓ).2.2) _)
      _ = _ := by dsimp only [tail]; ring

end OTSelector.Reconstruction
