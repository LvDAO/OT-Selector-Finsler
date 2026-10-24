import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSeedNonproper
import OTSelector.Reconstruction.FinslerPhysicalSceneProbeTargetCutoff

/-!
# Original global fixed-seed expected probe cutoff budgets

The entire original fixed-seed source restriction is retained. Its finite near
cover contributes only to the radius term, while original lost population mass
is paid once. The original true-distance energy controls the finite sample term.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability
open scoped Topology ContDiff ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] {μ ν : Measure M}
  [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞} [∀ j, SigmaFinite (κ j)]

namespace PopulationLocalPressureCore
variable (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
include hF hcomplete hu ha hinj

variable (horder : let _inst : MetricSpace M := F.metricSpace
  ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
    (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
include horder

/-- A single actual target cutoff, fixed before sample size and allocation,
controls the entire unchanged original seed source. Population loss is paid once. -/
theorem exists_original_fixed_seed_macro_clock_probe_cutoff_budget
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B) (hBcompact : IsCompact B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hwindow : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2) :
    ∃ q > 0, ∃ c > 0, ∀ (j : ℕ)
      (U : Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)),
      MeasurableSet U → volume U ≠ ⊤ → ∀ (R W : ℝ), 0 < R →
      (∀ x ∈ U, ‖x‖ ≤ W) →
      ∀ (η : C_c(Fin (finrank ℝ (P j).seed.covector.ker) → ℝ, ℝ))
        (g : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ)),
      tsupport η ⊆ U →
      ∃ χ : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ, ℝ),
      (∀ y, χ y ∈ Icc 0 1) ∧ EqOn χ 1 (physicalSceneSpatialClockCutoff W R (u '' B)) ∧
      ∀ (n : ℕ)
        (Aalloc : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ),
      (∀ k, Measurable (fun z : (((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M) ↦
        Aalloc z.1 z.2 k)) →
      (∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ z.2 (Aalloc z)) →
      ∀ (spatialScale N : ℝ), 0 < spatialScale → 0 < N →
      ∀ rootDomain : Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ),
      volume rootDomain = ENNReal.ofReal N → ∀ C : ℝ≥0∞,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (spatialScale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C →
      ∀ rootTag : (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) →
        (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ),
      let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
      let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j spatialScale
      let Γ := physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1)
      let π := fun w z ↦ physicalSceneRootedPlan ((Γ w).restrict (H ×ˢ univ)) coord u N z
      (∫⁻ w, ∫⁻ z, ∫⁻ e, ENNReal.ofReal
        |η e.1.1 * g (rootTag z, (e.1.2, e.2.2)) -
          (η e.1.1 * g (rootTag z, (e.1.2, e.2.2))) * χ e.2|
            ∂π w z ∂cavityRootMeasure volume rootDomain N
              ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
        ENNReal.ofReal (‖η.toBoundedContinuousFunction‖ * ‖g.toBoundedContinuousFunction‖) *
          ((D.haar.continuous.count : ℝ≥0∞) *
            ((volume U * (C / ENNReal.ofReal q)) / ENNReal.ofReal (R ^ 2)) +
            volume U * (μ (⋃ i, D.physicalCoreDomain i)ᶜ + ν (⋃ i, D.physicalCoreDomain i)ᶜ +
              C / ENNReal.ofReal (spatialScale ^ 2 * c))) := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨q, hq, c, hc, hb⟩ := D.exists_original_fixed_seed_allocation_nonproper_tail_bound
    hF hcomplete hu ha hinj horder hA hB hBcompact hμA hνB hgap hdist hwindow
  refine ⟨q, hq, c, hc, ?_⟩
  intro j U hU hUf R W hR hUW η g hηU
  let K := physicalSceneSpatialClockCutoff
    (ι := Fin (finrank ℝ (P j).seed.covector.ker)) W R (u '' B)
  have hK : IsCompact K :=
    isCompact_physicalSceneSpatialClockCutoff W R (hBcompact.image hu.continuous)
  obtain ⟨χ, hχK, hχ⟩ := LocalFiniteMeasure.exists_compact_cutoff hK
  refine ⟨χ, hχ, hχK, ?_⟩
  intro n Aalloc halloc hfeas spatialScale N hsp hN rootDomain hD C henergy rootTag
  dsimp only
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
  let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j spatialScale
  let Γ := physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1)
  let π := fun w z ↦ physicalSceneRootedPlan ((Γ w).restrict (H ×ˢ univ)) coord u N z
  let L := ENNReal.ofReal (‖η.toBoundedContinuousFunction‖ * ‖g.toBoundedContinuousFunction‖)
  have hpoint (w) (z) : (∫⁻ e, ENNReal.ofReal
      |η e.1.1 * g (rootTag z, (e.1.2, e.2.2)) -
        (η e.1.1 * g (rootTag z, (e.1.2, e.2.2))) * χ e.2| ∂π w z) ≤
        L * π w z ((U ×ˢ univ) ×ˢ Kᶜ) := by
    have hh := lintegral_macro_clockProbe_cutoff_error_le_escape (π w z) (rootTag z) η g
      χ hχ K hK.measurableSet hχK
    apply hh.trans
    have hm : π w z ((tsupport η ×ˢ univ) ×ˢ Kᶜ) ≤ π w z ((U ×ˢ univ) ×ˢ Kᶜ) :=
      measure_mono (prod_mono (prod_mono hηU subset_rfl) subset_rfl)
    simpa only [L, mul_comm] using mul_le_mul_right hm L
  calc
    _ ≤ ∫⁻ w, ∫⁻ z, L * π w z ((U ×ˢ univ) ×ˢ Kᶜ)
        ∂cavityRootMeasure volume rootDomain N
          ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) :=
      lintegral_mono fun w ↦ lintegral_mono fun z ↦ hpoint w z
    _ = L * (∫⁻ w, ∫⁻ z, π w z ((U ×ˢ univ) ×ˢ Kᶜ)
        ∂cavityRootMeasure volume rootDomain N
          ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) := by
      have hi (w) : (∫⁻ z, L * π w z ((U ×ˢ univ) ×ˢ Kᶜ)
          ∂cavityRootMeasure volume rootDomain N) =
          L * ∫⁻ z, π w z ((U ×ˢ univ) ×ˢ Kᶜ)
            ∂cavityRootMeasure volume rootDomain N :=
        lintegral_const_mul' L _ ENNReal.ofReal_ne_top
      simp_rw [hi]
      exact lintegral_const_mul' L _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
      have htail := hb j n Aalloc halloc hfeas spatialScale N hsp hN
        rootDomain U hD hU hUf R W hR hUW C henergy
      simpa only [L, mul_comm] using mul_le_mul_right htail L

end PopulationLocalPressureCore
end OTSelector.Reconstruction
