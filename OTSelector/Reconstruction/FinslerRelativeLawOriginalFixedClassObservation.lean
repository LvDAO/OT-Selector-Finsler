import OTSelector.Reconstruction.FinslerConcreteUpperActualClassObservation
import OTSelector.Reconstruction.FinslerRelativeLawActualHaarRetainedLaw

/-!
The original class split restores its original bin masses. The actual positive
Haar density then transfers that property to original seed coordinates, and
observing raw clocks gives exactly the fixed finite class reference over the
same original Haar cell.
-/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

namespace PopulationLocalPressureCore
variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)

/-- Every prescribed measurable exact bin classifier has the same original
Haar/reference class law. The classifier can therefore remain fixed before
compact refinements and across all empirical optimizers and pressure limits. -/
theorem actual_retained_haar_class_observation_of_classifier
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (classify : ℝ → Fin Q.count) (hm : Measurable classify)
    (hclass : ∀ j x, x ∈ Q.cell j → classify x = j)
    (fallbackS fallbackT : Fin Q.count → ℝ)
    (P₀ : Fin Q.count → Fin Q.count → ℝ) (hP₀ : ∀ j k, 0 ≤ P₀ j k)
    (Pf residual : (ℚ → M) → Fin Q.count → Fin Q.count → ℝ)
    (hmPf : ∀ j k, Measurable (fun z ↦ Pf z j k))
    (hPf : ∀ z ∈ L, ∀ j k, Pf z j k = P₀ j k / D.rootIntensity i z)
    (hresidual : ∀ᵐ z ∂lambda.restrict L, ∀ j k, 0 ≤ residual z j k)
    (hrow : ∀ᵐ z ∂lambda.restrict L, ∀ j, ∑ k, (Pf z j k + residual z j k) =
      (condDistrib u a η₀ z).real (Q.cell j))
    (hcol : ∀ᵐ z ∂lambda.restrict L, ∀ k, ∑ j, (Pf z j k + residual z j k) =
      (condDistrib u a η₁ z).real (Q.cell k)) :
    let C := D.haar.continuous.coefficient i
    let R := populationSeedRootLabelValue (P C.seedIndex).seed a
    let raw := (lambda.restrict L) ⊗ₘ finiteClassPopulationKernel Pf
      (fun j ↦ normalizedActualBinKernel (condDistrib u a η₀) (Q.cell j) (Q.measurable_cell j) (fallbackS j))
      (fun k ↦ normalizedActualBinKernel (condDistrib u a η₁) (Q.cell k) (Q.measurable_cell k) (fallbackT k))
    raw.map (Prod.map R (Prod.map classify classify)) =
        ((κ C.seedIndex).restrict (R '' L)).prod (clockClassPairMeasure P₀) ∧
      (normalizedFiniteLaw raw).map (Prod.map R (Prod.map classify classify)) =
        (normalizedFiniteLaw ((κ C.seedIndex).restrict (R '' L))).prod
          (normalizedClockClassPairMeasure P₀) ∧
      raw.map (fun p ↦ (R p.1, classify p.2.1)) =
        ((κ C.seedIndex).restrict (R '' L)).prod ((clockClassPairMeasure P₀).map Prod.fst) ∧
      raw.map (fun p ↦ (R p.1, classify p.2.2)) =
        ((κ C.seedIndex).restrict (R '' L)).prod ((clockClassPairMeasure P₀).map Prod.snd) := by
  classical
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let Seed := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue Seed a
  let m := (κ C.seedIndex).restrict (R '' L)
  haveI : IsFiniteMeasure m := D.isFiniteMeasure_original_haar_cell hF hcomplete hu ha hinj i hL hsub
  let κs := populationSeedCoordinateClockKernel Seed a ha (condDistrib u a η₀)
  let κt := populationSeedCoordinateClockKernel Seed a ha (condDistrib u a η₁)
  have hsub' : L ⊆ (D.haar.intensity i).roots := by rwa [D.haar.intensity_roots]
  have hpositiveDensity : ∀ᵐ z ∂lambda.restrict L, 0 < D.rootIntensity i z := by
    filter_upwards [ae_restrict_mem hL] with z hz
    exact (D.haar.intensity i).lower_pos.trans_le
      ((D.haar.intensity i).bounds (R z) (mem_image_of_mem R (hsub' hz))).1
  have hrow' : ∀ᵐ z ∂lambda.restrict L, ∀ j, ∑ k, (P₀ j k / D.rootIntensity i z + residual z j k) =
      (condDistrib u a η₀ z).real (Q.cell j) := by
    filter_upwards [hrow, ae_restrict_mem hL] with z hz hzL
    simpa only [hPf z hzL] using hz
  have hcol' : ∀ᵐ z ∂lambda.restrict L, ∀ k, ∑ j, (P₀ j k / D.rootIntensity i z + residual z j k) =
      (condDistrib u a η₁ z).real (Q.cell k) := by
    filter_upwards [hcol, ae_restrict_mem hL] with z hz hzL
    simpa only [hPf z hzL] using hz
  have hpositiveOriginal := fixed_reference_bin_masses_ne_zero_of_original_split (lambda.restrict L)
    (condDistrib u a η₀) (condDistrib u a η₁) Q.cell Q.cell P₀ hP₀
    (D.rootIntensity i) residual hpositiveDensity hresidual hrow' hcol'
  have hpositiveHaar := D.original_positive_bin_masses_on_haar hF hcomplete hu ha hinj i hL hsub
    Q.cell Q.cell Q.measurable_cell Q.measurable_cell P₀ hpositiveOriginal
  let raw := (lambda.restrict L) ⊗ₘ finiteClassPopulationKernel Pf
    (fun j ↦ normalizedActualBinKernel (condDistrib u a η₀) (Q.cell j) (Q.measurable_cell j) (fallbackS j))
    (fun k ↦ normalizedActualBinKernel (condDistrib u a η₁) (Q.cell k) (Q.measurable_cell k) (fallbackT k))
  let observe : (ℚ → M) × (ℝ × ℝ) → Seed.covector.ker × (Fin Q.count × Fin Q.count) :=
    Prod.map R (Prod.map classify classify)
  have hR : Measurable R := measurable_populationSeedRootLabelValue Seed hF hcomplete hu ha hinj
  have hmeas : Measurable observe := hR.prodMap (hm.prodMap hm)
  have hhaar := D.actual_retained_cell_pair_law_eq_haar hF hcomplete hu ha hinj i hL hsub
    Q.cell Q.cell Q.measurable_cell Q.measurable_cell fallbackS fallbackT P₀ Pf hmPf hPf
  have hclasslaw := fixedPairClassKernel_original_cell_law m κs κt Q.cell Q.cell
    Q.measurable_cell Q.measurable_cell fallbackS fallbackT classify classify hm hm hclass hclass P₀ hpositiveHaar
  have hexact : raw.map observe = m.prod (clockClassPairMeasure P₀) := by
    have hh := congrArg (fun μ ↦ μ.map (Prod.map (id : Seed.covector.ker → Seed.covector.ker)
      (Prod.map classify classify))) hhaar
    rw [Measure.map_map (measurable_id.prodMap (hm.prodMap hm)) (hR.prodMap measurable_id)] at hh
    exact hh.trans hclasslaw
  refine ⟨hexact, ?_, ?_, ?_⟩
  · have hmassRaw : (raw.map observe).real univ = raw.real univ := by
      simp only [measureReal_def, Measure.map_apply hmeas MeasurableSet.univ, preimage_univ]
    have hnormalize : (normalizedFiniteLaw raw).map observe = normalizedFiniteLaw (raw.map observe) := by
      simp only [normalizedFiniteLaw, hmassRaw, Measure.map_smul]
    rw [hnormalize, hexact, normalizedFiniteLaw_prod_eq]
    rfl
  · have hs := congrArg (fun μ : Measure (Seed.covector.ker × (Fin Q.count × Fin Q.count)) ↦
      μ.map (Prod.map (id : Seed.covector.ker → Seed.covector.ker) Prod.fst)) hexact
    rw [Measure.map_map (measurable_id.prodMap measurable_fst) hmeas,
      ← Measure.map_prod_map m (clockClassPairMeasure P₀) measurable_id measurable_fst,
      Measure.map_id] at hs
    exact hs
  · have ht := congrArg (fun μ : Measure (Seed.covector.ker × (Fin Q.count × Fin Q.count)) ↦
      μ.map (Prod.map (id : Seed.covector.ker → Seed.covector.ker) Prod.snd)) hexact
    rw [Measure.map_map (measurable_id.prodMap measurable_snd) hmeas,
      ← Measure.map_prod_map m (clockClassPairMeasure P₀) measurable_id measurable_snd,
      Measure.map_id] at ht
    exact ht


end PopulationLocalPressureCore
end OTSelector.Reconstruction
