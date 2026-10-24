import OTSelector.Reconstruction.FinslerPhysicalSceneRootedPopulationSourcePartition
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedSourceHaarReference

/-!
# Normalized original population source references

The same original conditional population and its actual finite Taylor cells
produce finite outer-regular source references. Exact native Haar normalization
cancels the original scale^dimension mass factor. Reference laws may depend on
accuracy, while the error constant is independent of their finite count, the
sample scale and the actual root. Every target remains in the source readout.
-/
open Set Function MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

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

/-- Exact original Haar normalization turns all finite conditional references
into one source-window reference independent of sample scale and actual root. -/
theorem exists_original_normalized_source_window_reference
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count)
    [(κ (D.haar.continuous.coefficient i).seedIndex).IsAddHaarMeasure]
    {q : ℕ}
    (e : (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker ≃L[ℝ] (Fin q → ℝ))
    {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hmap : (κ (D.haar.continuous.coefficient i).seedIndex).map e =
      c • (volume : Measure (Fin q → ℝ)))
    (U : Set (Fin q → ℝ)) (hU : MeasurableSet U) (hUfinite : volume U ≠ ⊤)
    {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ reference : Measure ((Fin q → ℝ) × ℝ),
      IsFiniteMeasure reference ∧ reference.OuterRegular ∧
      reference ≪ (volume : Measure (Fin q → ℝ)).prod (volume : Measure ℝ) ∧
      ∀ (scale : ℝ), 0 < scale → ∀ (root : Fin q → ℝ)
        (L : Set (ℚ → M)) (_hL : MeasurableSet L)
        (_hsub : L ⊆ (D.haar.continuous.coefficient i).roots),
        (∀ z ∈ L,
          scale • e (populationSeedRootLabelValue
            (P (D.haar.continuous.coefficient i).seedIndex).seed a z) - root ∈ U) →
        ∀ s : Set ((Fin q → ℝ) × ℝ), MeasurableSet s →
          ENNReal.ofReal (scale ^ q) *
            ((η₀.restrict (a ⁻¹' L)).map (fun x ↦
              (scale • e (D.haar.sceneCoordinate i x).1 - root, u x))) s ≤
            reference s + ENNReal.ofReal (2 * tolerance * (D.haar.intensity i).upper) *
              c * volume U := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨T, Q, hclock, hbound⟩ :=
    D.exists_original_source_partition_observation_bound hF hcomplete hu ha hinj i htolerance
  let d : Fin Q.count → ℝ≥0 := fun k ↦ (D.rootIntensity i (Q.center k)).toNNReal
  let α : Fin Q.count → Measure ℝ := fun k ↦ condDistrib u a η₀ (Q.center k)
  let reference : Measure ((Fin q → ℝ) × ℝ) :=
    ∑ k : Fin Q.count, d k • ((c • (volume : Measure (Fin q → ℝ)).restrict U).prod (α k))
  have href := finiteFrozenHaarClockReference_finite_outerRegular_ac
    (fun k ↦ (d k : ℝ≥0∞)) (fun k ↦ ENNReal.coe_ne_top) hc hUfinite α hclock
  refine ⟨reference, href.1, href.2.1, href.2.2, ?_⟩
  intro scale hscale root L hL hsub hinside s hs
  let R := populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a
  let obs := fun p : (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker × ℝ ↦
    (scale • e p.1 - root, p.2)
  have hobs : Measurable obs := by fun_prop
  have hsource := hbound L hL hsub obs hobs s hs
  have hshape (k : Fin Q.count) : R '' (Q.cell k ∩ L) ⊆
      (fun w ↦ scale • e w - root) ⁻¹' U := by
    rintro w ⟨z, hz, rfl⟩
    exact hinside z hz.2
  have hterm (k : Fin Q.count) :
      ENNReal.ofReal (scale ^ q) *
        ((((d k) • ((κ (D.haar.continuous.coefficient i).seedIndex).restrict
          (R '' (Q.cell k ∩ L)))).prod (α k)).map obs) s ≤
      (d k • ((c • (volume : Measure (Fin q → ℝ)).restrict U).prod (α k))) s := by
    have hh := scale_pow_smul_map_restrict_haar_product_scaled_seed_coordinate_le
      (κ (D.haar.continuous.coefficient i).seedIndex) e hmap hscale root (α k) hU (hshape k)
    have hv := Measure.le_iff.mp hh s hs
    rw [Measure.smul_apply, smul_eq_mul] at hv
    have hb := mul_le_mul_right hv (d k : ℝ≥0∞)
    simpa only [Measure.prod_smul_left, Measure.map_smul, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
      obs, mul_assoc, mul_comm, mul_left_comm] using hb
  have hmass : ENNReal.ofReal (scale ^ q) *
      (κ (D.haar.continuous.coefficient i).seedIndex) (R '' L) ≤ c * volume U := by
    have hg : Measurable (fun w ↦ scale • e w - root) := by fun_prop
    have hm := congrArg (fun μ : Measure (Fin q → ℝ) ↦ μ U)
      (scale_pow_smul_map_haar_scaled_seed_coordinate_sub
        (κ (D.haar.continuous.coefficient i).seedIndex) e hmap hscale root)
    rw [Measure.smul_apply, Measure.map_apply hg hU, Measure.smul_apply, smul_eq_mul,
      smul_eq_mul] at hm
    have hk : R '' L ⊆ (fun w ↦ scale • e w - root) ⁻¹' U := by
      rintro w ⟨z, hz, rfl⟩
      exact hinside z hz
    exact (mul_le_mul_right (measure_mono hk) (ENNReal.ofReal (scale ^ q))).trans_eq hm
  have herr := mul_le_mul_right hmass
    (ENNReal.ofReal (2 * tolerance * (D.haar.intensity i).upper))
  have hb := mul_le_mul_right hsource (ENNReal.ofReal (scale ^ q))
  rw [mul_add, Finset.mul_sum] at hb
  have hsums := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) ↦ hterm k
  dsimp only [d, α, R] at hsums
  simp only [Measure.prod_smul_left, Measure.map_smul] at hb hsums
  have hh := hb.trans (add_le_add hsums (by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using herr))
  simpa only [Measure.finsetSum_apply, Measure.prod_smul_left, d, α, R, reference, obs,
    PopulationHaarPressureCore.sceneCoordinate, mul_assoc, mul_comm, mul_left_comm] using hh
/-- The actual original seed basis and Haar law produce a finite source-window
reference at every accuracy. The original full core source is read on its literal
rooted spatial window; no supplied cell, shape or frozen-reference hypothesis is
needed, and the error constant is independent of the reference partition size. -/
theorem exists_original_core_source_window_reference
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count)
    [(κ (D.haar.continuous.coefficient i).seedIndex).IsAddHaarMeasure]
    (U : Set (Fin (finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ))
    (hU : MeasurableSet U) (hUfinite : volume U ≠ ⊤) :
    ∃ errorConstant : ℝ≥0∞, errorConstant ≠ ⊤ ∧
    ∀ tolerance : ℝ, 0 < tolerance →
    ∃ reference : Measure ((Fin (finrank ℝ
        (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ) × ℝ),
      IsFiniteMeasure reference ∧ reference.OuterRegular ∧
      reference ≪ (volume : Measure (Fin (finrank ℝ
        (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ)).prod
          (volume : Measure ℝ) ∧
      ∀ scale : ℝ, 0 < scale →
      ∀ root : Fin (finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ,
      ∀ s : Set ((Fin (finrank ℝ
        (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ) × ℝ),
        MeasurableSet s →
        ENNReal.ofReal (scale ^ finrank ℝ
          (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) *
          ((η₀.restrict (a ⁻¹' (D.haar.continuous.coefficient i).roots)).map (fun x ↦
            (scale • (Module.finBasis ℝ
              (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker).equivFunL
                (D.haar.sceneCoordinate i x).1 - root, u x))) (s ∩ (U ×ˢ univ)) ≤
          reference s + ENNReal.ofReal tolerance * errorConstant := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let W := (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker
  let q := finrank ℝ W
  let e := (Module.finBasis ℝ W).equivFunL
  let R := populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a
  obtain ⟨c, _hcpos, hc, hmap⟩ :=
    exists_haar_seed_coordinate_density (κ (D.haar.continuous.coefficient i).seedIndex) e
  let errorConstant := ENNReal.ofReal (2 * (D.haar.intensity i).upper) * c * volume U
  refine ⟨errorConstant, ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc) hUfinite, ?_⟩
  intro tolerance htolerance
  obtain ⟨reference, hfinite, hregular, hac, hbound⟩ :=
    D.exists_original_normalized_source_window_reference hF hcomplete hu ha hinj i e hc hmap
      U hU hUfinite htolerance
  refine ⟨reference, hfinite, hregular, hac, ?_⟩
  intro scale hscale root s hs
  have hR : Measurable R := measurable_populationSeedRootLabelValue
    (P (D.haar.continuous.coefficient i).seedIndex).seed hF hcomplete hu ha hinj
  let f := fun z : ℚ → M ↦ scale • e (R z) - root
  have hf : Measurable f := by
    have hh := ((e.continuous.measurable.comp hR).const_smul scale).sub_const root
    simpa only [f, Function.comp_def, Pi.smul_apply] using hh
  let L := (D.haar.continuous.coefficient i).roots ∩ f ⁻¹' U
  have hL : MeasurableSet L :=
    (D.haar.continuous.coefficient i).roots_compact.measurableSet.inter (hf hU)
  have hsub : L ⊆ (D.haar.continuous.coefficient i).roots := inter_subset_left
  have hinside : ∀ z ∈ L, scale • e (R z) - root ∈ U := fun _ hz ↦ hz.2
  have hb := hbound scale hscale root L hL hsub hinside s hs
  let obs := fun x : M ↦ (scale • e (D.haar.sceneCoordinate i x).1 - root, u x)
  have hobs : Measurable obs := by
    have hc := D.haar.measurable_sceneCoordinate hF hcomplete hu ha hinj i
    have hw := e.continuous.measurable.comp (measurable_fst.comp hc)
    have hh := ((hw.const_smul scale).sub_const root).prodMk hu.continuous.measurable
    simpa only [obs, Function.comp_def, Pi.smul_apply] using hh
  have heq :
      ((η₀.restrict (a ⁻¹' (D.haar.continuous.coefficient i).roots)).map obs)
        (s ∩ (U ×ˢ univ)) = ((η₀.restrict (a ⁻¹' L)).map obs) s := by
    rw [Measure.map_apply hobs (hs.inter (hU.prod MeasurableSet.univ)),
      Measure.map_apply hobs hs, Measure.restrict_apply
        (hobs (hs.inter (hU.prod MeasurableSet.univ))), Measure.restrict_apply (hobs hs)]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true, L, f, obs,
      PopulationHaarPressureCore.sceneCoordinate, R]
    tauto
  rw [← heq] at hb
  have hcoef : 2 * tolerance * (D.haar.intensity i).upper =
      tolerance * (2 * (D.haar.intensity i).upper) := by ring
  rw [hcoef, ENNReal.ofReal_mul htolerance.le] at hb
  simpa only [mul_assoc, errorConstant, obs, W, q, e] using hb

end PopulationLocalPressureCore
end OTSelector.Reconstruction
