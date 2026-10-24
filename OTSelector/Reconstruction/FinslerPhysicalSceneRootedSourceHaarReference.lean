import OTSelector.Probability.HaarAffineCube
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-!
# Exact Haar spatial normalization of original frozen source products

The native seed Haar measure is transported by its original linear basis,
positive spatial scale and actual root translation. Its exact Jacobian is
retained. Arbitrary original clock laws are untouched. Native measurable shapes
inside a rooted source window are dominated by the corresponding uniform spatial
reference times that SAME frozen clock law, with no population-density claim.
-/

open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open MeasureTheory.Measure
open scoped Topology ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {q : ℕ}

/-- The original native Haar law itself produces its finite positive basis
Jacobian. This constant concerns Haar coordinates, not a population density. -/
theorem exists_haar_seed_coordinate_density
    (κ : Measure E) [κ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ)) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧
      κ.map e = c • (volume : Measure (Fin q → ℝ)) := by
  let _inst : (κ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map κ
  let c : ℝ≥0 := addHaarScalarFactor (κ.map e) (volume : Measure (Fin q → ℝ))
  have hc : 0 < c := addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  refine ⟨(c : ℝ≥0∞), by exact_mod_cast hc, ENNReal.coe_ne_top, ?_⟩
  change κ.map e = c • (volume : Measure (Fin q → ℝ))
  exact isAddLeftInvariant_eq_smul _ _

/-- Positive scaling in the original finite seed basis has the exact inverse
volume Jacobian. The exponent is the original seed-space dimension. -/
theorem map_volume_positive_smul_seed_coordinates {scale : ℝ} (hscale : 0 < scale) :
    (volume : Measure (Fin q → ℝ)).map (fun z ↦ scale • z) =
      ((ENNReal.ofReal scale) ^ q)⁻¹ • (volume : Measure (Fin q → ℝ)) := by
  rw [map_addHaar_smul volume hscale.ne']
  simp only [Module.finrank_fin_fun,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hscale.le q)),
    ENNReal.ofReal_inv_of_pos (pow_pos hscale q), ENNReal.ofReal_pow hscale.le]

/-- The original native Haar measure has its exact coordinate density after
positive spatial scaling and the SAME actual root translation. -/
theorem map_haar_scaled_seed_coordinate_sub
    (κ : Measure E) [κ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    {c : ℝ≥0∞} (hmap : κ.map e = c • (volume : Measure (Fin q → ℝ)))
    {scale : ℝ} (hscale : 0 < scale) (root : Fin q → ℝ) :
    κ.map (fun w ↦ scale • e w - root) =
      (c / (ENNReal.ofReal scale) ^ q) • (volume : Measure (Fin q → ℝ)) := by
  have hs : Measurable (fun z : Fin q → ℝ ↦ scale • z) := by fun_prop
  have ht : Measurable (fun z : Fin q → ℝ ↦ -root + z) := by fun_prop
  calc
    _ = ((κ.map e).map (fun z : Fin q → ℝ ↦ scale • z)).map
        (fun z : Fin q → ℝ ↦ -root + z) := by
      rw [Measure.map_map ht hs,
        Measure.map_map (ht.comp hs) e.continuous.measurable]
      congr 1
      funext w
      simp only [Function.comp_def, sub_eq_add_neg, add_comm]
    _ = _ := by
      rw [hmap, Measure.map_smul, map_volume_positive_smul_seed_coordinates hscale,
        smul_smul, Measure.map_smul, IsAddLeftInvariant.map_add_left_eq_self, div_eq_mul_inv]

/-- The original clock remains unchanged in the exact product pushforward. -/
theorem map_haar_product_scaled_seed_coordinate_sub
    (κ : Measure E) [κ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    {c : ℝ≥0∞} (hmap : κ.map e = c • (volume : Measure (Fin q → ℝ)))
    {scale : ℝ} (hscale : 0 < scale) (root : Fin q → ℝ)
    (α : Measure ℝ) [SFinite α] :
    (κ.prod α).map (fun p : E × ℝ ↦ (scale • e p.1 - root, p.2)) =
      ((c / (ENNReal.ofReal scale) ^ q) • (volume : Measure (Fin q → ℝ))).prod α := by
  have hg : Measurable (fun w : E ↦ scale • e w - root) := by fun_prop
  change (κ.prod α).map (Prod.map (fun w : E ↦ scale • e w - root) id) = _
  rw [← Measure.map_prod_map κ α hg measurable_id, Measure.map_id,
    map_haar_scaled_seed_coordinate_sub κ e hmap hscale root]

/-- An arbitrary original AC clock law gives AC of the original full frozen
product observation. Only its Haar spatial factor has been normalized. -/
theorem map_haar_product_scaled_seed_coordinate_sub_absolutelyContinuous
    (κ : Measure E) [κ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    {c : ℝ≥0∞} (hmap : κ.map e = c • (volume : Measure (Fin q → ℝ)))
    {scale : ℝ} (hscale : 0 < scale) (root : Fin q → ℝ)
    (α : Measure ℝ) [SFinite α] (hα : α ≪ (volume : Measure ℝ)) :
    (κ.prod α).map (fun p : E × ℝ ↦ (scale • e p.1 - root, p.2)) ≪
      (volume : Measure (Fin q → ℝ)).prod (volume : Measure ℝ) := by
  rw [map_haar_product_scaled_seed_coordinate_sub κ e hmap hscale root α]
  exact Measure.smul_absolutelyContinuous.prod hα

/-- Every native shape inside the rooted spatial window is dominated by its
uniform restricted Haar reference, preserving the original exact Jacobian. -/
theorem map_restrict_haar_scaled_seed_coordinate_le
    (κ : Measure E) [κ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    {c : ℝ≥0∞} (hmap : κ.map e = c • (volume : Measure (Fin q → ℝ)))
    {scale : ℝ} (hscale : 0 < scale) (root : Fin q → ℝ)
    {K : Set E} {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (hK : K ⊆ (fun w : E ↦ scale • e w - root) ⁻¹' U) :
    (κ.restrict K).map (fun w ↦ scale • e w - root) ≤
      (c / (ENNReal.ofReal scale) ^ q) • (volume : Measure (Fin q → ℝ)).restrict U := by
  have hg : Measurable (fun w : E ↦ scale • e w - root) := by fun_prop
  calc
    _ ≤ (κ.restrict ((fun w : E ↦ scale • e w - root) ⁻¹' U)).map
        (fun w ↦ scale • e w - root) := Measure.map_mono (κ.restrict_mono_set hK) hg
    _ = (κ.map (fun w ↦ scale • e w - root)).restrict U :=
      (Measure.restrict_map hg hU).symm
    _ = _ := by rw [map_haar_scaled_seed_coordinate_sub κ e hmap hscale root,
      Measure.restrict_smul]

/-- The actual native shape times its original frozen clock is dominated by
restricted uniform spatial reference times that SAME original clock law. -/
theorem map_restrict_haar_product_scaled_seed_coordinate_le
    (κ : Measure E) [κ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    {c : ℝ≥0∞} (hmap : κ.map e = c • (volume : Measure (Fin q → ℝ)))
    {scale : ℝ} (hscale : 0 < scale) (root : Fin q → ℝ)
    (α : Measure ℝ) [SFinite α]
    {K : Set E} {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (hK : K ⊆ (fun w : E ↦ scale • e w - root) ⁻¹' U) :
    ((κ.restrict K).prod α).map (fun p : E × ℝ ↦ (scale • e p.1 - root, p.2)) ≤
      ((c / (ENNReal.ofReal scale) ^ q) • (volume : Measure (Fin q → ℝ)).restrict U).prod α := by
  have hg : Measurable (fun w : E ↦ scale • e w - root) := by fun_prop
  change ((κ.restrict K).prod α).map (Prod.map (fun w : E ↦ scale • e w - root) id) ≤ _
  rw [← Measure.map_prod_map (κ.restrict K) α hg measurable_id, Measure.map_id]
  exact Measure.prod_mono (map_restrict_haar_scaled_seed_coordinate_le κ e hmap hscale root hU hK)
    le_rfl

/-- The spatially restricted frozen reference is absolutely continuous with
respect to the fixed coordinate-volume times clock-volume reference. -/
theorem haar_spatial_restrict_product_absolutelyContinuous
    (c : ℝ≥0∞) (U : Set (Fin q → ℝ)) (α : Measure ℝ)
    (hα : α ≪ (volume : Measure ℝ)) :
    (c • (volume : Measure (Fin q → ℝ)).restrict U).prod α ≪
      (volume : Measure (Fin q → ℝ)).prod (volume : Measure ℝ) := by
  have hs : c • (volume : Measure (Fin q → ℝ)).restrict U ≪ volume :=
    Measure.absolutelyContinuous_restrict.smul_left c
  exact hs.prod hα

/-- The original mass factor scale^q cancels the SAME Haar Jacobian exactly. -/
theorem scale_pow_smul_map_haar_scaled_seed_coordinate_sub
    (κ : Measure E) [κ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    {c : ℝ≥0∞} (hmap : κ.map e = c • (volume : Measure (Fin q → ℝ)))
    {scale : ℝ} (hscale : 0 < scale) (root : Fin q → ℝ) :
    ENNReal.ofReal (scale ^ q) • κ.map (fun w ↦ scale • e w - root) =
      c • (volume : Measure (Fin q → ℝ)) := by
  rw [map_haar_scaled_seed_coordinate_sub κ e hmap hscale root, smul_smul,
    ENNReal.ofReal_pow hscale.le,
    ENNReal.mul_div_cancel (pow_ne_zero q (ENNReal.ofReal_pos.mpr hscale).ne') (by finiteness)]

/-- The original mass normalization gives scale-independent frozen domination
on the rooted source window, with no population constant-density hypothesis. -/
theorem scale_pow_smul_map_restrict_haar_product_scaled_seed_coordinate_le
    (κ : Measure E) [κ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    {c : ℝ≥0∞} (hmap : κ.map e = c • (volume : Measure (Fin q → ℝ)))
    {scale : ℝ} (hscale : 0 < scale) (root : Fin q → ℝ)
    (α : Measure ℝ) [SFinite α]
    {K : Set E} {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (hK : K ⊆ (fun w : E ↦ scale • e w - root) ⁻¹' U) :
    ENNReal.ofReal (scale ^ q) •
      ((κ.restrict K).prod α).map (fun p : E × ℝ ↦ (scale • e p.1 - root, p.2)) ≤
      (c • (volume : Measure (Fin q → ℝ)).restrict U).prod α := by
  calc
    _ ≤ ENNReal.ofReal (scale ^ q) •
        (((c / (ENNReal.ofReal scale) ^ q) •
          (volume : Measure (Fin q → ℝ)).restrict U).prod α) :=
      smul_le_smul_left _ (map_restrict_haar_product_scaled_seed_coordinate_le
        κ e hmap hscale root α hU hK)
    _ = _ := by
      rw [Measure.prod_smul_left, smul_smul, ENNReal.ofReal_pow hscale.le,
        ENNReal.mul_div_cancel (pow_ne_zero q (ENNReal.ofReal_pos.mpr hscale).ne') (by finiteness),
        Measure.prod_smul_left]

/-- Finite spatial windows and original finite clock laws give actual finite
AC references whenever their original Haar coordinate density is finite. -/
theorem isFiniteMeasure_haar_spatial_restrict_product
    {c : ℝ≥0∞} (hc : c ≠ ⊤) {U : Set (Fin q → ℝ)} (hU : volume U ≠ ⊤)
    (α : Measure ℝ) [IsFiniteMeasure α] :
    IsFiniteMeasure ((c • (volume : Measure (Fin q → ℝ)).restrict U).prod α) := by
  let _instSpatialFinite : IsFiniteMeasure ((volume : Measure (Fin q → ℝ)).restrict U) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hU.lt_top⟩
  let _instScaledFinite := Measure.smul_finite ((volume : Measure (Fin q → ℝ)).restrict U) hc
  infer_instance


/-- A deterministic finite mixture of the original frozen clock references.
The scalar weights preserve their actual original cell masses. -/
def finiteFrozenHaarClockReference {J : Type*} [Fintype J]
    (d : J → ℝ≥0∞) (c : ℝ≥0∞) (U : Set (Fin q → ℝ))
    (α : J → Measure ℝ) : Measure ((Fin q → ℝ) × ℝ) :=
  ∑ k, d k • ((c • (volume : Measure (Fin q → ℝ)).restrict U).prod (α k))

/-- The actual finite frozen-clock mixture is finite, outer regular and AC.
Clock laws are themselves finite original laws; their AC alone is not used as
a substitute for finiteness. No uniform population density is assumed. -/
theorem finiteFrozenHaarClockReference_finite_outerRegular_ac
    {J : Type*} [Fintype J] (d : J → ℝ≥0∞) (hd : ∀ k, d k ≠ ⊤)
    {c : ℝ≥0∞} (hc : c ≠ ⊤) {U : Set (Fin q → ℝ)} (hU : volume U ≠ ⊤)
    (α : J → Measure ℝ) [∀ k, IsFiniteMeasure (α k)]
    (hα : ∀ k, α k ≪ (volume : Measure ℝ)) :
    IsFiniteMeasure (finiteFrozenHaarClockReference d c U α) ∧
      (finiteFrozenHaarClockReference d c U α).OuterRegular ∧
      finiteFrozenHaarClockReference d c U α ≪
        (volume : Measure (Fin q → ℝ)).prod (volume : Measure ℝ) := by
  let _instBaseFinite : ∀ k, IsFiniteMeasure
      ((c • (volume : Measure (Fin q → ℝ)).restrict U).prod (α k)) :=
    fun k ↦ isFiniteMeasure_haar_spatial_restrict_product hc hU (α k)
  let _instWeightedFinite : ∀ k, IsFiniteMeasure
      (d k • ((c • (volume : Measure (Fin q → ℝ)).restrict U).prod (α k))) :=
    fun k ↦ Measure.smul_finite _ (hd k)
  have hfinite : IsFiniteMeasure (finiteFrozenHaarClockReference d c U α) := by
    unfold finiteFrozenHaarClockReference
    rw [← Measure.sum_fintype]
    infer_instance
  let _instFinite := hfinite
  refine ⟨hfinite, inferInstance, ?_⟩
  unfold finiteFrozenHaarClockReference
  rw [← Measure.sum_fintype]
  exact Measure.absolutelyContinuous_sum_left fun k ↦
    (haar_spatial_restrict_product_absolutelyContinuous c U (α k) (hα k)).smul_left (d k)

end OTSelector.Reconstruction
