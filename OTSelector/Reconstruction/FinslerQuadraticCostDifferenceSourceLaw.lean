import OTSelector.Probability.CavitySemidiscreteSourceMass
import OTSelector.Probability.WeightedMarkNormalization

/-!
# The actual frozen source law is dominated by Haar times its original mark law

Scaling the normalized restricted Haar source cancels its normalization exactly.
Translation preserves the full Haar product, so every original feasible rooted
allocation has a source marginal dominated by that same fixed product measure.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section
namespace OTSelector.Probability

variable {ι A B : Type*} [Fintype ι] [MeasurableSpace A] [MeasurableSpace B]

/-- Spatial translation preserves Haar times the unchanged original mark law. -/
theorem map_haar_product_cavitySpatialTranslate
    (κ : Measure A) [SFinite κ] (z : ι → ℝ) :
    (volume.prod κ).map (cavitySpatialTranslate z) = volume.prod κ := by
  change (volume.prod κ).map (Prod.map (fun x ↦ x - z) id) = _
  rw [← Measure.map_prod_map (f := fun x : ι → ℝ ↦ x - z) (g := id)
    volume κ (measurable_id.sub_const z) measurable_id,
    Measure.map_id]
  congr 1
  simpa only [sub_eq_add_neg] using map_add_right_eq_self volume (-z)

/-- Every root of the normalized frozen source is dominated by the same full
Haar product after the actual mass scaling. -/
theorem frozen_source_rooted_le
    (κ : Measure A) [SFinite κ] (D : Set (ι → ℝ)) {N : ℝ} (hN : 0 < N)
    (z : ι → ℝ) :
    ENNReal.ofReal N • ((ENNReal.ofReal N)⁻¹ • (volume.restrict D).prod κ).map
      (cavitySpatialTranslate z) ≤ volume.prod κ := by
  rw [Measure.map_smul, smul_smul,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hN).ne' ENNReal.ofReal_ne_top, one_smul]
  have hm : Measurable (cavitySpatialTranslate z : ((ι → ℝ) × A) → _) :=
    measurable_cavitySpatialTranslate.comp (measurable_const.prodMk measurable_id)
  exact (Measure.map_mono
    (Measure.prod_mono Measure.restrict_le_self le_rfl) hm).trans_eq
      (map_haar_product_cavitySpatialTranslate κ z)

/-- The preceding domination concerns the actual source marginal of every
feasible allocation, independently of target locations and weights. -/
theorem IsSemidiscreteAllocation.fst_frozenRootedPlan_le {m : ℕ}
    (κ : Measure A) [SFinite κ] (D : Set (ι → ℝ)) {N : ℝ} (hN : 0 < N)
    {p : Fin (m + 1) → ℝ} {a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation
      ((ENNReal.ofReal N)⁻¹ • (volume.restrict D).prod κ) p a)
    (Y : Fin (m + 1) → ((ι → ℝ) × B)) (z : ι → ℝ) :
    (cavitySpatialRootedPlan ((ENNReal.ofReal N)⁻¹ • (volume.restrict D).prod κ)
      a Y N z).fst ≤ volume.prod κ := by
  rw [ha.fst_cavitySpatialRootedPlan Y N z]
  exact frozen_source_rooted_le κ D hN z

/-- The same original frozen allocation source is absolutely continuous with
respect to Haar times its original conditional mark distribution. -/
theorem IsSemidiscreteAllocation.fst_frozenRootedPlan_absolutelyContinuous {m : ℕ}
    (κ : Measure A) [SFinite κ] (D : Set (ι → ℝ)) {N : ℝ} (hN : 0 < N)
    {p : Fin (m + 1) → ℝ} {a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation
      ((ENNReal.ofReal N)⁻¹ • (volume.restrict D).prod κ) p a)
    (Y : Fin (m + 1) → ((ι → ℝ) × B)) (z : ι → ℝ) :
    (cavitySpatialRootedPlan ((ENNReal.ofReal N)⁻¹ • (volume.restrict D).prod κ)
      a Y N z).fst ≪ volume.prod κ :=
  (ha.fst_frozenRootedPlan_le κ D hN Y z).absolutelyContinuous

/-- The existing normalization of the actual spatial cell is exactly the
inverse-mass expression used by the rooted domination theorem. -/
theorem normalized_restricted_haar_product_eq
    (κ : Measure A) [SFinite κ] (D : Set (ι → ℝ)) {N : ℝ} (hN : 0 < N)
    (hD : volume D = ENNReal.ofReal N) :
    (Reconstruction.normalizedFiniteLaw (volume.restrict D)).prod κ =
      (ENNReal.ofReal N)⁻¹ • (volume.restrict D).prod κ := by
  have hmass : (volume.restrict D).real univ = N := by
    simp only [measureReal_def, Measure.restrict_apply_univ, hD,
      ENNReal.toReal_ofReal hN.le]
  rw [Reconstruction.normalizedFiniteLaw, hmass, Measure.prod_smul_left,
    ← Measure.coe_nnreal_smul]
  congr 1
  exact ENNReal.ofReal_inv_of_pos hN

/-- Constant original intensity cancels under probability normalization. The
remaining source is precisely the original Haar cell times its reference mark. -/
theorem normalized_weighted_haar_product_eq
    (κ : Measure A) [IsProbabilityMeasure κ] (D : Set (ι → ℝ))
    [IsFiniteMeasure (volume.restrict D)] {N c : ℝ} (hN : 0 < N) (hc : 0 < c)
    (hD : volume D = ENNReal.ofReal N) :
    Reconstruction.normalizedFiniteLaw (c.toNNReal • (volume.restrict D).prod κ) =
      (ENNReal.ofReal N)⁻¹ • (volume.restrict D).prod κ := by
  have hmass : 0 < (volume.restrict D).real univ := by
    simpa only [measureReal_def, Measure.restrict_apply_univ, hD,
      ENNReal.toReal_ofReal hN.le] using hN
  rw [Reconstruction.normalized_frozen_weighted_law _ _ hc hmass]
  exact normalized_restricted_haar_product_eq κ D hN hD

/-- The actual normalized frozen physical law gives the same pointwise source
bound; no domination hypothesis is supplied to the consumer. -/
theorem IsSemidiscreteAllocation.fst_normalizedFrozenRootedPlan_le {m : ℕ}
    (κ : Measure A) [IsProbabilityMeasure κ] (D : Set (ι → ℝ))
    [IsFiniteMeasure (volume.restrict D)] {N c : ℝ} (hN : 0 < N) (hc : 0 < c)
    (hD : volume D = ENNReal.ofReal N)
    {p : Fin (m + 1) → ℝ} {a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation
      (Reconstruction.normalizedFiniteLaw (c.toNNReal • (volume.restrict D).prod κ)) p a)
    (Y : Fin (m + 1) → ((ι → ℝ) × B)) (z : ι → ℝ) :
    (cavitySpatialRootedPlan
      (Reconstruction.normalizedFiniteLaw (c.toNNReal • (volume.restrict D).prod κ))
      a Y N z).fst ≤ volume.prod κ := by
  rw [normalized_weighted_haar_product_eq κ D hN hc hD] at ha ⊢
  exact ha.fst_frozenRootedPlan_le κ D hN Y z

end OTSelector.Probability
