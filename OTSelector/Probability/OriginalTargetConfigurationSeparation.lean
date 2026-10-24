import OTSelector.Probability.OriginalTargetPairBudget
import OTSelector.Probability.LocalConfigurationSpatialSeparation

/-!
# Close-pair control for the original rooted iid target cloud

The original labeled iid array, seen from its actual independent root, satisfies
the vanishing spatial pair budget. The diagonal labels contribute zero because
the witnessing marks are separated; all other pairs retain their original law.
-/

open MeasureTheory Set Function Filter Topology
open scoped BigOperators Classical ENNReal

noncomputable section
namespace OTSelector.Probability

open PointProcess PointProcess.LocalConfiguration

variable {ι B : Type*} [Fintype ι] [MetricSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
  (base : (ι → ℝ) × B)

/-- An original rooted pair keeps the close-pair budget after integrating any
independent root law. The two observed labels are distinct. -/
theorem measure_original_rooted_nearPair_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Measure (ι → ℝ)) [IsProbabilityMeasure ρ]
    (ν : Measure ((ι → ℝ) × B)) [IsProbabilityMeasure ν]
    (Y : Ω → Fin n → ((ι → ℝ) × B))
    (hY : MeasurePreserving Y P (Measure.pi (fun _ : Fin n ↦ ν)))
    (D : Set (ι → ℝ)) {a : ℝ≥0∞}
    (hν : ν.map Prod.fst = a • volume.restrict D)
    {W : Set (ι → ℝ)} (hW : IsOpen W) (δ e : ℝ)
    {i j : Fin n} (hij : i ≠ j) :
    (P.prod ρ) {v | (cavitySpatialTranslate v.2 (Y v.1 i),
      cavitySpatialTranslate v.2 (Y v.1 j)) ∈ markedSpatialNearPair W δ e} ≤
      a * a * (volume W * volume (Metric.ball (0 : ι → ℝ) e)) := by
  have hp := (measurePreserving_iid_distinct_pair ν hij).comp hY
  have hobs : MeasurePreserving
      (fun v : Ω × (ι → ℝ) ↦ (v.2, (Y v.1 i, Y v.1 j)))
      (P.prod ρ) (ρ.prod (ν.prod ν)) :=
    ((MeasurePreserving.id ρ).prod hp).comp Measure.measurePreserving_swap
  let H : Set ((ι → ℝ) × (((ι → ℝ) × B) × ((ι → ℝ) × B))) :=
    {v | (cavitySpatialTranslate v.1 v.2.1, cavitySpatialTranslate v.1 v.2.2) ∈
      markedSpatialNearPair W δ e}
  have hH : MeasurableSet H :=
    (isOpen_markedSpatialNearPair hW δ e).measurableSet.preimage
      ((measurable_cavitySpatialTranslate.comp
        (measurable_fst.prodMk measurable_snd.fst)).prodMk
        (measurable_cavitySpatialTranslate.comp (measurable_fst.prodMk measurable_snd.snd)))
  change (P.prod ρ) ((fun v ↦ (v.2, (Y v.1 i, Y v.1 j))) ⁻¹' H) ≤ _
  rw [hobs.measure_preimage hH.nullMeasurableSet, Measure.prod_apply hH]
  calc
    _ ≤ ∫⁻ _z, a * a * (volume W * volume (Metric.ball (0 : ι → ℝ) e)) ∂ρ := by
      apply lintegral_mono
      intro z
      apply le_trans (measure_mono ?_) (original_marked_pair_mass_le ν D hν hW.measurableSet z e)
      intro p hp
      exact ⟨hp.1, by simpa only [cavitySpatialTranslate, dist_sub_right] using hp.2.1⟩
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

/-- The whole original rooted cloud has a dimension-independent pair budget;
only the small spatial-ball volume controls its decay. -/
theorem measure_cavityRootedTargetConfiguration_nearPair_le
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Measure (ι → ℝ)) [IsProbabilityMeasure ρ]
    (ν : Measure ((ι → ℝ) × B)) [IsProbabilityMeasure ν]
    (Y : Ω → Fin (n + 1) → ((ι → ℝ) × B))
    (hY : MeasurePreserving Y P (Measure.pi (fun _ : Fin (n + 1) ↦ ν)))
    (D : Set (ι → ℝ))
    (hν : ν.map Prod.fst = (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ • volume.restrict D)
    {W : Set (ι → ℝ)} (hW : IsOpen W) {δ : ℝ} (hδ : 0 < δ) (e : ℝ) :
    (P.prod ρ) {v | HasPairIn (markedSpatialNearPair W δ e)
      (cavityRootedTargetConfiguration base Y v)} ≤
      volume W * volume (Metric.ball (0 : ι → ℝ) e) := by
  let N : ℝ≥0∞ := n + 1
  let V : ℝ≥0∞ := volume W * volume (Metric.ball (0 : ι → ℝ) e)
  have hn0 : N ≠ 0 := by simp [N]
  have hntop : N ≠ ∞ := by simp [N]
  have hν' : ν.map Prod.fst = N⁻¹ • volume.restrict D := by
    simpa only [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one] using hν
  have hpair (i j : Fin (n + 1)) :
      (P.prod ρ) {v : Ω × (ι → ℝ) |
        (cavitySpatialTranslate v.2 (Y v.1 i), cavitySpatialTranslate v.2 (Y v.1 j)) ∈
          markedSpatialNearPair W δ e} ≤ N⁻¹ * N⁻¹ * V := by
    by_cases hij : i = j
    · subst j
      have hset : {v : Ω × (ι → ℝ) |
          (cavitySpatialTranslate v.2 (Y v.1 i), cavitySpatialTranslate v.2 (Y v.1 i)) ∈
            markedSpatialNearPair W δ e} = ∅ := by
        ext v
        simp [markedSpatialNearPair, not_lt_of_ge hδ.le]
      rw [hset, measure_empty]
      exact bot_le
    · exact measure_original_rooted_nearPair_le P ρ ν Y hY D hν' hW δ e hij
  calc
    _ ≤ ∑ i, ∑ j, (P.prod ρ) {v : Ω × (ι → ℝ) |
        (cavitySpatialTranslate v.2 (Y v.1 i), cavitySpatialTranslate v.2 (Y v.1 j)) ∈
          markedSpatialNearPair W δ e} :=
      measure_hasPairIn_ofTuple_le (P.prod ρ)
        (fun v j ↦ cavitySpatialTranslate v.2 (Y v.1 j)) _
    _ ≤ ∑ _i : Fin (n + 1), ∑ _j : Fin (n + 1), N⁻¹ * N⁻¹ * V :=
      Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ hpair i j))
    _ = N * (N * (N⁻¹ * N⁻¹ * V)) := by simp [N, nsmul_eq_mul]
    _ = (N * N⁻¹) * (N * N⁻¹) * V := by ring
    _ = V := by rw [ENNReal.mul_inv_cancel hn0 hntop, one_mul, one_mul]

end OTSelector.Probability
