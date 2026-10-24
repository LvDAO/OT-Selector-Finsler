import OTSelector.Reconstruction.QuantileCoupling

/-!
# Cdf-inverse-in-distribution and the general stochastic-dominance order coupling

This file completes the quantile machinery of `QuantileCoupling.lean` by proving that
the generalized inverse of the cdf pushes the uniform law on `(0,1)` forward to the
original probability law (`cdf` inverse in distribution).  Consequently the general
order coupling of two stochastically ordered real probability laws exists, with no
pushforward identity assumed.

* `le_cdf_quantile`: the right-continuity of the cdf gives `u ≤ cdf (quantile u)`;
* `quantile_le_iff_le_cdf`: the exact inverse relation `quantile u ≤ t ↔ u ≤ cdf t`;
* `unitIntervalLaw_map_quantile`: `unitIntervalLaw.map (quantile μ) = μ`;
* `exists_orderCoupling_of_stochastic_dominance`: the unconditional co-monotone
  coupling of two probability laws ordered by their cdfs.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

noncomputable section

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

/-- The cdf of the quantile reaches the level: right-continuity of the cdf. -/
theorem le_cdf_quantile (μ : Measure ℝ) {u : ℝ} (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    u ≤ cdf μ (quantile μ u) := by
  have hlim : Tendsto (cdf μ) (𝓝[>] (quantile μ u))
      (𝓝 (cdf μ (quantile μ u))) :=
    (((cdf μ).right_continuous' (quantile μ u)).mono Set.Ioi_subset_Ici_self)
  have hge : ∀ᶠ y in (𝓝[>] (quantile μ u)), u ≤ cdf μ y := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    obtain ⟨x, hxS, hxy⟩ :=
      exists_lt_of_csInf_lt (quantile_nonempty μ hu)
        (show quantile μ u < y from hy)
    exact le_trans hxS (monotone_cdf μ hxy.le)
  exact ge_of_tendsto hlim hge

/-- The exact inverse relation between the cdf and the quantile. -/
theorem quantile_le_iff_le_cdf {μ : Measure ℝ} {u t : ℝ}
    (hu : u ∈ Set.Ioo (0:ℝ) 1) : quantile μ u ≤ t ↔ u ≤ cdf μ t :=
  ⟨fun h => le_trans (le_cdf_quantile μ hu) (monotone_cdf μ h),
    fun h => quantile_le_of_le_cdf μ hu h⟩

/-- The generalized inverse of the cdf pushes the uniform law on `(0,1)` forward to
the original probability law. -/
theorem unitIntervalLaw_map_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    unitIntervalLaw.map (quantile μ) = μ := by
  have hae : AEMeasurable (quantile μ) unitIntervalLaw := aemeasurable_quantile μ
  haveI hmprob : IsProbabilityMeasure (unitIntervalLaw.map (quantile μ)) :=
    Measure.isProbabilityMeasure_map hae
  refine Measure.eq_of_cdf (unitIntervalLaw.map (quantile μ)) μ ?_
  ext t
  have key : ENNReal.ofReal (cdf (unitIntervalLaw.map (quantile μ)) t)
      = ENNReal.ofReal (cdf μ t) := by
    rw [ProbabilityTheory.ofReal_cdf (μ := unitIntervalLaw.map (quantile μ)) t,
      ProbabilityTheory.ofReal_cdf (μ := μ) t]
    rw [Measure.map_apply_of_aemeasurable hae measurableSet_Iic]
    have hA : {u : ℝ | quantile μ u ≤ t} ∩ Set.Ioo (0:ℝ) 1
        = {u : ℝ | u ∈ Set.Ioo (0:ℝ) 1 ∧ u ≤ cdf μ t} := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hq, hu⟩
        exact ⟨hu, (quantile_le_iff_le_cdf hu).mp hq⟩
      · rintro ⟨hu, huc⟩
        exact ⟨(quantile_le_iff_le_cdf hu).mpr huc, hu⟩
    rw [show (quantile μ) ⁻¹' Set.Iic t = {u : ℝ | quantile μ u ≤ t} from rfl]
    rw [unitIntervalLaw, Measure.restrict_apply' measurableSet_Ioo, hA]
    have hc1 : cdf μ t ≤ 1 := cdf_le_one μ t
    have hvol : volume {u : ℝ | u ∈ Set.Ioo (0:ℝ) 1 ∧ u ≤ cdf μ t}
        = ENNReal.ofReal (cdf μ t) := by
      rcases lt_or_eq_of_le hc1 with hlt | heq
      · have hset : {u : ℝ | u ∈ Set.Ioo (0:ℝ) 1 ∧ u ≤ cdf μ t}
            = Set.Ioc (0:ℝ) (cdf μ t) := by
          ext u
          simp only [Set.mem_ofPred_eq, Set.mem_Ioo, Set.mem_Ioc]
          constructor
          · rintro ⟨⟨hu0, _⟩, huc⟩
            exact ⟨hu0, huc⟩
          · rintro ⟨hu0, huc⟩
            exact ⟨⟨hu0, lt_of_le_of_lt huc hlt⟩, huc⟩
        rw [hset, Real.volume_Ioc]
        simp
      · have hset : {u : ℝ | u ∈ Set.Ioo (0:ℝ) 1 ∧ u ≤ cdf μ t}
            = Set.Ioo (0:ℝ) 1 := by
          ext u
          simp only [Set.mem_ofPred_eq, Set.mem_Ioo]
          constructor
          · rintro ⟨h, _⟩
            exact h
          · rintro ⟨hu0, hu1⟩
            exact ⟨⟨hu0, hu1⟩, by simpa [heq] using hu1.le⟩
        rw [hset, Real.volume_Ioo]
        simp [heq]
    rw [hvol, ProbabilityTheory.ofReal_cdf (μ := μ) t]
  exact (ENNReal.ofReal_eq_ofReal_iff (cdf_nonneg (unitIntervalLaw.map (quantile μ)) t)
    (cdf_nonneg μ t)).mp key

/-- The general order coupling of two stochastically ordered real probability laws:
no pushforward identity is assumed. -/
theorem exists_orderCoupling_of_stochastic_dominance
    {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hdom : ∀ t, cdf ν t ≤ cdf μ t) :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧ Vlasov.IsCoupling π μ ν ∧
      ∀ᵐ p ∂π, p.1 ≤ p.2 :=
  exists_orderCoupling_of_quantileMap hdom (unitIntervalLaw_map_quantile μ)
    (unitIntervalLaw_map_quantile ν)

end OTSelector.Reconstruction

end
