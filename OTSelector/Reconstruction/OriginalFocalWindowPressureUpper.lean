import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalFocalKinetic
import OTSelector.Reconstruction.OriginalRetainedPressureUpperContinuity
import OTSelector.Reconstruction.FinslerOriginalCanonicalClockPressure

/-! Expanding original clock windows retain the same full original focal
kernel. Original inverse-compliance comparison gives one bound before every
window, while actual retained original laws recover the full pressure upper. -/
open Set Function MeasureTheory ProbabilityTheory Filter Matrix Module Manifold
open scoped Topology ContDiff ENNReal NNReal Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Every original retained source/target sublaw is charged exactly its
actual inverse-compliance coefficient on the true legal graph, even when
its endpoints approach the full original span boundary. -/
theorem original_focal_pressure_eq_actual_coefficient
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hα : α ≪ μ) (hβ : β ≪ ν) (g : ℝ → ℝ → ℝ) (r : ℝ≥0) (t : ℝ) :
    legalMarkedPressure (finrank ℝ S.covector.ker) id id α β r (D.originalFocalKinetic gap) g t =
      legalMarkedPressure (finrank ℝ S.covector.ker) id id α β r
        (fun a b v ↦ matrixQuadratic (originalSeedPairCoefficient S w (a,b)) v) g t := by
  have hsource : ∀ᵐ a ∂α, a - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ a ∈ μ.support :=
    hα.ae_le (D.support.source.ae_open.and μ.support_mem_ae)
  have htarget : ∀ᵐ b ∂β, b - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ b ∈ ν.support :=
    hβ.ae_le (D.support.target.ae_open.and ν.support_mem_ae)
  apply legalMarkedPressure_congr_of_ae_on_legal
  filter_upwards [ae_fst_of_ae hsource,ae_snd_of_ae htarget] with p hpS hpT
  intro hforward
  refine ⟨?_,rfl⟩
  intro v
  exact D.originalFocalKinetic_eq_of_original_support hbounds hpS hpT hforward v

/-- The exact full original coefficient identification holds at every real
spatial scale, before any thermodynamic limit. -/
theorem original_focal_scalePressure_eq_actual_coefficient
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hα : α ≪ μ) (hβ : β ≪ ν) (g : ℝ → ℝ → ℝ) (R t : ℝ) :
    legalMarkedScalePressure (finrank ℝ S.covector.ker) id id α β (D.originalFocalKinetic gap) g R t =
      legalMarkedScalePressure (finrank ℝ S.covector.ker) id id α β
        (fun a b v ↦ matrixQuadratic (originalSeedPairCoefficient S w (a,b)) v) g R t := by
  by_cases hR : 0 < R
  · simp only [legalMarkedScalePressure,hR,↓reduceIte]
    rw [D.original_focal_pressure_eq_actual_coefficient hbounds α β hα hβ]
  · simp only [legalMarkedScalePressure,hR,↓reduceIte]

/-- Original conditional geometry removes arbitrary expanding clock screens
at the true canonical pressure upper. One actual original inverse-compliance
bound is produced before every screen; no uniform window bound or endpoint
nondegeneracy is assumed. -/
theorem exists_original_retained_pressure_upper
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π μ ν) (horder : ∀ᵐ p ∂π, p.1 ≤ p.2)
    (χ : ℕ → Measure (ℝ × ℝ)) (hχ : ∀ n, χ n ≤ π)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hδ0 : ∀ n, 0 ≤ δ n) (hδ1 : ∀ n, δ n < 1)
    (hmass : ∀ n, 1 - δ n ≤ (χ n).real univ)
    {G : ℝ} (hG : 0 ≤ G) (g : ℝ → ℝ → ℝ)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) :
    let _ : IsProbabilityMeasure μ := D.support.source.probability
    let _ : IsProbabilityMeasure ν := D.support.target.probability
    ∃ πret : ℕ → ProbabilityMeasure (ℝ × ℝ),
      (∀ n, (πret n : Measure (ℝ × ℝ)) = normalizedFiniteLaw (χ n)) ∧
    ∃ pref : ℝ → ℝ, ∃ p : ℕ → ℝ → ℝ,
      (∀ t, Tendsto (fun R ↦ legalMarkedScalePressure (finrank ℝ S.covector.ker) id id μ ν
        (fun a b v ↦ matrixQuadratic (originalSeedPairCoefficient S w (a,b)) v) g R t)
          atTop (𝓝 (pref t))) ∧
      (∀ n t, Tendsto (fun R ↦ legalMarkedScalePressure (finrank ℝ S.covector.ker) id id
        ((πret n).map measurable_fst.aemeasurable : Measure ℝ)
        ((πret n).map measurable_snd.aemeasurable : Measure ℝ)
        (fun a b v ↦ matrixQuadratic (originalSeedPairCoefficient S w (a,b)) v) g R t)
          atTop (𝓝 (p n t))) ∧
      LipschitzWith ⟨G,hG⟩ pref ∧ (∀ n, LipschitzWith ⟨G,hG⟩ (p n)) ∧
      ∀ t ε, 0 < ε → ∀ᶠ n in atTop, p n t < pref t + ε := by
  letI : IsProbabilityMeasure μ := D.support.source.probability
  letI : IsProbabilityMeasure ν := D.support.target.probability
  haveI : IsProbabilityMeasure (π.map Prod.fst) := hπ.1.symm ▸ D.support.source.probability
  haveI : IsProbabilityMeasure π := Measure.isProbabilityMeasure_of_map Prod.fst
  let α : ProbabilityMeasure ℝ := ⟨μ,inferInstance⟩
  let β : ProbabilityMeasure ℝ := ⟨ν,inferInstance⟩
  let pairLaw : ProbabilityMeasure (ℝ × ℝ) := ⟨π,inferInstance⟩
  let I : Set ℝ := μ.support ∪ ν.support
  have hI : IsCompact I := hbounds.source_compact.union hbounds.target_compact
  obtain ⟨coarse⟩ := exists_finiteScalarBins hI hgap
  have hsource : ∀ᵐ p ∂π, p.1 ∈ μ.support :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [hπ.1]; exact μ.support_mem_ae)
  have htarget : ∀ᵐ p ∂π, p.2 ∈ ν.support :=
    ae_of_ae_map measurable_snd.aemeasurable (by rw [hπ.2]; exact ν.support_mem_ae)
  have hcarry : ∀ᵐ p ∂π, p.1 ∈ I ∧ p.2 ∈ I :=
    (hsource.and htarget).mono (fun _ h ↦ ⟨Or.inl h.1,Or.inr h.2⟩)
  have hsep : ∀ᵐ p ∂μ.prod ν, gap ≤ |p.2 - p.1| := by
    filter_upwards [ae_fst_of_ae μ.support_mem_ae,ae_snd_of_ae ν.support_mem_ae] with p hpS hpT
    simpa only [Real.dist_eq,abs_sub_comm] using hbounds.separated p.1 hpS p.2 hpT
  have hvarS : Tendsto (fun _n : ℕ ↦
      ((α : Measure ℝ).toSignedMeasure - (α : Measure ℝ).toSignedMeasure).totalVariation.real univ)
      atTop (𝓝 0) := by
    simp only [sub_self,SignedMeasure.totalVariation_zero,measureReal_zero_apply]
    exact tendsto_const_nhds
  have hvarT : Tendsto (fun _n : ℕ ↦
      ((β : Measure ℝ).toSignedMeasure - (β : Measure ℝ).toSignedMeasure).totalVariation.real univ)
      atTop (𝓝 0) := by
    simp only [sub_self,SignedMeasure.totalVariation_zero,measureReal_zero_apply]
    exact tendsto_const_nhds
  obtain ⟨C,hC,hkb⟩ := D.exists_originalFocalKinetic_quadratic_bound hF hw hgap hbounds
  obtain ⟨πret,hπret,pref,p,href,hpt,hupper⟩ := exists_legalMarkedPressure_upper_of_original_retained_variation
    (finrank ℝ S.covector.ker) hq hI.measurableSet coarse hgap id id measurable_id measurable_id
    (fun _ ↦ α) (fun _ ↦ β) α β hvarS hvarT pairLaw hπ hcarry
    (hbounds.ae_clock_gap_of_coupling hπ horder) hsep
    (fun _ ↦ pairLaw) (fun _ ↦ hπ) (fun _ ↦ hcarry)
    (fun _ ↦ hbounds.ae_clock_gap_of_coupling hπ horder) (fun _ ↦ hsep)
    χ hχ δ hδ hδ0 hδ1 hmass hC hG (D.originalFocalKinetic gap)
    (D.measurable_originalFocalKinetic hF hw gap) (D.originalFocalKinetic_nonneg hF hw hgap)
    hkb (fun a b c _ v ↦ D.originalFocalKinetic_homogeneous gap a b c v) g hg hgb
  have hac n : normalizedFiniteLaw (χ n) ≪ π := (Measure.absolutelyContinuous_of_le (hχ n)).smul_left _
  have hα n : ((πret n).map measurable_fst.aemeasurable : Measure ℝ) ≪ μ := by
    rw [← hπ.1]
    change (πret n : Measure (ℝ × ℝ)).map Prod.fst ≪ π.map Prod.fst
    rw [hπret n]
    exact (hac n).map measurable_fst
  have hβ n : ((πret n).map measurable_snd.aemeasurable : Measure ℝ) ≪ ν := by
    rw [← hπ.2]
    change (πret n : Measure (ℝ × ℝ)).map Prod.snd ≪ π.map Prod.snd
    rw [hπret n]
    exact (hac n).map measurable_snd
  have hlip (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
      (P : ℝ → ℝ)
      (hP : ∀ t, Tendsto (fun R ↦ legalMarkedScalePressure (finrank ℝ S.covector.ker) id id α β
        (D.originalFocalKinetic gap) g R t) atTop (𝓝 (P t))) : LipschitzWith ⟨G,hG⟩ P := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simp only [Real.dist_eq]
    apply le_of_tendsto (((hP a).sub (hP b)).abs)
    exact Filter.Eventually.of_forall fun R ↦ legalMarkedScalePressure_lipschitz
      (finrank ℝ S.covector.ker) measurable_id measurable_id α β hC hG
      (D.measurable_originalFocalKinetic hF hw gap) (fun a b _ ↦ hkb a b) hg
      (fun a b _ ↦ hgb a b) R a b
  refine ⟨πret,hπret,pref,p,?_,?_,hlip μ ν pref href,?_,hupper⟩
  · intro t
    exact (href t).congr' (Filter.Eventually.of_forall fun R ↦
      D.original_focal_scalePressure_eq_actual_coefficient hbounds μ ν
        Measure.AbsolutelyContinuous.rfl Measure.AbsolutelyContinuous.rfl g R t)
  · intro n t
    exact (hpt n t).congr' (Filter.Eventually.of_forall fun R ↦
      D.original_focal_scalePressure_eq_actual_coefficient hbounds
        ((πret n).map measurable_fst.aemeasurable : Measure ℝ)
        ((πret n).map measurable_snd.aemeasurable : Measure ℝ) (hα n) (hβ n) g R t)
  · intro n
    exact hlip ((πret n).map measurable_fst.aemeasurable : Measure ℝ)
      ((πret n).map measurable_snd.aemeasurable : Measure ℝ) (p n) (hpt n)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
