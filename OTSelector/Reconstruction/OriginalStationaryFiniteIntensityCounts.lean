import OTSelector.Probability.PoissonCountExhaustion
import OTSelector.Reconstruction.OriginalStationaryCompactSetCounts

/-! Full original stationary count estimates on arbitrary finite-intensity sets. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

private theorem original_color_count_eq {q : ℕ}
    (s : LegalMarkedOptimalInputScene q) (c : Fin 2)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B) :
    (s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {c}) =
      legalInputColorMeasure q s.2 c B := by
  rw [legalInputColorMeasure, Measure.map_apply measurable_fst hB,
    Measure.restrict_apply (hB.preimage measurable_fst)]
  congr 1

private theorem original_color_count_mean {q : ℕ}
    (P : Measure (LegalMarkedOptimalInputScene q)) (c : Fin 2)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B) :
    (∫⁻ s, (s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {c}) ∂P) =
      legalMarkedInputColorIntensity q P c B := by
  rw [← lintegral_legalInputColorMeasure_eq_intensity q P c hB]
  exact lintegral_congr (fun s ↦ original_color_count_eq s c hB)

private theorem original_color_exp_moment_of_compact_laws
    {q : ℕ} {P : Measure (LegalMarkedOptimalInputScene q)} (c : Fin 2)
    (ν : Measure (LegalMarkedPhysicalPoint q))
    (hν : legalMarkedInputColorIntensity q P c = ν)
    (hlaw : ∀ {A K : Set (LegalMarkedPhysicalPoint q)}, MeasurableSet A → IsCompact K →
      A ⊆ K → HasLaw (fun s ↦ (s.2 : Measure (LegalColoredInputPoint q)) (A ×ˢ {c}))
        ((poissonMeasure (ν A).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)) P)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B) (hfin : ν B ≠ ∞)
    {t : ℝ} (ht : 0 ≤ t) :
    (∀ᵐ s ∂P, (s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {c}) < ∞) ∧
      Integrable (fun s ↦ Real.exp (t *
        ((s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {c})).toReal)) P ∧
      (∫ s, Real.exp (t * ((s.2 : Measure (LegalColoredInputPoint q))
        (B ×ˢ {c})).toReal) ∂P) ≤ Real.exp ((ν B).toReal * (Real.exp t - 1)) := by
  let K := compactCovering (LegalMarkedPhysicalPoint q)
  let Bn : ℕ → Set (LegalColoredInputPoint q) := fun n ↦ (B ∩ K n) ×ˢ {c}
  have hmono : Monotone Bn := fun _ _ h ↦
    prod_mono (inter_subset_inter_right B (compactCovering_subset _ h)) Subset.rfl
  have hunion : (⋃ n, Bn n) = B ×ˢ {c} := by
    ext x
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, h⟩
      exact ⟨h.1.1, h.2⟩
    · intro hx
      obtain ⟨n, hn⟩ := exists_mem_compactCovering x.1
      exact mem_iUnion.mpr ⟨n, ⟨hx.1, hn⟩, hx.2⟩
  have hm : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      (s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {c})) :=
    (Measure.measurable_coe (hB.prod (measurableSet_singleton c))).comp
      (measurable_localFiniteMeasure_coe.comp measurable_snd)
  have hmean : (∫⁻ s, (s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {c}) ∂P) ≠ ∞ := by
    rwa [original_color_count_mean P c hB, hν]
  have hn (n : ℕ) : HasLaw (fun s : LegalMarkedOptimalInputScene q ↦
      (s.2 : Measure (LegalColoredInputPoint q)) (Bn n))
      ((poissonMeasure (ν (B ∩ K n)).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)) P :=
    hlaw (hB.inter (isCompact_compactCovering _ n).measurableSet)
      (isCompact_compactCovering _ n) inter_subset_right
  have hr (n : ℕ) : (ν (B ∩ K n)).toNNReal ≤ (ν B).toNNReal :=
    ENNReal.toNNReal_mono hfin (measure_mono inter_subset_left)
  simpa only [ENNReal.toReal] using
    finite_count_and_exp_moment_of_poisson_measure_exhaustion
      (fun s : LegalMarkedOptimalInputScene q ↦ (s.2 : Measure (LegalColoredInputPoint q)))
      hmono hunion hm.aemeasurable hmean hn hr ht

/-- Every measurable set with finite original source intensity has the full
original Poisson exponential bound. Compact support of the set is unnecessary. -/
theorem LegalWeightedStationaryPoissonMatching.original_source_exp_moment_of_finite_intensity
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B)
    (hfin : ((volume : Measure (Fin q → ℝ)).prod α) B ≠ ∞)
    {t : ℝ} (ht : 0 ≤ t) :
    (∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      (s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {0}) < ∞) ∧
      Integrable (fun s ↦ Real.exp (t *
        ((s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {0})).toReal))
        (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, Real.exp (t * ((s.2 : Measure (LegalColoredInputPoint q))
        (B ×ˢ {0})).toReal) ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤
          Real.exp ((((volume : Measure (Fin q → ℝ)).prod α) B).toReal * (Real.exp t - 1)) :=
  original_color_exp_moment_of_compact_laws 0 _ M.inputColorIntensities_eq_volume_prod.1
    (fun hA hK hAK ↦ M.original_source_countLaw_of_compact_carrier hA hK hAK) hB hfin ht

/-- The same estimate holds for the complete unchanged original target input. -/
theorem LegalWeightedStationaryPoissonMatching.original_target_exp_moment_of_finite_intensity
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B)
    (hfin : ((volume : Measure (Fin q → ℝ)).prod β) B ≠ ∞)
    {t : ℝ} (ht : 0 ≤ t) :
    (∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      (s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {1}) < ∞) ∧
      Integrable (fun s ↦ Real.exp (t *
        ((s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {1})).toReal))
        (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, Real.exp (t * ((s.2 : Measure (LegalColoredInputPoint q))
        (B ×ˢ {1})).toReal) ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤
          Real.exp ((((volume : Measure (Fin q → ℝ)).prod β) B).toReal * (Real.exp t - 1)) :=
  original_color_exp_moment_of_compact_laws 1 _ M.inputColorIntensities_eq_volume_prod.2
    (fun hA hK hAK ↦ M.original_target_countLaw_of_compact_carrier hA hK hAK) hB hfin ht

end OTSelector.Reconstruction
