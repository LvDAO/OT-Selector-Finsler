import OTSelector.Reconstruction.OriginalStationaryFiniteIntensityCounts
import OTSelector.Probability.OriginalPoissonMaskedQuadraticCost
import OTSelector.Probability.FiniteIntensityCountFatou

/-! Genuine full-clock Poisson count deviations from compact exhaustion and original intensity. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The actual extended-real Poisson count retains the ordinary centered first moment. -/
theorem originalActualCount_poisson_deviation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ≥0∞} {r : ℝ≥0}
    (hlaw : HasLaw X ((poissonMeasure r).map (Nat.cast : ℕ → ℝ≥0∞)) P) :
    Integrable (fun ω ↦ |(X ω).toReal - (r:ℝ)|) P ∧
      (∫ ω, |(X ω).toReal - (r:ℝ)| ∂P) ≤ Real.sqrt (r:ℝ) := by
  let f : ℝ≥0∞ → ℝ := fun x ↦ |x.toReal - (r:ℝ)|
  have hf : Measurable f := (measurable_id.ennreal_toReal.sub measurable_const).abs
  have hi : Integrable f ((poissonMeasure r).map (Nat.cast : ℕ → ℝ≥0∞)) := by
    apply (integrable_map_measure hf.aestronglyMeasurable measurable_from_nat.aemeasurable).mpr
    simpa only [f, Function.comp_def, ENNReal.toReal_natCast, Pi.sub_apply] using
      ((integrable_id_poissonMeasure r).sub (integrable_const (r:ℝ))).abs
  have hi' : Integrable f (P.map X) := hlaw.map_eq.symm ▸ hi
  refine ⟨(integrable_map_measure hf.aestronglyMeasurable hlaw.aemeasurable).mp hi', ?_⟩
  calc
    _ = ∫ x, f x ∂(poissonMeasure r).map (Nat.cast : ℕ → ℝ≥0∞) :=
      hlaw.integral_comp hf.aestronglyMeasurable
    _ = ∫ n : ℕ, |(n:ℝ) - (r:ℝ)| ∂poissonMeasure r := by
      rw [integral_map measurable_from_nat.aemeasurable hf.aestronglyMeasurable]
      simp only [f, ENNReal.toReal_natCast]
    _ ≤ _ := integral_abs_sub_id_poissonMeasure_le r

/-- Compact Poisson counts converging to a finite full original count yield its centered
sqrt-rate deviation by Fatou, without assigning a new law to selected points. -/
theorem originalActualCount_deviation_of_poisson_exhaustion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ≥0∞} {Xn : ℕ → Ω → ℝ≥0∞} {r : ℝ≥0} {rn : ℕ → ℝ≥0}
    (hX : AEMeasurable X P) (hmean : (∫⁻ ω, X ω ∂P) ≠ ∞)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ Xn n ω) atTop (𝓝 (X ω)))
    (hlaw : ∀ n, HasLaw (Xn n) ((poissonMeasure (rn n)).map
      (Nat.cast : ℕ → ℝ≥0∞)) P)
    (hr : ∀ n, rn n ≤ r) (hrlim : Tendsto (fun n ↦ (rn n:ℝ)) atTop (𝓝 (r:ℝ))) :
    Integrable (fun ω ↦ |(X ω).toReal - (r:ℝ)|) P ∧
      (∫ ω, |(X ω).toReal - (r:ℝ)| ∂P) ≤ Real.sqrt (r:ℝ) := by
  have hfinite := ae_lt_top' hX hmean
  have hm := fun n ↦ originalActualCount_poisson_deviation (hlaw n)
  apply integrable_and_integral_le_of_nonneg_ae_limit (fun n ↦ (hm n).1)
    (fun _ ↦ Eventually.of_forall (fun _ ↦ abs_nonneg _))
    (hX.ennreal_toReal.sub_const (r:ℝ)).abs.aestronglyMeasurable
    (Eventually.of_forall (fun _ ↦ abs_nonneg _)) (Real.sqrt_nonneg _) ?_ ?_
  · filter_upwards [hfinite, hlim] with ω hω hlimω
    exact (((ENNReal.tendsto_toReal hω.ne).comp hlimω).sub hrlim).abs
  · intro n
    exact (hm n).2.trans (Real.sqrt_le_sqrt (by exact_mod_cast hr n))

/-- The unchanged colored input mean on any measurable physical set equals its actual
physical intensity, including physical sets containing all scalar clocks. -/
theorem lintegral_originalActualInputColorCount_eq_intensity
    {q : ℕ} (P : Measure (LegalMarkedOptimalInputScene q)) (c : Fin 2)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B) :
    (∫⁻ s, (s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {c}) ∂P) =
      legalMarkedInputColorIntensity q P c B := by
  rw [← lintegral_legalInputColorMeasure_eq_intensity q P c hB]
  apply lintegral_congr
  intro s
  rw [legalInputColorMeasure, Measure.map_apply measurable_fst hB,
    Measure.restrict_apply (hB.preimage measurable_fst)]
  congr 1

/-- The actual full input count on any finite-intensity set has its exact mean and
sqrt-intensity centered deviation. Compact carriers are exhausted internally. -/
theorem originalActualInputColorCount_moments_of_compact_laws
    {q : ℕ} (P : Measure (LegalMarkedOptimalInputScene q)) (c : Fin 2)
    (ν : Measure (LegalMarkedPhysicalPoint q))
    (hν : legalMarkedInputColorIntensity q P c = ν)
    (hlaw : ∀ {A K : Set (LegalMarkedPhysicalPoint q)}, MeasurableSet A → IsCompact K →
      A ⊆ K → HasLaw (fun s ↦ (s.2 : Measure (LegalColoredInputPoint q)) (A ×ˢ {c}))
        ((poissonMeasure (ν A).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)) P)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B) (hfin : ν B ≠ ∞) :
    (∀ᵐ s ∂P, (s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {c}) < ∞) ∧
    Integrable (fun s ↦ ((s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {c})).toReal) P ∧
    (∫ s, ((s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {c})).toReal ∂P) = (ν B).toReal ∧
    (∫ s, |((s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {c})).toReal - (ν B).toReal|
      ∂P) ≤ Real.sqrt (ν B).toReal := by
  let K := compactCovering (LegalMarkedPhysicalPoint q)
  let Bn : ℕ → Set (LegalColoredInputPoint q) := fun n ↦ (B ∩ K n) ×ˢ {c}
  have hmono : Monotone Bn := fun _ _ h ↦
    prod_mono (inter_subset_inter_right B (compactCovering_subset _ h)) Subset.rfl
  have hunion : (⋃ n, Bn n) = B ×ˢ {c} := by
    ext x
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, h⟩
      exact ⟨h.1.1,h.2⟩
    · intro hx
      obtain ⟨n,hn⟩ := exists_mem_compactCovering x.1
      exact mem_iUnion.mpr ⟨n,⟨hx.1,hn⟩,hx.2⟩
  have hm : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      (s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {c})) :=
    (Measure.measurable_coe (hB.prod (measurableSet_singleton c))).comp
      (measurable_localFiniteMeasure_coe.comp measurable_snd)
  have hmean : (∫⁻ s, (s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {c}) ∂P) = ν B := by
    rw [lintegral_originalActualInputColorCount_eq_intensity P c hB, hν]
  have hfinite := ae_lt_top hm (hmean.trans_ne hfin)
  refine ⟨hfinite, integrable_toReal_of_lintegral_ne_top hm.aemeasurable (hmean.trans_ne hfin),
    (integral_toReal hm.aemeasurable hfinite).trans (congrArg ENNReal.toReal hmean), ?_⟩
  apply (originalActualCount_deviation_of_poisson_exhaustion
    (r := (ν B).toNNReal) (rn := fun n ↦ (ν (B ∩ K n)).toNNReal)
    (Xn := fun n s ↦ (s.2 : Measure (LegalColoredInputPoint q)) (Bn n))
    hm.aemeasurable (hmean.trans_ne hfin) ?_ ?_ ?_ ?_).2
  · apply Eventually.of_forall
    intro s
    simpa only [hunion, Function.comp_def] using
      (tendsto_measure_iUnion_atTop (μ := (s.2 : Measure (LegalColoredInputPoint q))) hmono)
  · intro n
    exact hlaw (hB.inter (isCompact_compactCovering _ n).measurableSet)
      (isCompact_compactCovering _ n) inter_subset_right
  · intro n
    exact ENNReal.toNNReal_mono hfin (measure_mono inter_subset_left)
  · change Tendsto (fun n ↦ (ν (B ∩ K n)).toReal) atTop (𝓝 (ν B).toReal)
    apply (ENNReal.tendsto_toReal hfin).comp
    have hmono' : Monotone (fun n ↦ B ∩ K n) := fun _ _ h ↦
      inter_subset_inter_right B (compactCovering_subset _ h)
    have hunion' : (⋃ n, B ∩ K n) = B := by
      ext x
      simp only [mem_iUnion, mem_inter_iff]
      constructor
      · rintro ⟨_,hx,_⟩
        exact hx
      · intro hx
        obtain ⟨n,hn⟩ := exists_mem_compactCovering x
        exact ⟨n,hx,hn⟩
    simpa only [hunion', Function.comp_def] using (tendsto_measure_iUnion_atTop (μ := ν) hmono')

end OTSelector.Reconstruction
