import OTSelector.Reconstruction.OriginalMinimizerDyadicTrafficNorm

/-! # Selected bad-event moments for either unchanged original Poisson color

The deterministic physical envelopes may depend on the scale and endpoint color. All random
counts, bad events and selected currents retain the same original matching scene law. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OriginalSeedConditionalMoments
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- The physical mark law belonging to one of the two original input colors. -/
def originalMarkedColorLaw (α β : Measure ℝ) (color : Fin 2) : Measure ℝ :=
  if color = 0 then α else β

/-- The unchanged original input count in a deterministic physical envelope and color. -/
def originalMarkedEnvelopeCount (color : Fin 2) (V : Set (LegalMarkedPhysicalPoint q))
    (scene : LegalMarkedOptimalInputScene q) : ℝ :=
  ((scene.2 : Measure (LegalColoredInputPoint q)) (V ×ˢ {color})).toReal

/-- Either original Poisson color has the same dependent bad-event second-moment estimate.
The target case uses its own target intensity and the same matching law. -/
theorem LegalWeightedStationaryPoissonMatching.original_color_badEvent_second_moment
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (color : Fin 2)
    {V : Set (LegalMarkedPhysicalPoint q)} (hV : MeasurableSet V)
    (hfin : ((volume : Measure (Fin q → ℝ)).prod (originalMarkedColorLaw α β color)) V ≠ ∞)
    {B : Set (LegalMarkedOptimalInputScene q)} (hB : MeasurableSet B) :
    Integrable (fun scene ↦ (B.indicator (originalMarkedEnvelopeCount color V) scene) ^ 2)
        (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ scene, (B.indicator (originalMarkedEnvelopeCount color V) scene) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤
        (192 * Real.exp (Real.exp 1 - 1) *
          (1 + (((volume : Measure (Fin q → ℝ)).prod
            (originalMarkedColorLaw α β color)) V).toReal ^ 4)) ^ (1 / 2 : ℝ) *
          ((Q.law : Measure (LegalMarkedOptimalInputScene q)).real B) ^ (1 / 2 : ℝ) := by
  unfold originalMarkedEnvelopeCount
  fin_cases color
  · simpa [originalMarkedColorLaw, originalMarkedEnvelopeCount] using
      Q.original_source_badEvent_second_moment hV hfin hB
  · simpa [originalMarkedColorLaw, originalMarkedEnvelopeCount] using
      Q.original_target_badEvent_second_moment hV hfin hB

/-- Original intensity and actual bad-event probability imply the fixed-scale square bound. -/
theorem LegalWeightedStationaryPoissonMatching.originalMarkedCount_bad_second_moment_le_exp
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (color : Fin 2)
    {V : Set (LegalMarkedPhysicalPoint q)} (hV : MeasurableSet V)
    {B : Set (LegalMarkedOptimalInputScene q)} (hB : MeasurableSet B)
    {Λ r K : ℝ} (hΛ : 0 ≤ Λ) (hr : 0 ≤ r) (m : ℕ)
    (hIntensity : ((volume : Measure (Fin q → ℝ)).prod
      (originalMarkedColorLaw α β color)) V ≤ ENNReal.ofReal ((2 * (m : ℝ) + r) ^ q * Λ))
    (hProb : (Q.law : Measure (LegalMarkedOptimalInputScene q)).real B ≤
      Real.exp (-(K - (3 * (2 * q : ℝ) + (3 : ℝ) ^ (2 * q)) -
        2 * ((r + 2) ^ q * Λ) * (Real.exp 1 - 1)) * (m : ℝ))) :
    Integrable (fun scene ↦ (B.indicator (originalMarkedEnvelopeCount color V) scene) ^ 2)
        (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ scene, (B.indicator (originalMarkedEnvelopeCount color V) scene) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤
        (192 * Real.exp (Real.exp 1 - 1) *
          (1 + ((2 * (m : ℝ) + r) ^ q * Λ) ^ 4)) ^ (1 / 2 : ℝ) *
          Real.exp ((-(K - (3 * (2 * q : ℝ) + (3 : ℝ) ^ (2 * q)) -
            2 * ((r + 2) ^ q * Λ) * (Real.exp 1 - 1)) * (m : ℝ)) * (1 / 2 : ℝ)) := by
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hIntensity
  have hb := Q.original_color_badEvent_second_moment color hV hfin hB
  refine ⟨hb.1, hb.2.trans ?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hIntensity
  rw [ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg (by positivity) _) hΛ)] at hreal
  calc
    _ ≤ (192 * Real.exp (Real.exp 1 - 1) *
        (1 + ((2 * (m : ℝ) + r) ^ q * Λ) ^ 4)) ^ (1 / 2 : ℝ) *
        ((Q.law : Measure (LegalMarkedOptimalInputScene q)).real B) ^ (1 / 2 : ℝ) := by
      gcongr
    _ ≤ _ := by
      rw [Real.exp_mul]
      gcongr

/-- The explicit threshold makes either original color's bad count squares summable. -/
theorem LegalWeightedStationaryPoissonMatching.originalMarkedCount_bad_summable_le_exp
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (color : Fin 2)
    (V : ℕ → Set (LegalMarkedPhysicalPoint q))
    (B : ℕ → Set (LegalMarkedOptimalInputScene q))
    (hV : ∀ m, MeasurableSet (V m)) (hB : ∀ m, MeasurableSet (B m))
    {Λ r K : ℝ} (hΛ : 0 ≤ Λ) (hr : 0 ≤ r)
    (hIntensity : ∀ m, 1 ≤ m → ((volume : Measure (Fin q → ℝ)).prod
      (originalMarkedColorLaw α β color)) (V m) ≤
        ENNReal.ofReal ((2 * (m : ℝ) + r) ^ q * Λ))
    (hProb : ∀ m, 1 ≤ m → (Q.law : Measure (LegalMarkedOptimalInputScene q)).real (B m) ≤
      Real.exp (-(K - (3 * (2 * q : ℝ) + (3 : ℝ) ^ (2 * q)) -
        2 * ((r + 2) ^ q * Λ) * (Real.exp 1 - 1)) * (m : ℝ)))
    (hK : commonScaleSourceCountThreshold q Λ r ≤ K) :
    (∀ m : ℕ, 1 ≤ m → Integrable (fun scene ↦
      ((B m).indicator (originalMarkedEnvelopeCount color (V m)) scene) ^ 2)
        (Q.law : Measure (LegalMarkedOptimalInputScene q))) ∧
      Summable (fun m : ℕ ↦ ∫ scene,
        ((B m).indicator (originalMarkedEnvelopeCount color (V m)) scene) ^ 2
          ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ∧
      (∑' n : ℕ, ∫ scene,
        ((B (n + 1)).indicator (originalMarkedEnvelopeCount color (V (n + 1))) scene) ^ 2
          ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤
        commonScaleSourceEnvelopeBudget q Λ r *
          Real.exp (-(K - commonScaleSourceCountThreshold q Λ r) / 2) := by
  let a : ℕ → ℝ := fun m ↦
    (192 * Real.exp (Real.exp 1 - 1) *
      (1 + ((2 * (m : ℝ) + r) ^ q * Λ) ^ 4)) ^ (1 / 2 : ℝ) *
        Real.exp (-(m : ℝ) / 2)
  let J : ℕ → ℝ := fun m ↦ ∫ scene,
    ((B m).indicator (originalMarkedEnvelopeCount color (V m)) scene) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))
  let Δ := K - commonScaleSourceCountThreshold q Λ r
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr hK
  have ha : Summable a := summable_polynomialFourthRoot_exp_neg_half_nat q (by positivity) hr
  have hfixed (m : ℕ) (hm : 1 ≤ m) :=
    Q.originalMarkedCount_bad_second_moment_le_exp color (hV m) (hB m) hΛ hr m
      (hIntensity m hm) (hProb m hm)
  have hbound (m : ℕ) (hm : 1 ≤ m) : J m ≤ a m * Real.exp (-Δ / 2) := by
    apply (hfixed m hm).2.trans
    dsimp only [a]
    simp only [mul_assoc]
    rw [← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
    apply Real.exp_le_exp.mpr
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hΔm := mul_nonneg hΔ (sub_nonneg.mpr hm')
    dsimp only [Δ, commonScaleSourceCountThreshold] at hΔm ⊢
    nlinarith
  have hJ : Summable J := by
    apply (ha.mul_right (Real.exp (-Δ / 2))).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop 1] with m hm
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ ↦ sq_nonneg _))]
    exact hbound m hm
  refine ⟨fun m hm ↦ (hfixed m hm).1, hJ, ?_⟩
  have hshift := (summable_nat_add_iff 1).2 hJ
  have hashift := (summable_nat_add_iff 1).2 ha
  calc
    _ ≤ ∑' n : ℕ, a (n + 1) * Real.exp (-Δ / 2) :=
      hshift.tsum_le_tsum (fun n ↦ hbound (n + 1) (by omega)) (hashift.mul_right _)
    _ = _ := by rw [tsum_mul_right]; rfl

/-- A random selected bad current dominated by either original color inherits the exact
common-scale budget. Neither independence from the bad event nor a new input law is used. -/
theorem LegalWeightedStationaryPoissonMatching.originalMarkedCount_selected_bad_memLp_two_le
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (color : Fin 2)
    (V : ℕ → Set (LegalMarkedPhysicalPoint q))
    (B : ℕ → Set (LegalMarkedOptimalInputScene q))
    (hV : ∀ m, MeasurableSet (V m)) (hB : ∀ m, MeasurableSet (B m))
    {Λ r K : ℝ} (hΛ : 0 ≤ Λ) (hr : 0 ≤ r)
    (hIntensity : ∀ m, 1 ≤ m → ((volume : Measure (Fin q → ℝ)).prod
      (originalMarkedColorLaw α β color)) (V m) ≤
        ENNReal.ofReal ((2 * (m : ℝ) + r) ^ q * Λ))
    (hProb : ∀ m, 1 ≤ m → (Q.law : Measure (LegalMarkedOptimalInputScene q)).real (B m) ≤
      Real.exp (-(K - (3 * (2 * q : ℝ) + (3 : ℝ) ^ (2 * q)) -
        2 * ((r + 2) ^ q * Λ) * (Real.exp 1 - 1)) * (m : ℝ)))
    (hK : commonScaleSourceCountThreshold q Λ r ≤ K)
    {k : LegalMarkedOptimalInputScene q → ℕ} (hk : Measurable k)
    {f : LegalMarkedOptimalInputScene q → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C)
    (hdom : ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      scene ∈ B (k scene) →
        |f scene| ≤ C * |originalMarkedEnvelopeCount color (V (k scene)) scene|) :
    let err := {scene | 1 ≤ k scene ∧ scene ∈ B (k scene)}.indicator f
    let budget : ℝ := C ^ 2 * commonScaleSourceEnvelopeBudget q Λ r *
      Real.exp (-(K - commonScaleSourceCountThreshold q Λ r) / 2)
    MemLp err 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ scene, (err scene) ^ 2 ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤ budget ∧
      eLpNorm err 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) ≤
        ENNReal.ofReal (Real.sqrt budget) := by
  dsimp only
  let A := {scene | 1 ≤ k scene ∧ scene ∈ B (k scene)}
  have hs := Q.originalMarkedCount_bad_summable_le_exp color V B hV hB hΛ hr
    hIntensity hProb hK
  have he := integrable_selected_bad_sq_and_integral_le_tsum hk hB hf hC hdom
    hs.1 hs.2.1 (N := 1) le_rfl
  have hI : Integrable (fun scene ↦ (A.indicator f scene) ^ 2)
      (Q.law : Measure (LegalMarkedOptimalInputScene q)) := he.1
  have hm : (∫ scene, (A.indicator f scene) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤
      C ^ 2 * commonScaleSourceEnvelopeBudget q Λ r *
        Real.exp (-(K - commonScaleSourceCountThreshold q Λ r) / 2) := by
    calc
      _ ≤ C ^ 2 * ∑' n : ℕ, ∫ scene,
          ((B (n + 1)).indicator (originalMarkedEnvelopeCount color (V (n + 1))) scene) ^ 2
            ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)) := he.2
      _ ≤ C ^ 2 * (commonScaleSourceEnvelopeBudget q Λ r *
          Real.exp (-(K - commonScaleSourceCountThreshold q Λ r) / 2)) :=
        mul_le_mul_of_nonneg_left hs.2.2 (sq_nonneg C)
      _ = _ := (mul_assoc _ _ _).symm
  have hsel : MeasurableSet {scene | scene ∈ B (k scene)} := by
    have heq : {scene | scene ∈ B (k scene)} =
        ⋃ m : ℕ, {scene | k scene = m} ∩ B m := by
      ext scene
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
      exact ⟨fun hs ↦ ⟨k scene, rfl, hs⟩, fun ⟨m, hm, hs⟩ ↦ hm.symm ▸ hs⟩
    rw [heq]
    exact MeasurableSet.iUnion (fun m ↦
      ((measurableSet_singleton m).preimage hk).inter (hB m))
  have hAm : MeasurableSet A := (measurableSet_le measurable_const hk).inter hsel
  have hLp : MemLp (A.indicator f) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) :=
    (memLp_two_iff_integrable_sq (hf.indicator hAm).aestronglyMeasurable).mpr hI
  exact ⟨hLp, hm, eLpNorm_two_le_sqrt_of_integral_sq_le hLp hm⟩

end OTSelector.Reconstruction
