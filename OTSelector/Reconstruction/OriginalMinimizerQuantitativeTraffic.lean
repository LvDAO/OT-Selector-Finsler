import OTSelector.Reconstruction.OriginalMinimizerCompleteWindowTrafficLtwo

/-! Explicit actual original-input count budgets for complete-window traffic.
The count-envelope constants depend only on the unchanged original cell
intensities; the minimizer and its selected edges receive no new Poisson law. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator Classical BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "q" => finrank ℝ S.covector.ker

/-- A deterministic finite original-source envelope budget. Its only measure
input is the literal unit normalized cell intensity of the original source. -/
def originalSourceBadTrafficEnvelopeBudget
    (T : Matrix (Fin q) (Fin q) ℝ) (cut r : ℝ) : ℝ :=
  ∑' n : ℕ, (192 * Real.exp (Real.exp 1-1) *
    (1 + ((2*((n+1:ℕ):ℝ)+r)^q *
      (((volume : Measure (Fin q → ℝ)).prod μ)
        (D.normalizedSourcePhaseCell T cut 0 0 1)).toReal)^4))^(1/2:ℝ) *
    Real.exp (-((n+1:ℕ):ℝ)/2)

theorem originalSourceBadTrafficEnvelopeBudget_nonneg
    (T : Matrix (Fin q) (Fin q) ℝ) (cut r : ℝ) :
    0 ≤ D.originalSourceBadTrafficEnvelopeBudget T cut r :=
  tsum_nonneg (fun _ ↦ by positivity)

/-- The exact original Poisson fourth-moment envelope yields exponential
decay in the adjustable count threshold, uniformly over all current scales.
No selected cloud or selected scale is assigned a Poisson distribution. -/
theorem original_source_bad_count_sq_tsum_le_exp
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin q) (Fin q) ℝ) [Invertible T]
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
    {r K : ℝ} (hr : 0 ≤ r)
    (hK : D.normalizedSourcePhaseCurveCountThreshold T cut r ≤ K) :
    (∑' n : ℕ, ∫ scene,
      ((D.normalizedSourcePhaseCurveBadEvent T cut (n+1) r K).indicator
        (D.normalizedGlobalSourceEnvelopeCount T cut (n+1) r) scene)^2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤
      D.originalSourceBadTrafficEnvelopeBudget T cut r *
        Real.exp (-(K-D.normalizedSourcePhaseCurveCountThreshold T cut r)/2) := by
  let v₁ := (((volume : Measure (Fin q → ℝ)).prod μ)
    (D.normalizedSourcePhaseCell T cut 0 0 1)).toReal
  let v := (((volume : Measure (Fin q → ℝ)).prod μ)
    (D.normalizedSourcePhaseCell T cut 0 0 (r+2))).toReal
  let a : ℕ → ℝ := fun m ↦
    (192*Real.exp (Real.exp 1-1)*(1+((2*(m:ℝ)+r)^q*v₁)^4))^(1/2:ℝ) *
      Real.exp (-(m:ℝ)/2)
  let δ := K-D.normalizedSourcePhaseCurveCountThreshold T cut r
  have hδ : 0 ≤ δ := sub_nonneg.mpr hK
  have ha : Summable a := summable_polynomialFourthRoot_exp_neg_half_nat q (by positivity) hr
  have hashift : Summable (fun n : ℕ ↦ a (n+1)) := (summable_nat_add_iff 1).2 ha
  have hsum := ((summable_nat_add_iff 1).2
    (D.normalizedSourcePhaseCurveBadEvent_globalCount_summable hF hw T hcut Q hr hK).2)
  calc
    _ ≤ ∑' n : ℕ, a (n+1)*Real.exp (-δ/2) := by
      apply hsum.tsum_le_tsum _ (hashift.mul_right _)
      intro n
      have hb := (D.normalizedSourcePhaseCurveBadEvent_globalEnvelope_second_moment
        hF hw T hcut (show 1≤n+1 by omega) Q hr K).2
      apply hb.trans
      change (192*Real.exp (Real.exp 1-1)*(1+((2*((n+1:ℕ):ℝ)+r)^q*v₁)^4))^(1/2:ℝ) *
        Real.exp ((-(K-(3*(2*q:ℝ)+(3:ℝ)^(2*q))-2*v*(Real.exp 1-1))*
          ((n+1:ℕ):ℝ))*(1/2:ℝ)) ≤ a (n+1)*Real.exp (-δ/2)
      dsimp only [a]
      simp only [mul_assoc]
      rw [← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
      apply Real.exp_le_exp.mpr
      have hδmul := mul_nonneg hδ (show 0 ≤ ((n+1:ℕ):ℝ)-1 by
        simp only [Nat.cast_add,Nat.cast_one]
        linarith [Nat.cast_nonneg (α:=ℝ) n])
      dsimp [δ,normalizedSourcePhaseCurveCountThreshold,v] at hδmul ⊢
      nlinarith
    _ = _ := by rw [tsum_mul_right]; rfl

end OriginalSeedConditionalMoments
/-- The bounded actual canonical phase retains the full exponential original
input-count-tail moment and eLpNorm estimates, with no count callback. -/
theorem OriginalSeedConditionalMoments.original_minimizer_boundedPhase_countTail_traffic_ltwo
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T]
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ G) (t : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value t ≤ P.value t)
    {cut h ell a : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (hh : 0 < h)
    (hclockRange : ∀ r ∈ Icc (0 : ℝ) 1, cut + ell * r ∈ Ioo D.lo D.hi)
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r‖ *
        Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2) ≤ (1 / 2 : ℝ))
    {ρ : ℝ} (hR : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r‖ ≤ ρ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞}
    {f : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞}
    (hclock : ∀ m c, f (m, c) ≠ 0 →
      ∃ r ∈ Icc (0 : ℝ) 1, c = cut + S.level + ell * r)
    (hηwindow : ∀ x, η x ≠ 0 → ‖T *ᵥ x‖ ≤ a)
    (hmask : ∀ e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker), ∀ c,
      f ((physicalPairAnchor e).2, c) ≠ 0 →
        e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h)
    (ha : 0 ≤ a) {H : ℝ} (hH : 0 ≤ H)
    (hη : Measurable η) (hf : Measurable f)
    {B : ℝ} (hB : 0 ≤ B)
    (hsingle : ∀ x : Fin (finrank ℝ S.covector.ker) → ℝ,
      ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
      (∫⁻ c : ℝ, η (x + originalSeedPathOffset S w c m) * f (m, c) ∂volume) ≤
        ENNReal.ofReal B) (K : ℝ) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let PB := 2 * H + 2 * ((L : ℝ) * a + b)
    let radius := max PB (a + ρ * PB)
    let W := D.normalizedSourcePhaseCell T cut 0 0 radius
    let Λ := (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ) W).toReal
    let N := fun s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ↦
      ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker))) (W ×ˢ {0})).toReal
    let Small := {s | ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ H}
    let traffic := Small.indicator (fun s ↦
      (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s).toReal)
    MemLp ({s | K<N s}.indicator traffic) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
    (∫ s, ({z | K<N z}.indicator traffic s)^2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
      8*B^2*Real.exp (Λ*(Real.exp 1-1))*Real.exp (-K/2) ∧
    eLpNorm ({s | K<N s}.indicator traffic) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ≤
      ENNReal.ofReal (Real.sqrt 8*B*Real.exp (Λ*(Real.exp 1-1)/2)*Real.exp (-K/4)) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8 * |t| * G / h)
  let PB := 2 * H + 2 * ((L : ℝ) * a + b)
  let radius := max PB (a + ρ * PB)
  let W := D.normalizedSourcePhaseCell T cut 0 0 radius
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  have hd := measurable_originalSeedPathOffset_joint S hF hw
  let V := occupiedPairTrafficContributors (finrank ℝ S.covector.ker) d η f
  let Small := {s | ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ H}
  have hSmall : MeasurableSet Small := measurableSet_le
    (((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm) measurable_const
  have hW := D.measurableSet_normalizedSourcePhaseCell hF hw T hcut 0 0 radius
  have hWfin := D.normalizedSourcePhaseCell_intensity_lt_top hF hw T hcut 0 0 radius
  let mass := ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ) W
  have hmass : mass ≤ ENNReal.ofReal mass.toReal := by
    rw [ENNReal.ofReal_toReal hWfin.ne]
  have hc := D.ae_original_minimizer_boundedPhase_original_counts hF hw hgap hbounds
    T hg hgb t Q hmin hcut hh hclockRange hsmall hR hclock hηwindow hmask ha hH hη hf
  have ht := Q.original_source_countTail_completePath_ltwo_ae_on d hd hη hf hW
    ENNReal.toReal_nonneg hmass hSmall V
    (fun s ↦ measurableSet_occupiedPairTrafficContributors d hd hη hf s) (K := K) hB
    (by
      filter_upwards [hc] with s hs hss _
      refine ⟨ae_occupiedPairTrafficContributors_outside_zero d η f s, ?_, (hs hss).1⟩
      exact ae_of_all _ (fun z ↦ hsingle z.1 z.2))
  exact ht

/-- The actual minimizer current-bad error has an explicit exponential
eLpNorm bound from its unchanged original Poisson envelopes. -/
theorem OriginalSeedConditionalMoments.original_minimizer_canonical_source_bad_ltwo_le_exp
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T]
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ G) (t : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value t ≤ P.value t)
    {cut h ell a : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (hh : 0 < h) (ha : 0 ≤ a)
    (hclockRange : ∀ r ∈ Icc (0 : ℝ) 1, cut + ell * r ∈ Ioo D.lo D.hi)
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r‖ *
        Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2) ≤ (1 / 2 : ℝ))
    {ρ A : ℝ} (hA : 0 ≤ A)
    (hR : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r‖ ≤ ρ)
    (hRLip : ∀ r ∈ Icc (0 : ℝ) 1, ∀ r' ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r -
        originalNormalizedClockMobility S w T (cut + S.level) ell r'‖ ≤ A * |r - r'|)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞}
    {f : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞}
    (hclock : ∀ m c, f (m, c) ≠ 0 →
      ∃ r ∈ Icc (0 : ℝ) 1, c = cut + S.level + ell * r)
    (hηwindow : ∀ x, η x ≠ 0 → ‖T *ᵥ x‖ ≤ a)
    (hmask : ∀ e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker), ∀ c,
      f ((physicalPairAnchor e).2, c) ≠ 0 →
        e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h)
    (hη : Measurable η) (hf : Measurable f)
    (hηfinite : (∫⁻ x, η x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) ≠ (⊤ : ℝ≥0∞))
    (hffinite : (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞))
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ e ∈ legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f,
      (legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker)
        (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f e).toReal ≤ B)
    {K : ℝ} (hK :
      let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
      let b := Real.sqrt (8 * |t| * G / h)
      let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
      (3 * (2 * finrank ℝ S.covector.ker : ℝ) +
        (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) +
        2 * (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
          (D.normalizedSourcePhaseCell T cut 0 0 (radius + 2))).toReal *
            (Real.exp 1 - 1) + 1 ≤ K) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ)/h^2),Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8*|t| *G/h)
    let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
    let k := D.normalizedCanonicalCurveIntegerScale T cut h L ρ A
    let Bad := fun m ↦ D.normalizedSourcePhaseCurveBadEvent T cut m radius K
    let traffic := fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s).toReal
    let errorTraffic := {s | 1≤k s ∧ s ∈ Bad (k s)}.indicator traffic
    let budget := B^2*D.originalSourceBadTrafficEnvelopeBudget T cut radius *
      Real.exp (-(K-D.normalizedSourcePhaseCurveCountThreshold T cut radius)/2)
    MemLp errorTraffic 2 (Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
    (∫ s, (errorTraffic s)^2 ∂(Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤ budget ∧
    eLpNorm errorTraffic 2 (Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ≤
      ENNReal.ofReal (Real.sqrt budget) := by
  dsimp only at hK ⊢
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ)/h^2),Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8*|t| *G/h)
  let radius := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
  let k := D.normalizedCanonicalCurveIntegerScale T cut h L ρ A
  let Bad := fun m ↦ D.normalizedSourcePhaseCurveBadEvent T cut m radius K
  let traffic := fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
    (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s).toReal
  let errorTraffic := {s | 1≤k s ∧ s ∈ Bad (k s)}.indicator traffic
  have hρ : 0≤ρ := (norm_nonneg
    (originalNormalizedClockMobility S w T (cut+S.level) ell 0)).trans
      (hR 0 ⟨le_rfl,zero_le_one⟩)
  have hradius : 0≤radius := by dsimp [radius]; positivity
  have hbad := (D.original_minimizer_completePathTraffic_canonical_source_selected_bad_sq_tail
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hclock hηwindow hmask hη hf hηfinite hffinite hB hbound hK).1 1 le_rfl
  have htail := D.original_source_bad_count_sq_tsum_le_exp hF hw T hcut Q hradius hK
  let budget := B^2*D.originalSourceBadTrafficEnvelopeBudget T cut radius *
    Real.exp (-(K-D.normalizedSourcePhaseCurveCountThreshold T cut radius)/2)
  have hbadI : Integrable (fun s ↦ (errorTraffic s)^2)
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := hbad.1
  have hmean : (∫ s, (errorTraffic s)^2 ∂(Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤ budget := by
    calc
      _ ≤ B^2*∑' n : ℕ, ∫ scene,
          ((D.normalizedSourcePhaseCurveBadEvent T cut (n+1) radius K).indicator
            (D.normalizedGlobalSourceEnvelopeCount T cut (n+1) radius) scene)^2
          ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := hbad.2
      _ ≤ B^2*(D.originalSourceBadTrafficEnvelopeBudget T cut radius *
          Real.exp (-(K-D.normalizedSourcePhaseCurveCountThreshold T cut radius)/2)) :=
        mul_le_mul_of_nonneg_left htail (sq_nonneg B)
      _ = budget := (mul_assoc _ _ _).symm
  have hsqrt : AEStronglyMeasurable (fun s ↦ Real.sqrt ((errorTraffic s)^2))
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hbadI.aestronglyMeasurable
  have herror : AEStronglyMeasurable errorTraffic (Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := by
    apply hsqrt.congr
    exact Filter.Eventually.of_forall (fun s ↦ Real.sqrt_sq
      (indicator_nonneg (fun _ _ ↦ ENNReal.toReal_nonneg) s))
  have hLp : MemLp errorTraffic 2 (Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) :=
    (memLp_two_iff_integrable_sq herror).mpr hbadI
  exact ⟨hLp,hmean,eLpNorm_two_le_sqrt_of_integral_sq_le hLp hmean⟩

/-- The bounded-phase good-count part pays the actual original first
Palm occupation moment, rather than a scale-insensitive Poisson constant. -/
theorem OriginalSeedConditionalMoments.original_minimizer_boundedPhase_goodCount_ltwo
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T]
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ G) (t : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value t ≤ P.value t)
    {cut h ell a : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (hh : 0 < h)
    (hclockRange : ∀ r ∈ Icc (0 : ℝ) 1, cut + ell * r ∈ Ioo D.lo D.hi)
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r‖ *
        Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2) ≤ (1 / 2 : ℝ))
    {ρ : ℝ} (hR : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r‖ ≤ ρ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞}
    {f : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞}
    (hclock : ∀ m c, f (m, c) ≠ 0 →
      ∃ r ∈ Icc (0 : ℝ) 1, c = cut + S.level + ell * r)
    (hηwindow : ∀ x, η x ≠ 0 → ‖T *ᵥ x‖ ≤ a)
    (hmask : ∀ e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker), ∀ c,
      f ((physicalPairAnchor e).2, c) ≠ 0 →
        e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h)
    (ha : 0 ≤ a) {H : ℝ} (hH : 0 ≤ H)
    (hη : Measurable η) (hf : Measurable f)
    {B : ℝ} (hB : 0 ≤ B)
    (hsingle : ∀ x : Fin (finrank ℝ S.covector.ker) → ℝ,
      ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
      (∫⁻ c : ℝ, η (x + originalSeedPathOffset S w c m) * f (m, c) ∂volume) ≤
        ENNReal.ofReal B)
    (hηfinite : (∫⁻ x, η x ∂(volume : Measure
      (Fin (finrank ℝ S.covector.ker) → ℝ))) ≠ (⊤:ℝ≥0∞))
    (hffinite : (∫⁻ m, ∫⁻ c : ℝ, f (m,c) ∂volume
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤:ℝ≥0∞))
    {K : ℝ} (hK : 0≤K) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ)/h^2),Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8*|t| *G/h)
    let PB := 2*H+2*((L:ℝ)*a+b)
    let r := max PB (a+ρ*PB)
    let W := D.normalizedSourcePhaseCell T cut 0 0 r
    let N := fun s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ↦
      ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker))) (W ×ˢ {0})).toReal
    let traffic := fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s).toReal
    let Good := {s | ‖D.normalizedMomentumPhaseField T cut h L s 0‖≤H ∧ N s≤K}
    let palm := ((∫⁻ x, η x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ, f (m,c) ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal
    MemLp (Good.indicator traffic) 2 (Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
    (∫ s, (Good.indicator traffic s)^2 ∂(Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤ B*K*palm ∧
    eLpNorm (Good.indicator traffic) 2 (Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ≤
      ENNReal.ofReal (Real.sqrt (B*K*palm)) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ)/h^2),Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8*|t| *G/h)
  let PB := 2*H+2*((L:ℝ)*a+b)
  let r := max PB (a+ρ*PB)
  let W := D.normalizedSourcePhaseCell T cut 0 0 r
  let N := fun s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ↦
    ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker))) (W ×ˢ {0})).toReal
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  let traffic := fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker) d η f s).toReal
  let Small := {s | ‖D.normalizedMomentumPhaseField T cut h L s 0‖≤H}
  let Good := Small ∩ {s | N s≤K}
  let V := occupiedPairTrafficContributors (finrank ℝ S.covector.ker) d η f
  have hd := measurable_originalSeedPathOffset_joint S hF hw
  have hSmall : MeasurableSet Small := measurableSet_le
    (((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm) measurable_const
  have hW := D.measurableSet_normalizedSourcePhaseCell hF hw T hcut 0 0 r
  have hWfin := D.normalizedSourcePhaseCell_intensity_lt_top hF hw T hcut 0 0 r
  have hN : Measurable N := ((Measure.measurable_coe (hW.prod (measurableSet_singleton 0))).comp
    (measurable_localFiniteMeasure_coe.comp measurable_snd)).ennreal_toReal
  have hGood : MeasurableSet Good := hSmall.inter (measurableSet_le hN measurable_const)
  have hc := D.ae_original_minimizer_boundedPhase_original_counts hF hw hgap hbounds
    T hg hgb t Q hmin hcut hh hclockRange hsmall hR hclock hηwindow hmask ha hH hη hf
  have hNfin := (Q.original_source_exp_moment_of_finite_intensity hW hWfin.ne
    (t:=0) (by norm_num)).1
  have hdom : ∀ᵐ s ∂(Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      s ∈ Small → traffic s≤B*N s := by
    filter_upwards [hc,hNfin] with s hs hn hss
    have hb := originalCompletePath_traffic_le_of_count_ae s d η f (V s)
      (measurableSet_occupiedPairTrafficContributors d hd hη hf s)
      (ae_occupiedPairTrafficContributors_outside_zero d η f s)
      (ae_of_all _ (fun z ↦ hsingle z.1 z.2)) (hs hss).1
    have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hn.ne) hb
    simpa only [traffic,ENNReal.toReal_mul,ENNReal.toReal_ofReal hB] using hr
  have htraffic := measurable_legalMarkedCompletePathTraffic d hd hη hf
  have hfinite : (∫⁻ s, legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker) d η f s
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≠ (⊤:ℝ≥0∞) := by
    rw [Q.lintegral_completePathTraffic d hd hη hf]
    exact ENNReal.mul_ne_top hηfinite hffinite
  have hI : Integrable traffic (Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) :=
    integrable_toReal_of_lintegral_ne_top htraffic.aemeasurable hfinite
  have hpalm : (∫ s, traffic s ∂(Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) =
      ((∫⁻ x, η x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) *
        (∫⁻ m, ∫⁻ c : ℝ, f (m,c) ∂volume
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal := by
    rw [integral_toReal htraffic.aemeasurable (ae_lt_top htraffic hfinite),
      Q.lintegral_completePathTraffic d hd hη hf]
  have hmajor : ∀ᵐ s ∂(Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      (Good.indicator traffic s)^2 ≤ B*K*traffic s := by
    filter_upwards [hdom] with s hs
    by_cases hgs : s ∈ Good
    · rw [indicator_of_mem hgs]
      have ht : traffic s≤B*K := (hs hgs.1).trans (mul_le_mul_of_nonneg_left hgs.2 hB)
      simpa only [pow_two] using mul_le_mul_of_nonneg_right ht ENNReal.toReal_nonneg
    · rw [indicator_of_notMem hgs,zero_pow (by norm_num : (2:ℕ)≠0)]
      exact mul_nonneg (mul_nonneg hB hK) ENNReal.toReal_nonneg
  have hi : Integrable (fun s ↦ (Good.indicator traffic s)^2)
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := by
    apply (hI.const_mul (B*K)).mono'
      (((htraffic.ennreal_toReal).indicator hGood).pow_const 2).aestronglyMeasurable
    filter_upwards [hmajor] with s hs
    rwa [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hmean := integral_mono_ae hi (hI.const_mul (B*K)) hmajor
  rw [integral_const_mul,hpalm] at hmean
  have hLp : MemLp (Good.indicator traffic) 2 (Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) :=
    (memLp_two_iff_integrable_sq ((htraffic.ennreal_toReal).aestronglyMeasurable.indicator hGood)).mpr hi
  exact ⟨hLp,hmean,eLpNorm_two_le_sqrt_of_integral_sq_le hLp hmean⟩

/-- A complete actual physical-clock window has an explicit eLpNorm budget
from its original Poisson cell and its true normalized-momentum Palm mean.
The adjustable bad-event threshold retains its exponential error saving. -/
theorem OriginalSeedConditionalMoments.original_minimizer_completeWindowTraffic_eLpNorm_le
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T]
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ G) (t : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value t ≤ P.value t)
    {cut h ell a : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (hh : 0 < h) (ha : 0 ≤ a)
    (hclockRange : ∀ r ∈ Icc (0 : ℝ) 1, cut + ell * r ∈ Ioo D.lo D.hi)
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r‖ *
        Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2) ≤ (1 / 2 : ℝ))
    {ρ A : ℝ} (hA : 0 ≤ A)
    (hR : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r‖ ≤ ρ)
    (hRLip : ∀ r ∈ Icc (0 : ℝ) 1, ∀ r' ∈ Icc (0 : ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut + S.level) ell r -
        originalNormalizedClockMobility S w T (cut + S.level) ell r'‖ ≤ A * |r - r'|)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞}
    {f : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞}
    (hclock : ∀ m c, f (m, c) ≠ 0 →
      ∃ r ∈ Icc (0 : ℝ) 1, c = cut + S.level + ell * r)
    (hηwindow : ∀ x, η x ≠ 0 → ‖T *ᵥ x‖ ≤ a)
    (hmask : ∀ e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker), ∀ c,
      f ((physicalPairAnchor e).2, c) ≠ 0 →
        e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h)
    (hη : Measurable η) (hf : Measurable f)
    (hηfinite : (∫⁻ x, η x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) ≠ (⊤ : ℝ≥0∞))
    (hffinite : (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞))
    {B : ℝ} (hB : 0 ≤ B)
    (hsingle : ∀ x : Fin (finrank ℝ S.covector.ker) → ℝ,
      ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
      (∫⁻ c : ℝ, η (x + originalSeedPathOffset S w c m) * f (m, c) ∂volume) ≤
        ENNReal.ofReal B)
    (hpfinite : (∫⁻ m, ∫⁻ c : ℝ,
      ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m) * f (m, c) ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞))
    {K : ℝ} (hK :
      let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ)/h^2),Real.sqrt_nonneg _⟩
      let b := Real.sqrt (8*|t| *G/h)
      let r := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
      D.normalizedSourcePhaseCurveCountThreshold T cut r ≤ K) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ)/h^2),Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8*|t| *G/h)
    let H := 1+2*((L:ℝ)*a+b)
    let PB := 2*H+2*((L:ℝ)*a+b)
    let rs := max PB (a+ρ*PB)
    let Λ := (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
      (D.normalizedSourcePhaseCell T cut 0 0 rs)).toReal
    let r := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
    let C := canonicalPhaseCurveScaleCoefficient (L:ℝ) ρ A
    let palm := ((∫⁻ x, η x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ, ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m)* f (m,c)
        ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal
    let firstPalm := ((∫⁻ x, η x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ, f (m,c) ∂volume
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal
    let V := 3*B*(K*(C+1))*palm+B^2*D.originalSourceBadTrafficEnvelopeBudget T cut r *
      Real.exp (-(K-D.normalizedSourcePhaseCurveCountThreshold T cut r)/2)
    let smallBound := Real.sqrt (B*K*firstPalm)+
      Real.sqrt 8*B*Real.exp (Λ*(Real.exp 1-1)/2)*Real.exp (-K/4)
    let traffic := fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f s).toReal
    MemLp traffic 2 (Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
    eLpNorm traffic 2 (Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ≤
        ENNReal.ofReal (smallBound+Real.sqrt V) := by
  dsimp only at hK ⊢
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ)/h^2),Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8*|t| *G/h)
  let H := 1+2*((L:ℝ)*a+b)
  let PB := 2*H+2*((L:ℝ)*a+b)
  let rs := max PB (a+ρ*PB)
  let Λ := (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
    (D.normalizedSourcePhaseCell T cut 0 0 rs)).toReal
  let r := max (2*(a+ρ*b)) (b+2*(L:ℝ)*(a+ρ*b))
  let C := canonicalPhaseCurveScaleCoefficient (L:ℝ) ρ A
  let palm := ((∫⁻ x, η x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) *
    (∫⁻ m, ∫⁻ c : ℝ, ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m)* f (m,c)
      ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal
  let firstPalm := ((∫⁻ x, η x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) *
    (∫⁻ m, ∫⁻ c : ℝ, f (m,c) ∂volume
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal
  let V := 3*B*(K*(C+1))*palm+B^2*D.originalSourceBadTrafficEnvelopeBudget T cut r *
    Real.exp (-(K-D.normalizedSourcePhaseCurveCountThreshold T cut r)/2)
  let smallBound := Real.sqrt (B*K*firstPalm)+
      Real.sqrt 8*B*Real.exp (Λ*(Real.exp 1-1)/2)*Real.exp (-K/4)
  let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
    originalSeedPathOffset S w z.2 z.1
  let traffic := fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker) d η f s).toReal
  let Small := {s | ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ H}
  let k := D.normalizedCanonicalCurveIntegerScale T cut h L ρ A
  let Big := {s | 1≤k s ∧ 1≤‖D.normalizedMomentumPhaseField T cut h L s 0‖ ∧
    2*((L:ℝ)*a+b)≤‖D.normalizedMomentumPhaseField T cut h L s 0‖}
  have hH : 0≤H := by dsimp [H,b]; positivity
  have hK0 : 0≤K := (D.normalizedSourcePhaseCurveCountThreshold_pos T cut r).le.trans hK
  let N := fun s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ↦
    ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
      (D.normalizedSourcePhaseCell T cut 0 0 rs ×ˢ {0})).toReal
  let Good := {s | s ∈ Small ∧ N s≤K}
  let CountBad := {s | K<N s}
  have hgoodRaw := D.original_minimizer_boundedPhase_goodCount_ltwo
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh hclockRange hsmall hR hclock hηwindow
    hmask ha hH hη hf hB hsingle hηfinite hffinite hK0
  have htailRaw := D.original_minimizer_boundedPhase_countTail_traffic_ltwo
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh hclockRange hsmall hR hclock hηwindow
    hmask ha hH hη hf hB hsingle K
  have hgood : MemLp (Good.indicator traffic) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      eLpNorm (Good.indicator traffic) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ≤
        ENNReal.ofReal (Real.sqrt (B*K*firstPalm)) := ⟨hgoodRaw.1,hgoodRaw.2.2⟩
  have htail : MemLp (CountBad.indicator (Small.indicator traffic)) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      eLpNorm (CountBad.indicator (Small.indicator traffic)) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ≤
        ENNReal.ofReal (Real.sqrt 8*B*Real.exp (Λ*(Real.exp 1-1)/2)*Real.exp (-K/4)) :=
    ⟨htailRaw.1,htailRaw.2.2⟩
  have hsmallDom : ∀ᵐ s ∂(Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ‖Small.indicator traffic s‖ ≤ Good.indicator traffic s+
        CountBad.indicator (Small.indicator traffic) s := by
    filter_upwards [] with s
    have ht0 : 0≤traffic s := ENNReal.toReal_nonneg
    by_cases hs : s ∈ Small
    · rw [indicator_of_mem hs,Real.norm_eq_abs,abs_of_nonneg ht0]
      by_cases hn : N s≤K
      · rw [indicator_of_mem (show s ∈ Good from ⟨hs,hn⟩)]
        exact le_add_of_nonneg_right (indicator_nonneg
          (fun _ _ ↦ indicator_nonneg (fun _ _ ↦ ENNReal.toReal_nonneg) _) s)
      · rw [indicator_of_mem (show s ∈ CountBad from lt_of_not_ge hn),indicator_of_mem hs]
        exact le_add_of_nonneg_left (indicator_nonneg (fun _ _ ↦ ENNReal.toReal_nonneg) s)
    · rw [indicator_of_notMem hs,norm_zero]
      exact add_nonneg (indicator_nonneg (fun _ _ ↦ ENNReal.toReal_nonneg) s)
        (indicator_nonneg (fun _ _ ↦ indicator_nonneg (fun _ _ ↦ ENNReal.toReal_nonneg) _) s)
  have heBound : ∀ e ∈ legalMarkedCompletePathContributors (finrank ℝ S.covector.ker) d η f,
      (legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker) d η f e).toReal ≤ B := by
    intro e _
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hsingle e.1.1 (physicalPairAnchor e).2)
    simpa only [legalMarkedCompletePathEdgeTraffic,physicalPairAnchor,d,
      ENNReal.toReal_ofReal hB] using ht
  have hlarge := (D.original_minimizer_largeCanonicalTraffic_source_sq_integral_le
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hclock hηwindow hmask hη hf hηfinite hffinite hB heBound hpfinite hK).1 1 le_rfl
  have hbad := D.original_minimizer_canonical_source_bad_ltwo_le_exp
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh ha hclockRange hsmall hA hR hRLip
    hclock hηwindow hmask hη hf hηfinite hffinite hB heBound hK
  have htraffic : Measurable traffic :=
    (measurable_legalMarkedCompletePathTraffic d
      (measurable_originalSeedPathOffset_joint S hF hw) hη hf).ennreal_toReal
  have hamp : Measurable (fun s ↦ ‖D.normalizedMomentumPhaseField T cut h L s 0‖) :=
    ((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm
  have hk := D.measurable_normalizedCanonicalCurveIntegerScale hF hw T hcut h L ρ A
  have hBig : MeasurableSet Big := (measurableSet_le measurable_const hk).inter
    ((measurableSet_le measurable_const hamp).inter (measurableSet_le measurable_const hamp))
  have hSmall : MeasurableSet Small := measurableSet_le hamp measurable_const
  have hsmallMeas : AEStronglyMeasurable (Small.indicator traffic) (Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) :=
    htraffic.aestronglyMeasurable.indicator hSmall
  have hbounded : MemLp (Small.indicator traffic) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      eLpNorm (Small.indicator traffic) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ≤
        ENNReal.ofReal smallBound := by
    refine ⟨(hgood.1.add htail.1).mono' hsmallMeas hsmallDom,?_⟩
    calc
      _ ≤ eLpNorm (fun s ↦ Good.indicator traffic s+
          CountBad.indicator (Small.indicator traffic) s) 2
          (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) :=
        eLpNorm_mono_ae_real hsmallDom
      _ ≤ eLpNorm (Good.indicator traffic) 2 (Q.law : Measure
          (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) +
          eLpNorm (CountBad.indicator (Small.indicator traffic)) 2 (Q.law : Measure
          (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) :=
        eLpNorm_add_le hgood.1.aestronglyMeasurable htail.1.aestronglyMeasurable (by norm_num)
      _ ≤ ENNReal.ofReal (Real.sqrt (B*K*firstPalm))+
          ENNReal.ofReal (Real.sqrt 8*B*Real.exp (Λ*(Real.exp 1-1)/2)*Real.exp (-K/4)) :=
        add_le_add hgood.2 htail.2
      _ = _ := (ENNReal.ofReal_add (Real.sqrt_nonneg _) (by positivity)).symm
  have hBigLp : MemLp (Big.indicator traffic) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) :=
    (memLp_two_iff_integrable_sq (htraffic.aestronglyMeasurable.indicator hBig)).mpr hlarge.1
  have hBigMean : (∫ s, (Big.indicator traffic s)^2 ∂(Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤ V :=
    hlarge.2.trans (add_le_add le_rfl hbad.2.1)
  have hBigNorm := eLpNorm_two_le_sqrt_of_integral_sq_le hBigLp hBigMean
  have hdom : ∀ᵐ s ∂(Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ‖traffic s‖ ≤ Small.indicator traffic s+Big.indicator traffic s := by
    filter_upwards [] with s
    have ht0 : 0≤traffic s := ENNReal.toReal_nonneg
    rw [Real.norm_eq_abs,abs_of_nonneg ht0]
    by_cases hs : s ∈ Small
    · rw [indicator_of_mem hs]
      exact le_add_of_nonneg_right (indicator_nonneg (fun _ _ ↦ ENNReal.toReal_nonneg) s)
    · have hampH : H<‖D.normalizedMomentumPhaseField T cut h L s 0‖ := lt_of_not_ge hs
      have hH1 : 1≤H := by
        have hn : 0≤2*((L:ℝ)*a+b) := by dsimp [b]; positivity
        dsimp [H]
        linarith
      have hamp1 : 1≤‖D.normalizedMomentumPhaseField T cut h L s 0‖ := hH1.trans hampH.le
      have hscale := D.normalizedCanonicalCurveIntegerScale_spec T cut h L ρ A
        (N:=1) le_rfl s (by simpa only [Nat.cast_one] using hamp1)
      have hsBig : s ∈ Big := ⟨hscale.1,hamp1,by dsimp [H] at hampH; linarith⟩
      rw [indicator_of_notMem hs,indicator_of_mem hsBig,zero_add]
  refine ⟨(hbounded.1.add hBigLp).mono' htraffic.aestronglyMeasurable hdom,?_⟩
  calc
    _ ≤ eLpNorm (fun s ↦ Small.indicator traffic s+Big.indicator traffic s) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) :=
      eLpNorm_mono_ae_real hdom
    _ ≤ eLpNorm (Small.indicator traffic) 2 (Q.law : Measure
        (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) +
        eLpNorm (Big.indicator traffic) 2 (Q.law : Measure
        (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) :=
      eLpNorm_add_le hbounded.1.aestronglyMeasurable hBigLp.aestronglyMeasurable (by norm_num)
    _ ≤ ENNReal.ofReal smallBound+ENNReal.ofReal (Real.sqrt V) := add_le_add hbounded.2 hBigNorm
    _ = _ := (ENNReal.ofReal_add (by dsimp [smallBound]; positivity) (Real.sqrt_nonneg V)).symm

end OTSelector.Reconstruction
