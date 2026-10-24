import OTSelector.Reconstruction.FinslerOriginalCountingNormalizationLink
/-!
# Closing the fixed-pair identification from the rooted tile mean convergence

This module closes the last identification step of the counting-normalization route
to the concrete tile Palm sample law:

* (distinguished-pair readout) the fractional assignment cost of the concrete masked
  frozen cost matrix against the single-pair matrix is exactly the masked frozen
  entry at the distinguished pair, i.e. the frozen tile cost readout, and its
  expectation is the fixed-pair expectation decomposing into the linear (cost +
  probe) part and the clipping correction;
* (population value) the population value used by the Palm sample law is the
  population tile value;
* (probabilistic input closed) the fixed-pair expectation converges to the
  population tile value from the rooted tile mean convergence alone: with the
  uniform scaled plan, the probability-normalized empirical frozen tile mean is
  exactly the plan-free tile average divided by the sample size, whose fixed-pair
  identification follows from the masked-entry identity and the plan-free
  normalization identity.

The last step converts the named probabilistic input RootedTileMeanConvergence into
the fixed-pair convergence consumed by
tilePalmSampleLaw_sceneCloud_of_fixedPairConvergence, and hence derives the
concrete lane TilePalmSampleLaw with RootedTileMeanConvergence as the only remaining
probabilistic input (plus the clipping-budget vanishing and the
integrability/boundedness side conditions of the lane).

No sorry, admit or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

open OTSelector.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated (ℚ → M)]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
  {D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss}
  {ε : ℝ} (T : D.TaylorTiles ε)
  {K : Set M} {q : ℝ}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- The matrix with unit mass at the distinguished pair (0,0). -/
def distinguishedPairMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j ↦ if i = (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) ∧
      j = (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) then 1 else 0

/-- The uniform scaled plan used for the rooted tile mean readout. -/
def uniformTilePlan (Ω : ℕ → Type*) :
    ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun n _ ↦ fun _ _ ↦ 1 / ((n + 1 : ℕ) : ℝ)

/-- **The assignment cost of a single-pair plan is the corresponding entry.** -/
theorem fractionalAssignmentCost_eq_entry_of_singlePair {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ) (a : Fin m) :
    fractionalAssignmentCost M (fun i j ↦ if i = a ∧ j = a then 1 else 0) = M a a := by
  rw [fractionalAssignmentCost]
  have hinner : ∀ i : Fin m,
      (∑ j, (if i = a ∧ j = a then 1 else 0) * M i j) =
        if i = a then M i a else 0 := by
    intro i
    rw [Finset.sum_eq_single a]
    · by_cases hi : i = a
      · subst hi
        simp
      · rw [if_neg (fun h => hi h.1), if_neg hi]
        simp
    · intro j _ hj
      rw [if_neg (fun h => hj h.2), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  rw [show (∑ i, ∑ j, (if i = a ∧ j = a then 1 else 0) * M i j) =
      ∑ i, (if i = a then M i a else 0) from
    Finset.sum_congr rfl (fun i _ => hinner i)]
  rw [Finset.sum_eq_single a]
  · simp
  · intro i _ hi
    rw [if_neg hi]
  · intro h
    exact absurd (Finset.mem_univ a) h

namespace PopulationLocalPressureCore.TaylorTiles

open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

/-- **Readout at the distinguished pair.**  The fractional assignment cost of the
concrete masked frozen cost matrix against the single-pair matrix is the masked
frozen entry at the distinguished pair, i.e. the frozen tile cost readout. -/
theorem fractionalAssignmentCost_distinguishedPair
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) (s : Ω n) :
    fractionalAssignmentCost
      (maskedFrozenCost (T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c)
        (frozenCoreMatrix (T.core c) ε (fun _ _ ↦ T.reference c)
          (fun i ↦ X n i s) (fun i ↦ Y n i s) (scale n) t (hprobe f t n s c)))
      (distinguishedPairMatrix n) =
      T.tileCostMatrix f t X Y scale hprobe n c s
        ⟨0, Nat.succ_pos n⟩ ⟨0, Nat.succ_pos n⟩ := by
  have h := fractionalAssignmentCost_eq_entry_of_singlePair
    (maskedFrozenCost (T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c)
      (frozenCoreMatrix (T.core c) ε (fun _ _ ↦ T.reference c)
        (fun i ↦ X n i s) (fun i ↦ Y n i s) (scale n) t (hprobe f t n s c)))
    (⟨0, Nat.succ_pos n⟩ : Fin (n + 1))
  show fractionalAssignmentCost _ (fun i j ↦
    if i = (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) ∧
      j = (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) then 1 else 0) = _
  rw [h]
  rfl

/-- **The fixed-pair identification at the distinguished pair.**  The expectation of
the distinguished-pair fractional assignment cost is the fixed-pair masked frozen
expectation, and it splits into the linear (cost + probe) part plus the clipping
correction. -/
theorem integral_fractionalAssignmentCost_distinguishedPair
    (sample : ∀ n, Measure (Ω n))
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index)
    (h1 : Integrable (T.tileLinearIntegrand (ε := ε) f t X Y scale hprobe n c)
      (sample n))
    (h2 : Integrable (T.tileClippingIntegrand (ε := ε) f t X Y scale hprobe n c)
      (sample n)) :
    (∫ s, fractionalAssignmentCost
        (maskedFrozenCost (T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c)
          (frozenCoreMatrix (T.core c) ε (fun _ _ ↦ T.reference c)
            (fun i ↦ X n i s) (fun i ↦ Y n i s) (scale n) t (hprobe f t n s c)))
        (distinguishedPairMatrix n) ∂sample n) =
      T.tileFixedPairLinearPart f t sample X Y scale hprobe n c +
        T.tileFixedPairClippingCorrection f t sample X Y scale hprobe n c := by
  have hcongr : (fun s ↦ fractionalAssignmentCost
        (maskedFrozenCost (T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c)
          (frozenCoreMatrix (T.core c) ε (fun _ _ ↦ T.reference c)
            (fun i ↦ X n i s) (fun i ↦ Y n i s) (scale n) t (hprobe f t n s c)))
        (distinguishedPairMatrix n)) =
      (fun s ↦ T.tileCostMatrix f t X Y scale hprobe n c s
        ⟨0, Nat.succ_pos n⟩ ⟨0, Nat.succ_pos n⟩) :=
    funext fun s ↦
      T.fractionalAssignmentCost_distinguishedPair f t X Y scale hprobe n c s
  rw [hcongr]
  exact T.tileFixedPair_eq_linear_add_clipping sample f t X Y scale hprobe n c h1 h2

/-- **The population value is the population tile value.** -/
theorem popVal_eq_tilePopValue
    (G : ℕ → (ℚ → M) → ℝ)
    (popVal : ((K × K) →ᵇ ℝ) → ℝ → T.Index → ℝ)
    (hpop : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      popVal f t c =
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index) :
    popVal f t c =
      T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c :=
  hpop f t c

/-- **The fixed-pair expectation converges to the population tile value from the
rooted tile mean convergence alone.**

Take the uniform scaled plan.  Then the frozen tile cost is the plan-free average
divided by n+1, so the probability-normalized empirical tile mean is 1/(n+1) times
the plan-free average, and the masked-entry exchangeability gives the plan-free
normalization identity 1/(n+1)^2 * uniformTilePart = tileFixedPair.  Hence the
rooted tile mean convergence bounds the distance of tileFixedPair from the
population tile value by the summable per-tile error budget. -/
theorem tileFixedPair_tendsto_of_rootedTileMeanConvergence
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (hintEntry : ∀ (n : ℕ) (c : T.Index) (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t X Y scale hprobe n c s i j)
        (sample n))
    (hExch : ∀ (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sample n) (T.tileCostMatrix f t X Y scale hprobe n c))
    (hconv : T.RootedTileMeanConvergence
      (fun (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index) ↦
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      sample X Y scale hprobe (uniformTilePlan Ω))
    (c : T.Index) :
    Tendsto (fun n ↦ T.tileFixedPair f t sample X Y scale hprobe n c) atTop
      (𝓝 (T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c)) := by
  obtain ⟨err, herrSum, herrBound⟩ := hconv f t
  have hmean : ∀ (n : ℕ) (c' : T.Index), (1 / ((n + 1 : ℕ) : ℝ)) *
      (∫ s, T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
        (hprobe f t n) (uniformTilePlan Ω n) (scale n) t c' s ∂sample n) =
      T.tileFixedPair f t sample X Y scale hprobe n c' := by
    intro n c'
    have hpc : (fun s ↦ T.tileFrozenCost (fun s i ↦ X n i s)
        (fun s i ↦ Y n i s) (hprobe f t n) (uniformTilePlan Ω n)
        (scale n) t c' s) =
        (fun s ↦ (1 / ((n + 1 : ℕ) : ℝ)) *
          ∑ i, ∑ j, T.tileCostMatrix f t X Y scale hprobe n c' s i j) := by
      funext s
      simp only [tileFrozenCost, fractionalAssignmentCost, tileCostMatrix,
        uniformTilePlan, Finset.mul_sum]
    have hu : (∫ s, T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
        (hprobe f t n) (uniformTilePlan Ω n) (scale n) t c' s ∂sample n) =
        (1 / ((n + 1 : ℕ) : ℝ)) *
          T.uniformTilePart f t sample X Y scale hprobe n c' := by
      rw [hpc, integral_const_mul]
      rfl
    rw [hu]
    exact uniformTilePart_eq_fixedPair (T := T) sample f t X Y scale hprobe n c'
      (hintEntry n c') (hExch n c')
  have hbound : ∀ (n : ℕ) (c' : T.Index),
      |T.tileFixedPair f t sample X Y scale hprobe n c' -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c'| ≤
        err n c' := by
    intro n c'
    have hb := herrBound n c'
    have hb' : |(∫ s, T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
        (hprobe f t n) (uniformTilePlan Ω n) (scale n) t c' s
        ∂sample n) / ((n + 1 : ℕ) : ℝ) -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
          G c'| ≤ err n c' := by
      simpa only [] using hb
    have hdiv : (∫ s, T.tileFrozenCost (fun s i ↦ X n i s)
        (fun s i ↦ Y n i s) (hprobe f t n) (uniformTilePlan Ω n)
        (scale n) t c' s ∂sample n) / ((n + 1 : ℕ) : ℝ) =
        (1 / ((n + 1 : ℕ) : ℝ)) *
          (∫ s, T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
            (hprobe f t n) (uniformTilePlan Ω n) (scale n) t c' s
            ∂sample n) := by
      rw [div_eq_mul_inv, one_div, mul_comm]
    rw [hdiv, hmean n c'] at hb'
    exact hb'
  refine (Metric.tendsto_atTop).2 (fun δ hδ ↦ ?_)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (herrSum (δ / 2) (by positivity))
  refine ⟨N, fun n hn ↦ ?_⟩
  have hnonneg : ∀ c' : T.Index, 0 ≤ err n c' :=
    fun c' ↦ (abs_nonneg _).trans (hbound n c')
  calc dist (T.tileFixedPair f t sample X Y scale hprobe n c)
        (T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      = |T.tileFixedPair f t sample X Y scale hprobe n c -
          T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
            G c| := by rw [Real.dist_eq]
    _ ≤ err n c := hbound n c
    _ ≤ ∑ c' : T.Index, err n c' :=
        Finset.single_le_sum (fun c' _ ↦ hnonneg c') (Finset.mem_univ c)
    _ ≤ δ / 2 := hN n hn
    _ < δ := by linarith

/-- **The concrete tile Palm sample law from the rooted tile mean convergence.**

This closes the fixed-pair identification of
tilePalmSampleLaw_sceneCloud_of_fixedPairConvergence with the convergence
RootedTileMeanConvergence as the only remaining probabilistic input: the population
value is the population tile value, and the fixed-pair expectation converges to it
by tileFixedPair_tendsto_of_rootedTileMeanConvergence. -/
noncomputable def tilePalmSampleLaw_sceneCloud_of_rootedConvergence
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintLin : ∀ n, Integrable (T.tileLinearIntegrand (ε := ε) f t
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
      (sceneCloudSample n))
    (hintClip : ∀ n, Integrable (T.tileClippingIntegrand (ε := ε) f t
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
      (sceneCloudSample n))
    (hintC : ∀ n, Integrable (T.tileLinearCostIntegrand (ε := ε) f t
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale n c) (sceneCloudSample n))
    (hintP : ∀ n, Integrable (T.tileLinearProbeIntegrand f t
      (sceneCloudX pcloud) (sceneCloudY qcloud)
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
      (sceneCloudSample n))
    (hclip : Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sceneCloudSample
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) atTop (𝓝 0))
    (G : ℕ → (ℚ → M) → ℝ)
    (hintEntry : ∀ (n : ℕ) (c' : T.Index) (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c' s i j)
        (sceneCloudSample n))
    (hExch : ∀ (n : ℕ) (c' : T.Index),
      MaskedEntryExchangeability (sceneCloudSample n)
        (T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
          (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c'))
    (hconv : T.RootedTileMeanConvergence
      (fun (f : (K × K) →ᵇ ℝ) (t : ℝ) (c' : T.Index) ↦
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c')
      sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c')
      (uniformTilePlan (fun n ↦ Fin (n + 1)))) :
    T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale c
      (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c) :=
  T.tilePalmSampleLaw_sceneCloud_of_fixedPairConvergence f t pcloud qcloud base hBp
    hbase hintLin hintClip hintC hintP hclip G
    (tileFixedPair_tendsto_of_rootedTileMeanConvergence (T := T) sceneCloudSample G
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') f t
      hintEntry hExch hconv c)

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
