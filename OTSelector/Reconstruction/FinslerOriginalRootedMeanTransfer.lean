import OTSelector.Reconstruction.FinslerOriginalCountingNormalizationLink

/-!
# Rooted tile mean transfer: counted form <-> probability fixed-pair form

This module bridges the probability-form rooted tile mean used by the fixed-pair
consumer (T.tileFixedPair against the uniform empirical sample law
sceneCloudSample) and the counted/empirical form used by the lower counting
lane (the 1/(n+1)-normalized integral of the masked cost matrix against the
counting measure sceneCloudCounting).

The bridge is EXACT level-by-level, via the repo's counting normalization lemma
integral_counting_eq_empirical:

1. **countedTileFixedPair_eq_tileFixedPair**: the counted masked fixed-pair mean
   equals the probability fixed-pair mean, for every n and every tile index c.
   No scale factor appears in this identity: the fixed-pair mean is the masked
   entry expectation, not the (1-2 eps)*scale-scaled readout, so the uniform
   boundedness eps_mul_tileScale_abs_le is NOT needed for the transfer itself.
2. **tileFixedPair_tendsto_of_countedTileMean**: convergence of the counted
   masked fixed-pair means implies the probability-form convergence hfixed
   used by the consumer (same limit).
3. **countedTileMean_tendsto_of_tileFixedPair**: the converse transfer.
4. **tilePalmSampleLaw_sceneCloud_of_countedTileMean**: the consumer's
   TilePalmSampleLaw for the concrete lane with the single probabilistic input
   stated in COUNTED form: the only remaining named input is convergence of the
   normalized counting-measure masked fixed-pair mean towards the tile pop
   value, instead of the probability-law fixed-pair convergence.

No sorry, admit or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
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

namespace PopulationLocalPressureCore.TaylorTiles

/-- **The counted masked fixed-pair mean equals the probability fixed-pair
mean**: the normalized counting-measure integral of the masked cost matrix entry
(0,0) is the empirical-law expectation of the same entry. -/
theorem countedTileFixedPair_eq_tileFixedPair
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) :
    ((n + 1 : ℕ) : ℝ)⁻¹ *
        ∫ s, T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
          (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s
          ⟨0, Nat.succ_pos n⟩ ⟨0, Nat.succ_pos n⟩ ∂(sceneCloudCounting n) =
      T.tileFixedPair f t sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud)
        tileScale (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c := by
  unfold tileFixedPair
  exact integral_counting_eq_empirical n _

/-- **Transfer COUNTED -> PROBABILITY (consumer shape).**  Convergence of the
normalized counting-measure masked fixed-pair mean implies the probability-form
fixed-pair convergence used by the lower lane. -/
theorem tileFixedPair_tendsto_of_countedTileMean
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {L : ℝ}
    (hcounted : Tendsto (fun n ↦ ((n + 1 : ℕ) : ℝ)⁻¹ *
        ∫ s, T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
          (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s
          ⟨0, Nat.succ_pos n⟩ ⟨0, Nat.succ_pos n⟩ ∂(sceneCloudCounting n))
      atTop (𝓝 L)) :
    Tendsto (fun n ↦ T.tileFixedPair f t sceneCloudSample
        (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
      atTop (𝓝 L) := by
  have hfun : (fun n ↦ T.tileFixedPair f t sceneCloudSample
        (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) =
      (fun n ↦ ((n + 1 : ℕ) : ℝ)⁻¹ *
        ∫ s, T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
          (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s
          ⟨0, Nat.succ_pos n⟩ ⟨0, Nat.succ_pos n⟩ ∂(sceneCloudCounting n)) := by
    funext n
    exact (countedTileFixedPair_eq_tileFixedPair T f t pcloud qcloud base n c).symm
  rw [hfun]
  exact hcounted

/-- **Transfer PROBABILITY -> COUNTED.**  Convergence of the probability-form
fixed-pair mean implies convergence of the normalized counting-measure masked
fixed-pair mean (same limit). -/
theorem countedTileMean_tendsto_of_tileFixedPair
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {L : ℝ}
    (hfixed : Tendsto (fun n ↦ T.tileFixedPair f t sceneCloudSample
        (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
      atTop (𝓝 L)) :
    Tendsto (fun n ↦ ((n + 1 : ℕ) : ℝ)⁻¹ *
        ∫ s, T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
          (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s
          ⟨0, Nat.succ_pos n⟩ ⟨0, Nat.succ_pos n⟩ ∂(sceneCloudCounting n))
      atTop (𝓝 L) := by
  have hfun : (fun n ↦ ((n + 1 : ℕ) : ℝ)⁻¹ *
        ∫ s, T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
          (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s
          ⟨0, Nat.succ_pos n⟩ ⟨0, Nat.succ_pos n⟩ ∂(sceneCloudCounting n)) =
      (fun n ↦ T.tileFixedPair f t sceneCloudSample
        (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) := by
    funext n
    exact countedTileFixedPair_eq_tileFixedPair T f t pcloud qcloud base n c
  rw [hfun]
  exact hfixed

/-- **The consumer TilePalmSampleLaw with the single probabilistic input in
COUNTED form.**  All other exposed inputs are as in
tilePalmSampleLaw_sceneCloud_of_fixedPairConvergence; the named convergence is
now the normalized counting-measure masked fixed-pair mean, transferred to the
probability form by tileFixedPair_tendsto_of_countedTileMean. -/
noncomputable def tilePalmSampleLaw_sceneCloud_of_countedTileMean
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintLin : ∀ n, Integrable (T.tileLinearIntegrand (ε := ε) f t
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sceneCloudSample n))
    (hintClip : ∀ n, Integrable (T.tileClippingIntegrand (ε := ε) f t
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sceneCloudSample n))
    (hintC : ∀ n, Integrable (T.tileLinearCostIntegrand (ε := ε) f t
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale n c) (sceneCloudSample n))
    (hintP : ∀ n, Integrable (T.tileLinearProbeIntegrand f t
      (sceneCloudX pcloud) (sceneCloudY qcloud)
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sceneCloudSample n))
    (hclip : Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sceneCloudSample
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) atTop (𝓝 0))
    (G : ℕ → (ℚ → M) → ℝ)
    (hcounted : Tendsto (fun n ↦ ((n + 1 : ℕ) : ℝ)⁻¹ *
        ∫ s, T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
          (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s
          ⟨0, Nat.succ_pos n⟩ ⟨0, Nat.succ_pos n⟩ ∂(sceneCloudCounting n))
      atTop (𝓝 (T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c))) :
    T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale c
      (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c) :=
  T.tilePalmSampleLaw_sceneCloud_of_fixedPairConvergence f t pcloud qcloud base hBp hbase
    hintLin hintClip hintC hintP hclip G
    (tileFixedPair_tendsto_of_countedTileMean T f t pcloud qcloud base hcounted)

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
