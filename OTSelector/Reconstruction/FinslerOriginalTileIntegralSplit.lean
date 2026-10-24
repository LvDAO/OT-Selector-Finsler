import OTSelector.Reconstruction.FinslerOriginalTileFixedPairDecomposition

/-!
# Integral-level split of the tile fixed-pair masked expectation

This module finishes the mechanical part of task 186: the **integral-level split** of
`tileFixedPair` into its linear part and its clipping correction.

To keep definitional unfolding small, the integrands are given **named definitions**
first (`tileClippedIntegrand`, `tileLinearIntegrand`, `tileClippingIntegrand`); the
integrability hypotheses therefore mention these small names, and the only unfolding
needed is one layer deep.  The split is then the two-step composition

* `tileFixedPair_eq_integral_clipped`: `tileFixedPair` is the integral of the clipped
  masked integrand (pointwise unfolding through `tileCostMatrix` / `maskedFrozenCost` /
  `frozenCoreMatrix`, proved in the previous module as
  `tileCostMatrix_apply_eq_indicator_max`);
* `integral_clipped_eq_linear_add_clipping`: the generic masked clipping decomposition
  `integral_indicator_max_eq'` applied to the named integrands.

**Result** (`tileFixedPair_eq_linear_add_clipping`):

```T.tileFixedPair f t sample X Y scale hprobe n c
  = T.tileFixedPairLinearPart f t sample X Y scale hprobe n c
    + T.tileFixedPairClippingCorrection f t sample X Y scale hprobe n c```

Together with `planFreeTileMeanIdentification_of_linear_and_clipping` (task 182) this
reduces the fixed-pair linear Palm identification to: (i) the linear (cost + probe)
Palm identification of `tileFixedPairLinearPart` against `tilePopValue`, and (ii) the
clipping vanishing, whose budget form is recorded as `TileClippingVanishing`.

No `sorry`, `admit` or added axiom occurs.
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

/-- The **clipped masked integrand** at the distinguished pair: the frozen core entry
after the mask indicator and the clip.  (Named to avoid unfolding the heavy
`frozenCoreMatrix` expression repeatedly.) -/
noncomputable def tileClippedIntegrand
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) (s : Ω n) : ℝ :=
  (T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c).indicator
    (fun p : Fin (n + 1) × Fin (n + 1) ↦
      max (T.tileLinearTerm (ε := ε) f t X Y scale hprobe n c s p.1 p.2) 0)
    (⟨0, Nat.succ_pos n⟩, ⟨0, Nat.succ_pos n⟩)

/-- The **linear masked integrand**: the mask indicator times the argument of the
clip. -/
noncomputable def tileLinearIntegrand
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) (s : Ω n) : ℝ :=
  (T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c).indicator
    (fun p : Fin (n + 1) × Fin (n + 1) ↦
      T.tileLinearTerm (ε := ε) f t X Y scale hprobe n c s p.1 p.2)
    (⟨0, Nat.succ_pos n⟩, ⟨0, Nat.succ_pos n⟩)

/-- The **clipping integrand**: the mask indicator times the clipping correction
`max (-·) 0`. -/
noncomputable def tileClippingIntegrand
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) (s : Ω n) : ℝ :=
  (T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c).indicator
    (fun p : Fin (n + 1) × Fin (n + 1) ↦
      max (-(T.tileLinearTerm (ε := ε) f t X Y scale hprobe n c s p.1 p.2)) 0)
    (⟨0, Nat.succ_pos n⟩, ⟨0, Nat.succ_pos n⟩)

/-- The **linear part** of the fixed-pair masked expectation. -/
noncomputable def tileFixedPairLinearPart
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) : ℝ :=
  ∫ s, T.tileLinearIntegrand (ε := ε) f t X Y scale hprobe n c s ∂sample n

/-- The **clipping correction** of the fixed-pair masked expectation. -/
noncomputable def tileFixedPairClippingCorrection
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) : ℝ :=
  ∫ s, T.tileClippingIntegrand (ε := ε) f t X Y scale hprobe n c s ∂sample n

/-- **Step 1**: the fixed-pair masked expectation is the integral of the clipped
masked integrand. -/
theorem tileFixedPair_eq_integral_clipped
    (sample : ∀ n, Measure (Ω n))
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) :
    T.tileFixedPair f t sample X Y scale hprobe n c =
      ∫ s, T.tileClippedIntegrand (ε := ε) f t X Y scale hprobe n c s ∂sample n := by
  have hpoint : ∀ s : Ω n,
      T.tileCostMatrix f t X Y scale hprobe n c s
          ⟨0, Nat.succ_pos n⟩ ⟨0, Nat.succ_pos n⟩ =
        T.tileClippedIntegrand (ε := ε) f t X Y scale hprobe n c s :=
    fun s ↦ T.tileCostMatrix_apply_eq_indicator_max f t X Y scale hprobe n c s _ _
  show (∫ s, T.tileCostMatrix f t X Y scale hprobe n c s
      ⟨0, Nat.succ_pos n⟩ ⟨0, Nat.succ_pos n⟩ ∂sample n) = _
  exact integral_congr_ae (Eventually.of_forall hpoint)

/-- **Step 2a (pointwise)**: the clipped masked integrand is the sum of the linear
masked integrand and the clipping integrand. -/
theorem tileClippedIntegrand_eq_add
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) (s : Ω n) :
    T.tileClippedIntegrand (ε := ε) f t X Y scale hprobe n c s =
      T.tileLinearIntegrand (ε := ε) f t X Y scale hprobe n c s +
        T.tileClippingIntegrand (ε := ε) f t X Y scale hprobe n c s := by
  simp only [tileClippedIntegrand, tileLinearIntegrand, tileClippingIntegrand]
  by_cases h : (⟨0, Nat.succ_pos n⟩, ⟨0, Nat.succ_pos n⟩) ∈
      T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Set.indicator_of_mem h]
    exact max_zero_eq_add_max_neg _
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h,
      Set.indicator_of_notMem h, add_zero]

/-- **Step 2b**: integrating the pointwise splitting and using linearity of the
integral, the integral of the clipped masked integrand is the linear part plus the
clipping correction. -/
theorem integral_clipped_eq_linear_add_clipping
    (sample : ∀ n, Measure (Ω n))
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index)
    (h1 : Integrable (T.tileLinearIntegrand (ε := ε) f t X Y scale hprobe n c)
      (sample n))
    (h2 : Integrable (T.tileClippingIntegrand (ε := ε) f t X Y scale hprobe n c)
      (sample n)) :
    ∫ s, T.tileClippedIntegrand (ε := ε) f t X Y scale hprobe n c s ∂sample n =
      T.tileFixedPairLinearPart f t sample X Y scale hprobe n c +
        T.tileFixedPairClippingCorrection f t sample X Y scale hprobe n c := by
  have hcongr : ∫ s, T.tileClippedIntegrand (ε := ε) f t X Y scale hprobe n c s
      ∂sample n =
      ∫ s, T.tileLinearIntegrand (ε := ε) f t X Y scale hprobe n c s +
        T.tileClippingIntegrand (ε := ε) f t X Y scale hprobe n c s ∂sample n :=
    integral_congr_ae (Eventually.of_forall
      (T.tileClippedIntegrand_eq_add f t X Y scale hprobe n c))
  rw [hcongr, integral_add h1 h2]
  rfl

/-- **The integral-level split of the fixed-pair masked expectation.** -/
theorem tileFixedPair_eq_linear_add_clipping
    (sample : ∀ n, Measure (Ω n))
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index)
    (h1 : Integrable (T.tileLinearIntegrand (ε := ε) f t X Y scale hprobe n c)
      (sample n))
    (h2 : Integrable (T.tileClippingIntegrand (ε := ε) f t X Y scale hprobe n c)
      (sample n)) :
    T.tileFixedPair f t sample X Y scale hprobe n c =
      T.tileFixedPairLinearPart f t sample X Y scale hprobe n c +
        T.tileFixedPairClippingCorrection f t sample X Y scale hprobe n c :=
  (T.tileFixedPair_eq_integral_clipped sample f t X Y scale hprobe n c).trans
    (T.integral_clipped_eq_linear_add_clipping sample f t X Y scale hprobe n c h1 h2)

/-- **Clipping-budget vanishing (named hypothesis).**  The clipping correction is
bounded by an explicit budget sequence; vanishing of the budget gives vanishing of the
correction via the frozen absolute entry budget.  This records the form in which the
unavailable Taylor slack rate enters. -/
def TileClippingVanishing (clipping budget : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ clipping n ∧ clipping n ≤ budget n) ∧ Tendsto budget atTop (𝓝 0)

/-- **Clipping correction tends to zero from a vanishing budget.** -/
theorem tileFixedPairClipping_tendsto_zero_of_budget
    (clipping budget : ℕ → ℝ) (h : TileClippingVanishing clipping budget) :
    Tendsto clipping atTop (𝓝 0) :=
  maskedClipping_tendsto_zero_of_budget (ι := ℕ) clipping budget h.1 h.2

/-- **The fixed-pair Palm identification from the linear Palm identification and
clipping vanishing.**  Instantiation of the task-182 reduction with the exact integral
split proved above. -/
theorem planFreeTileMeanIdentification_of_tileSplit
    (fixedPair linear clipping : ℕ → ℝ) (popVal : ℕ → ℝ)
    (hsplit : ∀ n, fixedPair n = linear n + clipping n)
    (hpalm : PlanFreeTileMeanIdentification linear popVal)
    (hclip : Tendsto clipping atTop (𝓝 0)) :
    PlanFreeTileMeanIdentification fixedPair popVal :=
  planFreeTileMeanIdentification_of_linear_and_clipping fixedPair linear clipping popVal
    hsplit hpalm hclip

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
