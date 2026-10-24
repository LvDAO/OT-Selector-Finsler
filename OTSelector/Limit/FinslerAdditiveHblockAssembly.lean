import OTSelector.Reconstruction.FinslerTileProbeCorrection
import OTSelector.Probability.FinslerTileBlockLawComparisonCounts
import OTSelector.Limit.FinslerExpectationUpperBoundAdditive

/-!
# Additive `hblock` and `hupper` for the Finsler supported pressure

This module composes the now-available pieces of the upper-bound lane into the
additive per-cell comparison `hblock` and hence the expectation upper bound and
`hupper` for the Finsler supported pressure.

The composition has three inputs at each sample size `n` and tile `c`:

* **pointwise frozen comparison.**  The deterministic comparison
  `finslerTileBlock_le_frozenModelTileBlock` gives
  `phys ≤ (1 + 2 ε) * frozen + min (#S_c) (#T_c) * (|t| B + 2 ε |t| Gb)`
  on the tile edges.  Dividing by `n + 1` and using
  `min (#S_c) (#T_c) ≤ n + 1` turns it into the normalized additive comparison
  `phys_norm ≤ (1 + 2 ε) * frozen_norm + δcorr` with
  `δcorr = |t| B + 2 ε |t| Gb`.

* **frozen law identity.**  `∫ frozen_norm = modelBlockSum / (n + 1)`, supplied
  by `OTSelector.Probability.integral_frozenModelTileBlock_eq_modelBlockSum_of_bounds`.

* **correction bound and vanishing.**  The correction is the `probeCorrectionBound`
  shape `|t| * (modulus ρ + 2 G farMass) + 2 ε |t| Gb`; its vanishing is
  `tendsto_probeCorrectionBound_of_pressure`, and the expected weighted error
  estimate is `integral_normalized_weighted_probe_error_le`.

The main per-scale result is
`integral_finslerNormalizedTileBlock_le_modelBlockSum_add`; the sequence-level
results are `finslerExpectationUpperBound_of_frozen_comparison` and
`finsler_hupper_of_frozen_comparison`.

No `sorry`, `admit` or added axiom occurs.
-/

open MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Probability OTSelector.Geometry
open scoped BigOperators ENNReal NNReal Topology ContDiff BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}

/-- **Per-scale additive `hblock` from the frozen comparison.**

At one sample size `n`, fix a tile `c`.  Assume:

* the per-edge freezing bound `|physical kinetic - frozenCost| ≤ 2 ε frozenCost`
  and the per-edge probe bounds `|physical probe - modelProbe| ≤ B`,
  `|modelProbe| ≤ Gb` on the tile edges;
* the normalized physical block and the normalized frozen block are integrable;
* the frozen law identity bounds the expected normalized frozen block by
  `modelBlockSum/(n+1)`, and by the explicit bound `Bnd`.

Then the expected normalized physical block is at most
`modelBlockSum/(n+1) + (2 ε Bnd + δcorr)` with the additive correction
`δcorr = |t| * B + 2 ε * |t| * Gb`.

All non-integrability inputs are deterministic; the law identity and the
integrability are the only probabilistic inputs. -/
theorem integral_finslerNormalizedTileBlock_le_modelBlockSum_add
    {n : ℕ} (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (P : Measure (Ω n)) [IsProbabilityMeasure P]
    (blockS blockT : Fin (n + 1) → Ω n → ι) (X Y : Fin (n + 1) → Ω n → M)
    (φ : M → ℝ) (k : ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : ι)
    {q : ℕ} {A C : Type*} [MeasurableSpace A] [MeasurableSpace C]
    (kin : ι → A → C → (Fin q → ℝ) → ℝ) (g : ι → A → C → ℝ)
    (α : ι → Measure A) (β : ι → Measure C)
    [∀ c, IsProbabilityMeasure (α c)] [∀ c, IsProbabilityMeasure (β c)]
    (w : ι → unitInterval)
    (frozenCost modelProbe : Ω n → Fin (n + 1) → Fin (n + 1) → ℝ)
    (ε B Gb Bnd : ℝ) (hε0 : 0 ≤ ε) (hB0 : 0 ≤ B) (hGb0 : 0 ≤ Gb)
    (hF0 : ∀ ξ i j, blockS i ξ = c → blockT j ξ = c → 0 ≤ frozenCost ξ i j)
    (hrel : ∀ ξ i j, blockS i ξ = c → blockT j ξ = c →
      |finslerTileKinetic F (fun i => X i ξ) (fun j => Y j ξ) φ k i j -
          frozenCost ξ i j| ≤ 2 * ε * frozenCost ξ i j)
    (hprobe : ∀ ξ i j, blockS i ξ = c → blockT j ξ = c →
      |finslerTileProbe μ ν K hK hμ hν (fun i => X i ξ) (fun j => Y j ξ) f i j -
          modelProbe ξ i j| ≤ B)
    (hG : ∀ ξ i j, blockS i ξ = c → blockT j ξ = c → |modelProbe ξ i j| ≤ Gb)
    (hintPhys : Integrable (fun ξ =>
      finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK hμ hν
        blockS blockT X Y φ k f t c ξ) P)
    (hintModel : Integrable (fun ξ =>
      frozenModelTileBlock (fun i => blockS i ξ) (fun j => blockT j ξ)
        (frozenCost ξ) (modelProbe ξ) t c / ((n + 1 : ℕ) : ℝ)) P)
    (hmodel_law : (∫ ξ,
      frozenModelTileBlock (fun i => blockS i ξ) (fun j => blockT j ξ)
        (frozenCost ξ) (modelProbe ξ) t c / ((n + 1 : ℕ) : ℝ) ∂P) ≤
      modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ))
    (hmodel_bound : (∫ ξ,
      frozenModelTileBlock (fun i => blockS i ξ) (fun j => blockT j ξ)
        (frozenCost ξ) (modelProbe ξ) t c / ((n + 1 : ℕ) : ℝ) ∂P) ≤ Bnd) :
    (∫ ξ, finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK hμ hν
      blockS blockT X Y φ k f t c ξ ∂P) ≤
      modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ) +
        (2 * ε * Bnd + (|t| * B + 2 * ε * (|t| * Gb))) := by
  classical
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  -- The deterministic pointwise comparison at each sample point.
  have hcomp : ∀ ξ,
      finslerTileBlock F μ ν K hK hμ hν (fun i => blockS i ξ) (fun j => blockT j ξ)
        (fun i => X i ξ) (fun j => Y j ξ) φ k f t c ≤
      (1 + 2 * ε) * frozenModelTileBlock (fun i => blockS i ξ) (fun j => blockT j ξ)
          (frozenCost ξ) (modelProbe ξ) t c +
        (min (blockSizeS (fun i => blockS i ξ) c) (blockSizeT (fun j => blockT j ξ) c) : ℝ) *
          (|t| * B + 2 * ε * (|t| * Gb)) :=
    fun ξ => finslerTileBlock_le_frozenModelTileBlock F μ ν K hK hμ hν
      (fun i => blockS i ξ) (fun j => blockT j ξ) (fun i => X i ξ) (fun j => Y j ξ)
      φ k f t c (frozenCost ξ) (modelProbe ξ) hε0
      (hF0 ξ) (hrel ξ) (hprobe ξ) (hG ξ)
  -- The normalized additive pointwise comparison with the constant correction.
  have hpoint : ∀ ξ,
      finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK hμ hν
        blockS blockT X Y φ k f t c ξ ≤
      (1 + 2 * ε) *
          (frozenModelTileBlock (fun i => blockS i ξ) (fun j => blockT j ξ)
            (frozenCost ξ) (modelProbe ξ) t c / ((n + 1 : ℕ) : ℝ)) +
        (|t| * B + 2 * ε * (|t| * Gb)) := by
    intro ξ
    have h := finslerNormalizedTileBlock_le_frozenModelTileBlock_add
      (F := F) (n := n) μ ν K hK hμ hν blockS blockT X Y φ k f t c ξ
      (frozenCost ξ) (modelProbe ξ) (hcomp ξ)
    have hmin : (min (blockSizeS (fun i => blockS i ξ) c)
          (blockSizeT (fun j => blockT j ξ) c) : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one hNpos]
      exact_mod_cast le_trans (Nat.min_le_left _ _)
        (OTSelector.Probability.blockSizeS_le (fun i => blockS i ξ) c)
    have hfac : 0 ≤ |t| * B + 2 * ε * (|t| * Gb) := by
      have h1 : 0 ≤ |t| * B := mul_nonneg (abs_nonneg t) hB0
      have h2 : 0 ≤ 2 * ε * (|t| * Gb) := by positivity
      linarith
    calc
      finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK hμ hν
          blockS blockT X Y φ k f t c ξ
          ≤ (1 + 2 * ε) *
              (frozenModelTileBlock (fun i => blockS i ξ) (fun j => blockT j ξ)
                (frozenCost ξ) (modelProbe ξ) t c / ((n + 1 : ℕ) : ℝ)) +
            ((min (blockSizeS (fun i => blockS i ξ) c)
              (blockSizeT (fun j => blockT j ξ) c) : ℝ) / ((n + 1 : ℕ) : ℝ)) *
              (|t| * B + 2 * ε * (|t| * Gb)) := h
      _ ≤ (1 + 2 * ε) *
              (frozenModelTileBlock (fun i => blockS i ξ) (fun j => blockT j ξ)
                (frozenCost ξ) (modelProbe ξ) t c / ((n + 1 : ℕ) : ℝ)) +
            (|t| * B + 2 * ε * (|t| * Gb)) := by
          gcongr
          exact mul_le_of_le_one_left hfac hmin
      _ = _ := rfl
  -- Apply the additive assembly at the single tile `c`.
  have haux := integral_normalized_block_le_model_add (P := P) (ι := Unit)
    (phys := fun _ ξ => finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK hμ hν
      blockS blockT X Y φ k f t c ξ)
    (model := fun _ ξ => frozenModelTileBlock (fun i => blockS i ξ) (fun j => blockT j ξ)
      (frozenCost ξ) (modelProbe ξ) t c / ((n + 1 : ℕ) : ℝ))
    (corr := fun _ _ => |t| * B + 2 * ε * (|t| * Gb))
    (modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) / ((n + 1 : ℕ) : ℝ))
    Bnd (|t| * B + 2 * ε * (|t| * Gb)) ε hε0
    (fun _ => Filter.Eventually.of_forall hpoint)
    (fun _ => hintPhys) (fun _ => hintModel)
    (fun _ => integrable_const _)
    (fun _ => hmodel_law) (fun _ => hmodel_bound)
    (fun _ => by
      rw [integral_const]
      simp)
  exact haux ()

end OTSelector.Reconstruction

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}

/-- **Sequence-level additive `hblock`: the frozen comparison assembled over
all scales.**

The per-scale bound `integral_finslerNormalizedTileBlock_le_modelBlockSum_add`
is applied at every `n` and `c` with the vanishing additive error

`δ n = 2 * ε n * Bnd n + (|t| * B n + 2 * ε n * (|t| * Gb n))`,

giving exactly the `hblock` hypothesis of the additive block-model assembly. -/
theorem integral_finslerNormalizedTileBlock_le_modelBlockSum_add_all
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (blockS blockT : ∀ n, Fin (n + 1) → Ω n → ι)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (φ : M → ℝ) (k : ℕ → ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ)
    {q : ℕ} {A C : Type*} [MeasurableSpace A] [MeasurableSpace C]
    (kin : ι → A → C → (Fin q → ℝ) → ℝ) (g : ι → A → C → ℝ)
    (α : ι → Measure A) (β : ι → Measure C)
    [∀ c, IsProbabilityMeasure (α c)] [∀ c, IsProbabilityMeasure (β c)]
    (w : ι → unitInterval)
    (frozenCost modelProbe : ∀ n, ι → Ω n → Fin (n + 1) → Fin (n + 1) → ℝ)
    (ε B Gb Bnd : ℕ → ℝ)
    (hε0 : ∀ n, 0 ≤ ε n) (hB0 : ∀ n, 0 ≤ B n) (hGb0 : ∀ n, 0 ≤ Gb n)
    (hBnd0 : ∀ n, 0 ≤ Bnd n)
    (hF0 : ∀ n c ξ i j, blockS n i ξ = c → blockT n j ξ = c →
      0 ≤ frozenCost n c ξ i j)
    (hrel : ∀ n c ξ i j, blockS n i ξ = c → blockT n j ξ = c →
      |finslerTileKinetic F (fun i => X n i ξ) (fun j => Y n j ξ) φ (k n) i j -
          frozenCost n c ξ i j| ≤ 2 * ε n * frozenCost n c ξ i j)
    (hprobe : ∀ n c ξ i j, blockS n i ξ = c → blockT n j ξ = c →
      |finslerTileProbe μ ν K hK hμ hν (fun i => X n i ξ) (fun j => Y n j ξ) f i j -
          modelProbe n c ξ i j| ≤ B n)
    (hG : ∀ n c ξ i j, blockS n i ξ = c → blockT n j ξ = c →
      |modelProbe n c ξ i j| ≤ Gb n)
    (hintBlock : ∀ n c, Integrable (fun ξ =>
      finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK hμ hν
        (blockS n) (blockT n) (X n) (Y n) φ (k n) f t c ξ) (P n))
    (hintModel : ∀ n c, Integrable (fun ξ =>
      frozenModelTileBlock (fun i => blockS n i ξ) (fun j => blockT n j ξ)
        (frozenCost n c ξ) (modelProbe n c ξ) t c / ((n + 1 : ℕ) : ℝ)) (P n))
    (hmodel_law : ∀ n c, (∫ ξ,
      frozenModelTileBlock (fun i => blockS n i ξ) (fun j => blockT n j ξ)
        (frozenCost n c ξ) (modelProbe n c ξ) t c / ((n + 1 : ℕ) : ℝ) ∂P n) ≤
      modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ))
    (hmodel_bound : ∀ n c, (∫ ξ,
      frozenModelTileBlock (fun i => blockS n i ξ) (fun j => blockT n j ξ)
        (frozenCost n c ξ) (modelProbe n c ξ) t c / ((n + 1 : ℕ) : ℝ) ∂P n) ≤ Bnd n) :
    ∀ n c, (∫ ξ, finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK hμ hν
        (blockS n) (blockT n) (X n) (Y n) φ (k n) f t c ξ ∂P n) ≤
      modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ) +
        (2 * ε n * Bnd n + (|t| * B n + 2 * ε n * (|t| * Gb n))) := by
  intro n c
  exact Reconstruction.integral_finslerNormalizedTileBlock_le_modelBlockSum_add
    μ ν K hK hμ hν (P n) (blockS n) (blockT n) (X n) (Y n) φ (k n) f t c
    kin g α β w (frozenCost n c) (modelProbe n c) (ε n) (B n) (Gb n) (Bnd n)
    (hε0 n) (hB0 n) (hGb0 n) (hF0 n c) (hrel n c) (hprobe n c) (hG n c)
    (hintBlock n c) (hintModel n c) (hmodel_law n c) (hmodel_bound n c)

/-- **The additive expectation upper bound from the frozen comparison.**

Composing `integral_finslerNormalizedTileBlock_le_modelBlockSum_add_all` with
`finslerExpectationUpperBound_of_additive_block_model` gives the normalized
expectation upper bound at the weighted sum of the local marked pressure
limits, provided the assembled additive error

`δ n = 2 * ε n * Bnd n + (|t| * B n + 2 * ε n * (|t| * Gb n))`

is nonnegative and tends to zero.  The remaining hypotheses are exactly those of
the additive assembly (`hintBlock`, `hintCount`, `hcount`) together with the
frozen-comparison inputs. The relative freezing comparison is required only
for all sufficiently large sample sizes; finitely many initial scales do not
affect the conclusion. -/
theorem finslerExpectationUpperBound_of_frozen_comparison
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : ProbabilityMeasure M)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (φ : M → ℝ)
    (hφ : let _instUpperPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (q : ℕ) (hq : 4 < q) {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (w : ι → unitInterval) (hwsum : ∑ c, (w c : ℝ) = 1) (hwpos : ∀ c, 0 < (w c : ℝ))
    {A C : Type*} [MeasurableSpace A] [MeasurableSpace C]
    {kin : ι → A → C → (Fin q → ℝ) → ℝ} {g : ι → A → C → ℝ}
    {Cb G : ℝ} (hCb0 : 0 ≤ Cb) (hG0 : 0 ≤ G)
    (hkin : ∀ c, Measurable (Function.uncurry (fun p : A × C => kin c p.1 p.2)))
    (hkin_bound : ∀ c a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hg : ∀ c, Measurable (Function.uncurry (g c)))
    (hgb : ∀ c a b, |g c a b| ≤ G)
    (α : ι → Measure A) (β : ι → Measure C)
    [∀ c, IsProbabilityMeasure (α c)] [∀ c, IsProbabilityMeasure (β c)]
    (p : ι → ℝ → ℝ)
    (hp : ∀ (c : ι) (t : ℝ), Tendsto
      (fun R => markedScalePressure q A C (α c) (β c) (kin c) (g c) R t)
      atTop (𝓝 (p c t)))
    (blockS blockT : ∀ n, Fin (n + 1) → Ω n → ι)
    (frozenCost modelProbe : ∀ n, ι → Ω n → Fin (n + 1) → Fin (n + 1) → ℝ)
    (ε B Gb Bnd : ℕ → ℝ)
    (hε0 : ∀ n, 0 ≤ ε n) (hB0 : ∀ n, 0 ≤ B n) (hGb0 : ∀ n, 0 ≤ Gb n)
    (hBnd0 : ∀ n, 0 ≤ Bnd n)
    (hF0 : ∀ n c ξ i j, blockS n i ξ = c → blockT n j ξ = c →
      0 ≤ frozenCost n c ξ i j)
    (hrel : ∀ᶠ n in atTop, ∀ c ξ i j, blockS n i ξ = c → blockT n j ξ = c →
      |finslerTileKinetic F (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) i j -
          frozenCost n c ξ i j| ≤
        2 * ε n * frozenCost n c ξ i j)
    (hprobe : ∀ n c ξ i j, blockS n i ξ = c → blockT n j ξ = c →
      |finslerTileProbe μ ν K hK.measurableSet hμ hν
          (fun i => X n i ξ) (fun j => Y n j ξ) f i j -
          modelProbe n c ξ i j| ≤ B n)
    (hG : ∀ n c ξ i j, blockS n i ξ = c → blockT n j ξ = c →
      |modelProbe n c ξ i j| ≤ Gb n)
    (hintBlock : ∀ n c, Integrable (fun ξ =>
      finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet hμ hν
        (blockS n) (blockT n) (X n) (Y n) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ) (P n))
    (hintModel : ∀ n c, Integrable (fun ξ =>
      frozenModelTileBlock (fun i => blockS n i ξ) (fun j => blockT n j ξ)
        (frozenCost n c ξ) (modelProbe n c ξ) t c / ((n + 1 : ℕ) : ℝ)) (P n))
    (hmodel_law : ∀ n c, (∫ ξ,
      frozenModelTileBlock (fun i => blockS n i ξ) (fun j => blockT n j ξ)
        (frozenCost n c ξ) (modelProbe n c ξ) t c / ((n + 1 : ℕ) : ℝ) ∂P n) ≤
      modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ))
    (hmodel_bound : ∀ n c, (∫ ξ,
      frozenModelTileBlock (fun i => blockS n i ξ) (fun j => blockT n j ξ)
        (frozenCost n c ξ) (modelProbe n c ξ) t c / ((n + 1 : ℕ) : ℝ) ∂P n) ≤ Bnd n)
    (hintCount : ∀ n c, Integrable (fun ξ =>
      |tileSourceCount (blockS n) c ξ - tileTargetCount (blockT n) c ξ|) (P n))
    (hcount : ∀ n c, ∫ ξ,
      |tileSourceCount (blockS n) c ξ - tileTargetCount (blockT n) c ξ| ∂P n ≤
      Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (w c : ℝ)))
    (hδ : Tendsto (fun n =>
      2 * ε n * Bnd n + (|t| * B n + 2 * ε n * (|t| * Gb n))) atTop (𝓝 0)) :
    ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop,
      (∫ ξ, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t ∂P n) ≤
        (∑ c, (w c : ℝ) * p c t) + ε' := by
  let δ : ℕ → ℝ := fun n =>
    2 * ε n * Bnd n + (|t| * B n + 2 * ε n * (|t| * Gb n))
  have hblock : ∀ᶠ n in atTop, ∀ c, (∫ ξ, finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K
      hK.measurableSet hμ hν (blockS n) (blockT n) (X n) (Y n) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ ∂P n) ≤
      modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ) + δ n := by
    filter_upwards [hrel] with n hnrel
    intro c
    exact Reconstruction.integral_finslerNormalizedTileBlock_le_modelBlockSum_add
      μ ν K hK.measurableSet hμ hν (P n) (blockS n) (blockT n) (X n) (Y n)
      φ (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c kin g α β w
      (frozenCost n c) (modelProbe n c) (ε n) (B n) (Gb n) (Bnd n)
      (hε0 n) (hB0 n) (hGb0 n) (hF0 n c) (hnrel c) (hprobe n c) (hG n c)
      (hintBlock n c) (hintModel n c) (hmodel_law n c) (hmodel_bound n c)
  have hδ0 : ∀ n, 0 ≤ δ n := by
    intro n
    have h1 : 0 ≤ |t| * B n := mul_nonneg (abs_nonneg t) (hB0 n)
    have h2 : 0 ≤ 2 * ε n * (|t| * Gb n) := by
      have h3 : 0 ≤ |t| * Gb n := mul_nonneg (abs_nonneg t) (hGb0 n)
      nlinarith [hε0 n, h3]
    have h4 : 0 ≤ 2 * ε n * Bnd n := by nlinarith [hε0 n, hBnd0 n]
    simp only [δ]
    linarith
  have hδ' : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ] using hδ
  exact finslerExpectationUpperBound_of_additive_block_model
    (F := F) hcomplete μ ν K hK hμ hν P X Y hX hY hXlaw hYlaw φ hφ f t q hq
    w hwsum hwpos hCb0 hG0 hkin hkin_bound hg hgb α β p hp
    blockS blockT hintBlock hintCount hcount δ hδ0 hδ' hblock

/-- **The additive `hupper` interface from the frozen comparison.**

If the target pressure agrees with the weighted sum of the local marked
pressure limits at the fixed probe and tilt, the expectation upper bound of
`finslerExpectationUpperBound_of_frozen_comparison` is exactly the `hupper`
clause of `exists_finsler_pressure_producer_of_squeeze`. -/
theorem finsler_hupper_of_frozen_comparison
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : ProbabilityMeasure M)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (φ : M → ℝ)
    (hφ : let _instUpperPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (q : ℕ) (hq : 4 < q) {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (w : ι → unitInterval) (hwsum : ∑ c, (w c : ℝ) = 1) (hwpos : ∀ c, 0 < (w c : ℝ))
    {A C : Type*} [MeasurableSpace A] [MeasurableSpace C]
    {kin : ι → A → C → (Fin q → ℝ) → ℝ} {g : ι → A → C → ℝ}
    {Cb G : ℝ} (hCb0 : 0 ≤ Cb) (hG0 : 0 ≤ G)
    (hkin : ∀ c, Measurable (Function.uncurry (fun p : A × C => kin c p.1 p.2)))
    (hkin_bound : ∀ c a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hg : ∀ c, Measurable (Function.uncurry (g c)))
    (hgb : ∀ c a b, |g c a b| ≤ G)
    (α : ι → Measure A) (β : ι → Measure C)
    [∀ c, IsProbabilityMeasure (α c)] [∀ c, IsProbabilityMeasure (β c)]
    (p : ι → ℝ → ℝ)
    (hp : ∀ (c : ι) (t : ℝ), Tendsto
      (fun R => markedScalePressure q A C (α c) (β c) (kin c) (g c) R t)
      atTop (𝓝 (p c t)))
    (blockS blockT : ∀ n, Fin (n + 1) → Ω n → ι)
    (frozenCost modelProbe : ∀ n, ι → Ω n → Fin (n + 1) → Fin (n + 1) → ℝ)
    (ε B Gb Bnd : ℕ → ℝ)
    (hε0 : ∀ n, 0 ≤ ε n) (hB0 : ∀ n, 0 ≤ B n) (hGb0 : ∀ n, 0 ≤ Gb n)
    (hBnd0 : ∀ n, 0 ≤ Bnd n)
    (hF0 : ∀ n c ξ i j, blockS n i ξ = c → blockT n j ξ = c →
      0 ≤ frozenCost n c ξ i j)
    (hrel : ∀ᶠ n in atTop, ∀ c ξ i j, blockS n i ξ = c → blockT n j ξ = c →
      |finslerTileKinetic F (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) i j -
          frozenCost n c ξ i j| ≤
        2 * ε n * frozenCost n c ξ i j)
    (hprobe : ∀ n c ξ i j, blockS n i ξ = c → blockT n j ξ = c →
      |finslerTileProbe μ ν K hK.measurableSet hμ hν
          (fun i => X n i ξ) (fun j => Y n j ξ) f i j -
          modelProbe n c ξ i j| ≤ B n)
    (hG : ∀ n c ξ i j, blockS n i ξ = c → blockT n j ξ = c →
      |modelProbe n c ξ i j| ≤ Gb n)
    (hintBlock : ∀ n c, Integrable (fun ξ =>
      finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet hμ hν
        (blockS n) (blockT n) (X n) (Y n) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ) (P n))
    (hintModel : ∀ n c, Integrable (fun ξ =>
      frozenModelTileBlock (fun i => blockS n i ξ) (fun j => blockT n j ξ)
        (frozenCost n c ξ) (modelProbe n c ξ) t c / ((n + 1 : ℕ) : ℝ)) (P n))
    (hmodel_law : ∀ n c, (∫ ξ,
      frozenModelTileBlock (fun i => blockS n i ξ) (fun j => blockT n j ξ)
        (frozenCost n c ξ) (modelProbe n c ξ) t c / ((n + 1 : ℕ) : ℝ) ∂P n) ≤
      modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ))
    (hmodel_bound : ∀ n c, (∫ ξ,
      frozenModelTileBlock (fun i => blockS n i ξ) (fun j => blockT n j ξ)
        (frozenCost n c ξ) (modelProbe n c ξ) t c / ((n + 1 : ℕ) : ℝ) ∂P n) ≤ Bnd n)
    (hintCount : ∀ n c, Integrable (fun ξ =>
      |tileSourceCount (blockS n) c ξ - tileTargetCount (blockT n) c ξ|) (P n))
    (hcount : ∀ n c, ∫ ξ,
      |tileSourceCount (blockS n) c ξ - tileTargetCount (blockT n) c ξ| ∂P n ≤
      Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (w c : ℝ)))
    (hδ : Tendsto (fun n =>
      2 * ε n * Bnd n + (|t| * B n + 2 * ε n * (|t| * Gb n))) atTop (𝓝 0))
    (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hpressure : pressure f t = ∑ c, (w c : ℝ) * p c t) :
    ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop,
      (∫ ξ, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t ∂P n) ≤
        pressure f t + ε' := by
  have h := finslerExpectationUpperBound_of_frozen_comparison
    (F := F) hcomplete μ ν K hK hμ hν P X Y hX hY hXlaw hYlaw φ hφ f t q hq
    w hwsum hwpos hCb0 hG0 hkin hkin_bound hg hgb α β p hp
    blockS blockT frozenCost modelProbe ε B Gb Bnd
    hε0 hB0 hGb0 hBnd0 hF0 hrel hprobe hG hintBlock hintModel hmodel_law
    hmodel_bound hintCount hcount hδ
  intro ε' hε'
  filter_upwards [h ε' hε'] with n hn
  rwa [hpressure]

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
