import OTSelector.Reconstruction.FinslerTileProbeCorrection
import OTSelector.Limit.FinslerCanonicalTileData

/-!
# Aggregate frozen comparison with a fixed geometric error

The total fraction of points matched inside disjoint tiles is at most one.
Consequently the probe correction in the relative physical/frozen comparison
is paid once, regardless of how many cells the geometric cover has.  The
comparison is valid at every sample size, with no uniform bound on the
scaled kinetic kernels and with almost-everywhere geometric readouts.
-/

open MeasureTheory ProbabilityTheory Filter Manifold
open scoped BigOperators Topology ContDiff BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace OTSelector.PartialMatching

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sum of the numbers of edges matched inside disjoint tiles is bounded
by the number of source points. -/
theorem sum_min_blockSize_le (s t : Fin N → ι) :
    ∑ c, min (blockSizeS s c) (blockSizeT t c) ≤ N := by
  calc ∑ c, min (blockSizeS s c) (blockSizeT t c)
      ≤ ∑ c, blockSizeS s c := Finset.sum_le_sum fun _ _ ↦ Nat.min_le_left _ _
    _ = N := sum_card_blockFinset s

/-- Aggregate relative comparison.  The correction is independent of the
number of tiles because every point is used at most once. -/
theorem sum_normalized_blockValue_le_of_relative
    (hn : 0 < N) (s t : Fin N → ι)
    (phys frozen probe modelProbe : Fin N → Fin N → ℝ)
    {tilt relative probeError probeBound : ℝ}
    (hrelative : 0 ≤ relative) (herror : 0 ≤ probeError) (hbound : 0 ≤ probeBound)
    (hfrozen : ∀ c i j, s i = c → t j = c → 0 ≤ frozen i j)
    (hrel : ∀ c i j, s i = c → t j = c →
      |phys i j - frozen i j| ≤ relative * frozen i j)
    (hprobe : ∀ c i j, s i = c → t j = c →
      |probe i j - modelProbe i j| ≤ probeError)
    (hmodelProbe : ∀ c i j, s i = c → t j = c →
      |modelProbe i j| ≤ probeBound) :
    (∑ c, maxCardValue (blockCost s t (perturbedEdgeCost phys probe tilt) c) /
        (N : ℝ)) ≤
      (1 + relative) *
        (∑ c, maxCardValue (blockCost s t
          (perturbedEdgeCost frozen modelProbe tilt) c) / (N : ℝ)) +
      (|tilt| * probeError + relative * (|tilt| * probeBound)) := by
  classical
  have hnpos : (0 : ℝ) < N := Nat.cast_pos.mpr hn
  let correction := |tilt| * probeError + relative * (|tilt| * probeBound)
  have hcorr : 0 ≤ correction := by dsimp [correction]; positivity
  have hcomp (c : ι) := maxCardValue_blockCost_perturbed_le_of_relative
    (blockS := s) (blockT := t) (c := c)
    (F := frozen) (P := phys) (G := modelProbe) (Q := probe)
    (t := tilt) (B := probeError) (δ := relative) (Gb := probeBound)
    hrelative (hfrozen c) (hrel c) (hprobe c) (hmodelProbe c)
  have hsum : (∑ c, maxCardValue
      (blockCost s t (perturbedEdgeCost phys probe tilt) c)) ≤
      (1 + relative) * (∑ c, maxCardValue
        (blockCost s t (perturbedEdgeCost frozen modelProbe tilt) c)) +
        (N : ℝ) * correction := by
    calc (∑ c, maxCardValue (blockCost s t (perturbedEdgeCost phys probe tilt) c))
        ≤ ∑ c, ((1 + relative) * maxCardValue
            (blockCost s t (perturbedEdgeCost frozen modelProbe tilt) c) +
            (min (blockSizeS s c) (blockSizeT t c) : ℝ) * correction) :=
          Finset.sum_le_sum fun c _ ↦ hcomp c
      _ = (1 + relative) * (∑ c, maxCardValue
            (blockCost s t (perturbedEdgeCost frozen modelProbe tilt) c)) +
          (∑ c, (min (blockSizeS s c) (blockSizeT t c) : ℝ)) * correction := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      _ ≤ _ := by
        gcongr
        exact_mod_cast sum_min_blockSize_le s t
  rw [← Finset.sum_div, ← Finset.sum_div]
  apply (div_le_div_of_nonneg_right hsum hnpos.le).trans
  exact le_of_eq (by field_simp; ring)

end OTSelector.PartialMatching

namespace OTSelector.Reconstruction

open OTSelector.Geometry OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The normalized sum of actual physical blocks is relatively bounded by
the frozen sum, with a single probe correction for the whole cover. -/
theorem sum_finslerNormalizedTileBlock_le_frozen_sum
    {n : ℕ} {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s t : Fin (n + 1) → Ω n → ι) (X Y : Fin (n + 1) → Ω n → M)
    (φ : M → ℝ) (scale : ℝ) (f : (K × K) →ᵇ ℝ) (tilt : ℝ) (ξ : Ω n)
    (frozen modelProbe : Fin (n + 1) → Fin (n + 1) → ℝ)
    {relative probeError probeBound : ℝ}
    (hrelative : 0 ≤ relative) (herror : 0 ≤ probeError) (hbound : 0 ≤ probeBound)
    (hfrozen : ∀ c i j, s i ξ = c → t j ξ = c → 0 ≤ frozen i j)
    (hrel : ∀ c i j, s i ξ = c → t j ξ = c →
      |finslerTileKinetic F (fun i ↦ X i ξ) (fun j ↦ Y j ξ) φ scale i j -
        frozen i j| ≤ relative * frozen i j)
    (hprobe : ∀ c i j, s i ξ = c → t j ξ = c →
      |finslerTileProbe μ ν K hK hμ hν (fun i ↦ X i ξ) (fun j ↦ Y j ξ) f i j -
        modelProbe i j| ≤ probeError)
    (hmodelProbe : ∀ c i j, s i ξ = c → t j ξ = c →
      |modelProbe i j| ≤ probeBound) :
    (∑ c, finslerNormalizedTileBlock F μ ν K hK hμ hν s t X Y φ scale f tilt c ξ) ≤
      (1 + relative) * (∑ c, OTSelector.frozenModelTileBlock
        (fun i ↦ s i ξ) (fun j ↦ t j ξ) frozen modelProbe tilt c /
          ((n + 1 : ℕ) : ℝ)) +
      (|tilt| * probeError + relative * (|tilt| * probeBound)) := by
  exact PartialMatching.sum_normalized_blockValue_le_of_relative (Nat.succ_pos n)
    (fun i ↦ s i ξ) (fun j ↦ t j ξ)
    (finslerTileKinetic F (fun i ↦ X i ξ) (fun j ↦ Y j ξ) φ scale)
    frozen (finslerTileProbe μ ν K hK hμ hν (fun i ↦ X i ξ) (fun j ↦ Y j ξ) f)
    modelProbe hrelative herror hbound hfrozen hrel hprobe hmodelProbe

/-- Integrating the aggregate comparison only needs the geometric readout
almost everywhere.  The scaled frozen kernel may have an arbitrary bound at
each sample size. -/
theorem integral_sum_finslerNormalizedTileBlock_le_frozen_sum
    {n : ℕ} {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (sample : Measure (Ω n)) [IsProbabilityMeasure sample]
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s t : Fin (n + 1) → Ω n → ι) (X Y : Fin (n + 1) → Ω n → M)
    (φ : M → ℝ) (scale : ℝ) (f : (K × K) →ᵇ ℝ) (tilt : ℝ)
    (frozen modelProbe : Ω n → Fin (n + 1) → Fin (n + 1) → ℝ)
    {relative probeError probeBound : ℝ}
    (hrelative : 0 ≤ relative) (herror : 0 ≤ probeError) (hbound : 0 ≤ probeBound)
    (hedge : ∀ᵐ ξ ∂sample, ∀ c i j, s i ξ = c → t j ξ = c →
      0 ≤ frozen ξ i j ∧
      |finslerTileKinetic F (fun i ↦ X i ξ) (fun j ↦ Y j ξ) φ scale i j -
        frozen ξ i j| ≤ relative * frozen ξ i j ∧
      |finslerTileProbe μ ν K hK hμ hν (fun i ↦ X i ξ) (fun j ↦ Y j ξ) f i j -
        modelProbe ξ i j| ≤ probeError ∧ |modelProbe ξ i j| ≤ probeBound)
    (hintPhys : ∀ c, Integrable (fun ξ ↦
      finslerNormalizedTileBlock F μ ν K hK hμ hν s t X Y φ scale f tilt c ξ) sample)
    (hintFrozen : ∀ c, Integrable (fun ξ ↦ OTSelector.frozenModelTileBlock
      (fun i ↦ s i ξ) (fun j ↦ t j ξ) (frozen ξ) (modelProbe ξ) tilt c /
        ((n + 1 : ℕ) : ℝ)) sample) :
    (∑ c, ∫ ξ, finslerNormalizedTileBlock F μ ν K hK hμ hν
      s t X Y φ scale f tilt c ξ ∂sample) ≤
      (1 + relative) * (∑ c, ∫ ξ, OTSelector.frozenModelTileBlock
        (fun i ↦ s i ξ) (fun j ↦ t j ξ) (frozen ξ) (modelProbe ξ) tilt c /
          ((n + 1 : ℕ) : ℝ) ∂sample) +
      (|tilt| * probeError + relative * (|tilt| * probeBound)) := by
  classical
  have hp := integrable_finsetSum Finset.univ (fun c _ ↦ hintPhys c)
  have hf := integrable_finsetSum Finset.univ (fun c _ ↦ hintFrozen c)
  have hpoint : ∀ᵐ ξ ∂sample,
      (∑ c, finslerNormalizedTileBlock F μ ν K hK hμ hν s t X Y φ scale f tilt c ξ) ≤
      (1 + relative) * (∑ c, OTSelector.frozenModelTileBlock
        (fun i ↦ s i ξ) (fun j ↦ t j ξ) (frozen ξ) (modelProbe ξ) tilt c /
          ((n + 1 : ℕ) : ℝ)) +
        (|tilt| * probeError + relative * (|tilt| * probeBound)) := by
    filter_upwards [hedge] with ξ hξ
    apply sum_finslerNormalizedTileBlock_le_frozen_sum μ ν K hK hμ hν s t X Y
      φ scale f tilt ξ (frozen ξ) (modelProbe ξ) hrelative herror hbound
    · exact fun c i j hi hj ↦ (hξ c i j hi hj).1
    · exact fun c i j hi hj ↦ (hξ c i j hi hj).2.1
    · exact fun c i j hi hj ↦ (hξ c i j hi hj).2.2.1
    · exact fun c i j hi hj ↦ (hξ c i j hi hj).2.2.2
  have h := integral_mono_ae hp ((hf.const_mul _).add (integrable_const _)) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (hf.const_mul _) (integrable_const _), integral_const_mul,
    integral_const] at h
  simp only [probReal_univ, one_smul] at h
  simpa only [integral_finsetSum _ (fun c _ ↦ hintPhys c),
    integral_finsetSum _ (fun c _ ↦ hintFrozen c)] using h

end OTSelector.Reconstruction
