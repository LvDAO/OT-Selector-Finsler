import OTSelector.Finite.HierarchicalPartialMatching
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic

/-!
# Expected hierarchical bounds for maximum-cardinality matching values

The deterministic multiscale bound is integrated over an abstract probability
space.  The random point clouds may have random sizes; the only stochastic
inputs are the total counts, the per-level histogram discrepancies, and the
count difference.  This isolates the analytic step from the construction of the
Poisson cloud law.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

open OTSelector.Reconstruction

/-- Integrating the hierarchical matching bound.  If the random optimal value is
pathwise bounded by the count expression, and the count expressions have the
stated integrals, then the expected value is bounded by the integrated formula. -/
theorem integral_maxCardValue_le_of_counts
    {Ω X : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {K : ℕ} {C : Fin K → Type*} [∀ k, Fintype (C k)]
    (cell : (k : Fin K) → X → C k)
    (hnested : ∀ (k l : Fin K), k ≤ l → ∀ x y : X,
      cell l x = cell l y → cell k x = cell k y)
    (base : ℝ) (hb : 0 ≤ base) (weight : Fin K → ℝ) (hw : ∀ k, 0 ≤ weight k)
    (N M : Ω → ℕ) (x : ∀ ω, Fin (N ω) → X) (y : ∀ ω, Fin (M ω) → X)
    (cost : ∀ ω, Fin (N ω) → Fin (M ω) → ℝ)
    (hcost : ∀ ω i j, cost ω i j ≤ base + ∑ k, weight k *
      partitionDistance (cell k (x ω i)) (cell k (y ω j)))
    (hnonneg : ∀ ω i j, 0 ≤ cost ω i j)
    (hV : Integrable (fun ω => PartialMatching.maxCardValue (cost ω)) P)
    (hmax : Integrable (fun ω => ((max (N ω) (M ω) : ℕ) : ℝ)) P)
    (hD : ∀ k, Integrable (fun ω => ∑ c,
      |partitionCount (cell k ∘ x ω) c - partitionCount (cell k ∘ y ω) c|) P)
    (hDiff : Integrable (fun ω => |(N ω : ℝ) - (M ω : ℝ)|) P)
    (bmax : ℝ) (hbmax : ∫ ω, ((max (N ω) (M ω) : ℕ) : ℝ) ∂P ≤ bmax)
    (Dk : Fin K → ℝ)
    (hDk : ∀ k, ∫ ω, (∑ c,
      |partitionCount (cell k ∘ x ω) c - partitionCount (cell k ∘ y ω) c|) ∂P ≤ Dk k)
    (bdiff : ℝ) (hbdiff : ∫ ω, |(N ω : ℝ) - (M ω : ℝ)| ∂P ≤ bdiff) :
    ∫ ω, PartialMatching.maxCardValue (cost ω) ∂P ≤
      base * bmax + (1 / 2 : ℝ) * ∑ k, weight k * (Dk k + bdiff) := by
  classical
  -- Pointwise hierarchical bound.
  have hpoint : ∀ ω, PartialMatching.maxCardValue (cost ω) ≤
      ((max (N ω) (M ω) : ℕ) : ℝ) * base + (1 / 2 : ℝ) * ∑ k, weight k *
        ((∑ c, |partitionCount (cell k ∘ x ω) c -
            partitionCount (cell k ∘ y ω) c|) + |(N ω : ℝ) - (M ω : ℝ)|) := by
    intro ω
    have h := maxCardValue_le_hierarchical_counts
      (a := N ω) (b := M ω) cell hnested (x ω) (y ω) (cost ω)
      base hb weight hw (hcost ω) (hnonneg ω)
    simpa only [Function.comp_apply, Nat.cast_max] using h
  -- Integrability of the pointwise majorant.
  have hinner (k : Fin K) : Integrable (fun ω =>
      (∑ c, |partitionCount (cell k ∘ x ω) c -
        partitionCount (cell k ∘ y ω) c|) + |(N ω : ℝ) - (M ω : ℝ)|) P :=
    (hD k).add hDiff
  have hterm (k : Fin K) : Integrable (fun ω => weight k *
      ((∑ c, |partitionCount (cell k ∘ x ω) c -
        partitionCount (cell k ∘ y ω) c|) + |(N ω : ℝ) - (M ω : ℝ)|)) P :=
    (hinner k).const_mul (weight k)
  have hsum : Integrable (fun ω => ∑ k, weight k *
      ((∑ c, |partitionCount (cell k ∘ x ω) c -
        partitionCount (cell k ∘ y ω) c|) + |(N ω : ℝ) - (M ω : ℝ)|)) P :=
    integrable_finsetSum _ (fun k _ => hterm k)
  have hmajor : Integrable (fun ω => ((max (N ω) (M ω) : ℕ) : ℝ) * base +
      (1 / 2 : ℝ) * ∑ k, weight k *
        ((∑ c, |partitionCount (cell k ∘ x ω) c -
          partitionCount (cell k ∘ y ω) c|) + |(N ω : ℝ) - (M ω : ℝ)|)) P :=
    (hmax.mul_const base).add (hsum.const_mul (1 / 2 : ℝ))
  have hmono := integral_mono_ae hV hmajor (Filter.Eventually.of_forall hpoint)
  -- Integrate the majorant term by term.
  have hInt : ∫ ω, (((max (N ω) (M ω) : ℕ) : ℝ) * base +
      (1 / 2 : ℝ) * ∑ k, weight k *
        ((∑ c, |partitionCount (cell k ∘ x ω) c -
          partitionCount (cell k ∘ y ω) c|) + |(N ω : ℝ) - (M ω : ℝ)|)) ∂P =
      (∫ ω, ((max (N ω) (M ω) : ℕ) : ℝ) ∂P) * base +
        (1 / 2 : ℝ) * ∑ k, weight k *
          ((∫ ω, (∑ c, |partitionCount (cell k ∘ x ω) c -
              partitionCount (cell k ∘ y ω) c|) ∂P) +
            ∫ ω, |(N ω : ℝ) - (M ω : ℝ)| ∂P) := by
    rw [integral_add (hmax.mul_const base) (hsum.const_mul (1 / 2 : ℝ)),
      integral_mul_const, integral_const_mul, integral_finsetSum _ (fun k _ => hterm k)]
    rw [show (∑ i, ∫ a, weight i *
        (∑ c, |partitionCount (cell i ∘ x a) c - partitionCount (cell i ∘ y a) c| +
          |(N a : ℝ) - (M a : ℝ)|) ∂P) =
        ∑ k, weight k *
          ((∫ ω, ∑ c, |partitionCount (cell k ∘ x ω) c -
              partitionCount (cell k ∘ y ω) c| ∂P) +
            ∫ ω, |(N ω : ℝ) - (M ω : ℝ)| ∂P) from
      Finset.sum_congr rfl (fun k _ => by
        rw [integral_const_mul, integral_add (hD k) hDiff])]
  rw [hInt] at hmono
  -- Bound the integrated formula by the supplied constants.
  have hbase_le : (∫ ω, ((max (N ω) (M ω) : ℕ) : ℝ) ∂P) * base ≤ bmax * base :=
    mul_le_mul_of_nonneg_right hbmax hb
  have hsum_le : ∑ k, weight k *
      ((∫ ω, (∑ c, |partitionCount (cell k ∘ x ω) c -
          partitionCount (cell k ∘ y ω) c|) ∂P) +
        ∫ ω, |(N ω : ℝ) - (M ω : ℝ)| ∂P) ≤
      ∑ k, weight k * (Dk k + bdiff) := by
    apply Finset.sum_le_sum
    intro k _
    apply mul_le_mul_of_nonneg_left _ (hw k)
    exact add_le_add (hDk k) hbdiff
  have hsum2 := mul_le_mul_of_nonneg_left hsum_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
  linarith [hmono, hbase_le, hsum2]


/-- The expectation of the larger of two natural-valued counts, in terms of the
two means and the mean absolute difference. -/
theorem integral_max_nat_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N M : Ω → ℕ)
    (hN : Integrable (fun ω => (N ω : ℝ)) P)
    (hM : Integrable (fun ω => (M ω : ℝ)) P)
    (hD : Integrable (fun ω => |(N ω : ℝ) - (M ω : ℝ)|) P)
    (hmax : Integrable (fun ω => ((max (N ω) (M ω) : ℕ) : ℝ)) P) :
    ∫ ω, ((max (N ω) (M ω) : ℕ) : ℝ) ∂P ≤
      (∫ ω, (N ω : ℝ) ∂P) / 2 + (∫ ω, (M ω : ℝ) ∂P) / 2 +
        (∫ ω, |(N ω : ℝ) - (M ω : ℝ)| ∂P) / 2 := by
  have hpt : ∀ ω, ((max (N ω) (M ω) : ℕ) : ℝ) =
      ((N ω : ℝ) + (M ω : ℝ) + |(N ω : ℝ) - (M ω : ℝ)|) / 2 := by
    intro ω
    rcases le_total (N ω) (M ω) with h | h
    · have hcast : ((N ω : ℝ) ≤ (M ω : ℝ)) := by exact_mod_cast h
      rw [max_eq_right h, abs_of_nonpos (by linarith)]
      ring
    · have hcast : ((M ω : ℝ) ≤ (N ω : ℝ)) := by exact_mod_cast h
      rw [max_eq_left h, abs_of_nonneg (by linarith)]
      ring
  simp_rw [hpt]
  rw [integral_div]
  have hfg : Integrable (fun ω => (N ω : ℝ) + (M ω : ℝ)) P := hN.add hM
  change (∫ ω, ((N ω : ℝ) + (M ω : ℝ)) + |(N ω : ℝ) - (M ω : ℝ)| ∂P) / 2 ≤
    (∫ ω, (N ω : ℝ) ∂P) / 2 + (∫ ω, (M ω : ℝ) ∂P) / 2 +
      (∫ ω, |(N ω : ℝ) - (M ω : ℝ)| ∂P) / 2
  rw [integral_add hfg hD, integral_add hN hM]
  have h : ((∫ a, (N a : ℝ) ∂P) + (∫ a, (M a : ℝ) ∂P) +
        (∫ a, |(N a : ℝ) - (M a : ℝ)| ∂P)) / 2 =
      (∫ a, (N a : ℝ) ∂P) / 2 + (∫ a, (M a : ℝ) ∂P) / 2 +
        (∫ a, |(N a : ℝ) - (M a : ℝ)| ∂P) / 2 := by
    ring
  exact le_of_eq h

/-- Equal means convert the max bound into `mean + half the absolute-difference
mean`. -/
theorem integral_max_nat_le_of_equal_means
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N M : Ω → ℕ) (ν δ : ℝ)
    (hN : Integrable (fun ω => (N ω : ℝ)) P)
    (hM : Integrable (fun ω => (M ω : ℝ)) P)
    (hD : Integrable (fun ω => |(N ω : ℝ) - (M ω : ℝ)|) P)
    (hmax : Integrable (fun ω => ((max (N ω) (M ω) : ℕ) : ℝ)) P)
    (hNmean : ∫ ω, (N ω : ℝ) ∂P = ν)
    (hMmean : ∫ ω, (M ω : ℝ) ∂P = ν)
    (hDbound : ∫ ω, |(N ω : ℝ) - (M ω : ℝ)| ∂P ≤ δ) :
    ∫ ω, ((max (N ω) (M ω) : ℕ) : ℝ) ∂P ≤ ν + δ / 2 := by
  have h := integral_max_nat_le P N M hN hM hD hmax
  rw [hNmean, hMmean] at h
  linarith

end OTSelector.Probability
