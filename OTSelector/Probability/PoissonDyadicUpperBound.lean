import OTSelector.Finite.MaxCardValueScaling
import OTSelector.Probability.PoissonCubePressure
import OTSelector.Finite.DyadicCellCost
import OTSelector.Finite.HierarchicalPartialMatching
import OTSelector.Probability.HierarchicalMatchingExpectation
import OTSelector.Probability.PoissonCountDiscrepancy

/-!
# The dyadic cost bound for the Poissonized cube pressure

The quadratic edge cost of two truncated cube points is dominated by the dyadic
partition data of the two positions: a terminal cell-diameter term plus the
weighted sum of cell-mismatch indicators.  The truncation replaces points off
the unit cube by the origin, which changes nothing almost surely and makes the
bound valid for every sample.  This is the pathwise input of the integrated
hierarchical matching estimate.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open OTSelector.Reconstruction

noncomputable section
namespace OTSelector.Probability

/-- Coordinatewise truncation to the half-open unit cube. -/
noncomputable def cubeTruncPoint {q : ℕ} (x : Fin q → ℝ) : Fin q → ℝ :=
  fun l => if 0 ≤ x l ∧ x l < 1 then x l else 0

theorem cubeTruncPoint_mem {q : ℕ} (x : Fin q → ℝ) :
    ∀ l, 0 ≤ cubeTruncPoint x l ∧ cubeTruncPoint x l < 1 := by
  intro l
  unfold cubeTruncPoint
  split_ifs with h
  · exact h
  · exact ⟨le_refl 0, by norm_num⟩

theorem cubeTruncPoint_eq_of_mem {q : ℕ} {x : Fin q → ℝ}
    (hx : x ∈ unitCube q) : cubeTruncPoint x = x := by
  funext l
  have hl : x l ∈ Set.Ioo (0 : ℝ) 1 := Set.mem_pi.mp hx l (Set.mem_univ l)
  unfold cubeTruncPoint
  rw [if_pos ⟨le_of_lt hl.1, hl.2⟩]

/-- The dyadic upper bound for one edge: the truncated squared distance plus
the probe is bounded by the terminal diameter term plus the weighted dyadic
partition distance. -/
theorem dyadicEdgeCost_le (q : ℕ) {r t G : ℝ} (hr : 0 ≤ r) (hG0 : 0 ≤ G)
    {g : (Fin q → ℝ) → (Fin q → ℝ) → ℝ} (hgb : ∀ x y, |g x y| ≤ G)
    {K : ℕ} (hK : 0 < K) (ω : TwoCloudSpace q) (i j : ℕ) :
    r ^ (2 / (q : ℝ)) * sqDist (cubeTruncPoint (sourcePoint ω i))
        (cubeTruncPoint (targetPoint ω j)) + t * poissonCubeProbe g ω i j
      ≤ (r ^ (2 / (q : ℝ)) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) + |t| * G) +
        ∑ k : Fin K, (r ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ))) *
          partitionDistance (dyadicCell q (k : ℕ) (cubeTruncPoint (sourcePoint ω i)))
            (dyadicCell q (k : ℕ) (cubeTruncPoint (targetPoint ω j))) := by
  have hrpow : 0 ≤ r ^ (2 / (q : ℝ)) := Real.rpow_nonneg hr _
  have hgeo := sq_dist_le_dyadic_partitionDistance (q := q) (K := K) hK
    (x := cubeTruncPoint (sourcePoint ω i)) (y := cubeTruncPoint (targetPoint ω j))
    (cubeTruncPoint_mem _) (cubeTruncPoint_mem _)
  have hgeo' : sqDist (cubeTruncPoint (sourcePoint ω i))
      (cubeTruncPoint (targetPoint ω j)) ≤
      (4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K +
        ∑ k : Fin K, ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ)) *
          partitionDistance (dyadicCell q (k : ℕ) (cubeTruncPoint (sourcePoint ω i)))
            (dyadicCell q (k : ℕ) (cubeTruncPoint (targetPoint ω j))) := by
    have h := hgeo
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k) *
        partitionDistance (dyadicCell q k (cubeTruncPoint (sourcePoint ω i)))
          (dyadicCell q k (cubeTruncPoint (targetPoint ω j)))) K] at h
    exact h
  have hscaled := mul_le_mul_of_nonneg_left hgeo' hrpow
  have hprobe : t * poissonCubeProbe g ω i j ≤ |t| * G := by
    calc t * poissonCubeProbe g ω i j ≤ |t * poissonCubeProbe g ω i j| := le_abs_self _
      _ = |t| * |poissonCubeProbe g ω i j| := abs_mul _ _
      _ ≤ |t| * G := mul_le_mul_of_nonneg_left (hgb _ _) (abs_nonneg _)
  have hsum : r ^ (2 / (q : ℝ)) *
      ∑ k : Fin K, ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ)) *
        partitionDistance (dyadicCell q (k : ℕ) (cubeTruncPoint (sourcePoint ω i)))
          (dyadicCell q (k : ℕ) (cubeTruncPoint (targetPoint ω j))) =
      ∑ k : Fin K, (r ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ))) *
        partitionDistance (dyadicCell q (k : ℕ) (cubeTruncPoint (sourcePoint ω i)))
          (dyadicCell q (k : ℕ) (cubeTruncPoint (targetPoint ω j))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [mul_add, hsum] at hscaled
  linarith

/-- The truncated tilted edge cost (no nonnegativity shift). -/
noncomputable def truncatedEdgeCost (q : ℕ) (r : ℝ)
    (g : (Fin q → ℝ) → (Fin q → ℝ) → ℝ) (t : ℝ)
    (ω : TwoCloudSpace q) (i j : ℕ) : ℝ :=
  r ^ (2 / (q : ℝ)) * sqDist (cubeTruncPoint (sourcePoint ω i))
    (cubeTruncPoint (targetPoint ω j)) + t * poissonCubeProbe g ω i j

/-- The shifted truncated edge cost is nonnegative when the probe is bounded. -/
theorem shiftedEdgeCost_nonneg (q : ℕ) {r t G : ℝ} (hr : 0 ≤ r) (hG0 : 0 ≤ G)
    {g : (Fin q → ℝ) → (Fin q → ℝ) → ℝ} (hgb : ∀ x y, |g x y| ≤ G)
    (ω : TwoCloudSpace q) (i j : ℕ) :
    0 ≤ truncatedEdgeCost q r g t ω i j + |t| * G := by
  have hrpow : 0 ≤ r ^ (2 / (q : ℝ)) := Real.rpow_nonneg hr _
  have hsq : 0 ≤ sqDist (cubeTruncPoint (sourcePoint ω i))
      (cubeTruncPoint (targetPoint ω j)) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hprobe : -( |t| * G) ≤ t * poissonCubeProbe g ω i j := by
    have habs : |poissonCubeProbe g ω i j| ≤ G := hgb _ _
    have hmul : |t| * |poissonCubeProbe g ω i j| ≤ |t| * G :=
      mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    have h6 : -( |t * poissonCubeProbe g ω i j|) ≤ t * poissonCubeProbe g ω i j :=
      neg_abs_le _
    rw [abs_mul] at h6
    linarith
  have hfirst : 0 ≤ r ^ (2 / (q : ℝ)) * sqDist (cubeTruncPoint (sourcePoint ω i))
      (cubeTruncPoint (targetPoint ω j)) := mul_nonneg hrpow hsq
  unfold truncatedEdgeCost
  linarith

/-- The shifted truncated edge cost obeys the dyadic hierarchical bound with the
shifted base. -/
theorem shiftedEdgeCost_le_hier (q : ℕ) {r t G : ℝ} (hr : 0 ≤ r) (hG0 : 0 ≤ G)
    {g : (Fin q → ℝ) → (Fin q → ℝ) → ℝ} (hgb : ∀ x y, |g x y| ≤ G)
    {K : ℕ} (hK : 0 < K) (ω : TwoCloudSpace q) (i j : ℕ) :
    truncatedEdgeCost q r g t ω i j + |t| * G
      ≤ (r ^ (2 / (q : ℝ)) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) + 2 * (|t| * G)) +
        ∑ k : Fin K, (r ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ))) *
          partitionDistance (dyadicCell q (k : ℕ) (cubeTruncPoint (sourcePoint ω i)))
            (dyadicCell q (k : ℕ) (cubeTruncPoint (targetPoint ω j))) := by
  have h := dyadicEdgeCost_le q (t := t) hr hG0 hgb hK ω i j
  unfold truncatedEdgeCost
  linarith

/-- The shifted and unshifted truncated cloud values differ by the cardinality
times the shift. -/
theorem cloudValueNat_shifted_eq (q : ℕ) (r : ℝ)
    (g : (Fin q → ℝ) → (Fin q → ℝ) → ℝ) (t G : ℝ) (ω : TwoCloudSpace q) :
    cloudValueNat (fun ω i j => truncatedEdgeCost q r g t ω i j + |t| * G)
        (sourceCount) (targetCount) ω =
      cloudValueNat (truncatedEdgeCost q r g t) (sourceCount) (targetCount) ω +
        ((min (sourceCount ω) (targetCount ω) : ℕ) : ℝ) * (|t| * G) := by
  unfold cloudValueNat
  have hmat : (fun i : Fin (sourceCount ω) => fun j : Fin (targetCount ω) =>
        truncatedEdgeCost q r g t ω i j + |t| * G) =
      fun i : Fin (sourceCount ω) => fun j : Fin (targetCount ω) =>
        truncatedEdgeCost q r g t ω i j + |t| * G := rfl
  rw [hmat]
  simpa only [Nat.cast_min] using PartialMatching.maxCardValue_add_const
    (fun i : Fin (sourceCount ω) => fun j : Fin (targetCount ω) =>
      truncatedEdgeCost q r g t ω i j) (|t| * G)

/-- On the unit cube the truncated edge cost equals the clamped model edge on
every in-cloud pair. -/
theorem cloudValueNat_truncated_eq_tilted_ae (q : ℕ) (r : ℝ≥0)
    (g : (Fin q → ℝ) → (Fin q → ℝ) → ℝ) (t : ℝ) :
    ∀ᵐ ω ∂(twoCloudLaw q r),
      cloudValueNat (truncatedEdgeCost q (r : ℝ) g t) (sourceCount) (targetCount) ω =
        poissonCubeTilted q (r : ℝ) g t ω := by
  filter_upwards [ae_points_mem_unitCube_twoCloudLaw q r] with ω hω
  unfold cloudValueNat poissonCubeTilted tiltedCloudValue truncatedEdgeCost
    poissonCubeCost poissonCubeProbe
  congr 1
  funext i j
  have hx : cubeTruncPoint (sourcePoint ω (i : ℕ)) = sourcePoint ω (i : ℕ) :=
    cubeTruncPoint_eq_of_mem (hω.1 i)
  have hy : cubeTruncPoint (targetPoint ω (j : ℕ)) = targetPoint ω (j : ℕ) :=
    cubeTruncPoint_eq_of_mem (hω.2 j)
  rw [hx, hy, sqDistClamped_eq_sqDist (hω.1 i) (hω.2 j)]

/-- The law of the pair of the two Poisson counts. -/
theorem map_counts_twoCloudLaw (q : ℕ) (r : ℝ≥0) :
    (twoCloudLaw q r).map (fun ω : TwoCloudSpace q => (sourceCount ω, targetCount ω)) =
      (poissonMeasure r).prod (poissonMeasure r) := by
  have hfun : (fun ω : TwoCloudSpace q => (sourceCount ω, targetCount ω)) =
      Prod.map (fun z : PoissonCloudSpace q => z.1) (fun z : PoissonCloudSpace q => z.1) := rfl
  rw [hfun, twoCloudLaw, ← Measure.map_prod_map _ _ measurable_fst measurable_fst]
  rw [poissonCubeLaw, Measure.map_fst_prod, measure_univ, one_smul]

/-- The measured map to the pair of counts is measurable. -/
theorem measurable_counts_pair (q : ℕ) :
    Measurable fun ω : TwoCloudSpace q => (sourceCount ω, targetCount ω) :=
  (measurable_sourceCount q).prodMk (measurable_targetCount q)

/-- Expected absolute difference of the two Poisson counts. -/
theorem integral_abs_counts_sub_le (q : ℕ) (r : ℝ≥0) :
    ∫ ω, |(sourceCount ω : ℝ) - (targetCount ω : ℝ)| ∂(twoCloudLaw q r) ≤
      Real.sqrt (2 * (r : ℝ)) := by
  have hmap := map_counts_twoCloudLaw q r
  have hmeas : Measurable (fun ω : TwoCloudSpace q => (sourceCount ω, targetCount ω)) :=
    measurable_counts_pair q
  have hcont : Continuous (fun z : ℕ × ℕ => |(z.1 : ℝ) - (z.2 : ℝ)|) := by
    continuity
  rw [← integral_map hmeas.aemeasurable hcont.aestronglyMeasurable]
  rw [hmap]
  exact integral_abs_sub_poissonPair_le r

/-- Integral of the source count. -/
theorem integral_sourceCount (q : ℕ) (r : ℝ≥0) :
    ∫ ω, ((sourceCount ω : ℕ) : ℝ) ∂(twoCloudLaw q r) = (r : ℝ) := by
  have hmap := map_counts_twoCloudLaw q r
  have hmeas : Measurable (fun ω : TwoCloudSpace q => (sourceCount ω, targetCount ω)) :=
    measurable_counts_pair q
  have hcont : Continuous (fun z : ℕ × ℕ => (z.1 : ℝ)) := by continuity
  rw [← integral_map hmeas.aemeasurable hcont.aestronglyMeasurable]
  rw [hmap]
  have hmapf : Measure.map Prod.fst ((poissonMeasure r).prod (poissonMeasure r)) = poissonMeasure r := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  calc ∫ y : ℕ × ℕ, (y.1 : ℝ) ∂((poissonMeasure r).prod (poissonMeasure r))
      = ∫ n : ℕ, (n : ℝ) ∂Measure.map Prod.fst
          ((poissonMeasure r).prod (poissonMeasure r)) := by
        rw [integral_map measurable_fst.aemeasurable measurable_from_nat.aestronglyMeasurable]
    _ = ∫ n : ℕ, (n : ℝ) ∂(poissonMeasure r) := by rw [hmapf]
    _ = (r : ℝ) := integral_id_poissonMeasure r

/-- Integral of the target count. -/
theorem integral_targetCount (q : ℕ) (r : ℝ≥0) :
    ∫ ω, ((targetCount ω : ℕ) : ℝ) ∂(twoCloudLaw q r) = (r : ℝ) := by
  have hmap := map_counts_twoCloudLaw q r
  have hmeas : Measurable (fun ω : TwoCloudSpace q => (sourceCount ω, targetCount ω)) :=
    measurable_counts_pair q
  have hcont : Continuous (fun z : ℕ × ℕ => (z.2 : ℝ)) := by continuity
  rw [← integral_map hmeas.aemeasurable hcont.aestronglyMeasurable]
  rw [hmap]
  have hmapf : Measure.map Prod.snd ((poissonMeasure r).prod (poissonMeasure r)) = poissonMeasure r := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  calc ∫ y : ℕ × ℕ, (y.2 : ℝ) ∂((poissonMeasure r).prod (poissonMeasure r))
      = ∫ n : ℕ, (n : ℝ) ∂Measure.map Prod.snd
          ((poissonMeasure r).prod (poissonMeasure r)) := by
        rw [integral_map measurable_snd.aemeasurable measurable_from_nat.aestronglyMeasurable]
    _ = ∫ n : ℕ, (n : ℝ) ∂(poissonMeasure r) := by rw [hmapf]
    _ = (r : ℝ) := integral_id_poissonMeasure r

/-- The target Poisson count is integrable. -/
theorem integrable_targetCount (q : ℕ) (r : ℝ≥0) :
    Integrable (fun ω : TwoCloudSpace q => ((targetCount ω : ℕ) : ℝ)) (twoCloudLaw q r) := by
  have h1 : Integrable (fun z : PoissonCloudSpace q => (z.1 : ℝ)) (poissonCubeLaw q r) := by
    unfold poissonCubeLaw
    exact (integrable_id_poissonMeasure r).comp_fst _
  have hne : poissonCubeLaw q r ≠ 0 := by
    intro h0
    have h1' : poissonCubeLaw q r Set.univ = 1 := measure_univ
    rw [h0] at h1'
    simp at h1'
  unfold twoCloudLaw targetCount
  exact (Integrable.comp_snd_iff (μ := poissonCubeLaw q r) hne).mpr h1

/-- Expected maximum of the two Poisson counts is at most twice the rate. -/
theorem integral_max_counts_le (q : ℕ) (r : ℝ≥0) :
    ∫ ω, ((max (sourceCount ω) (targetCount ω) : ℕ) : ℝ) ∂(twoCloudLaw q r) ≤
      2 * (r : ℝ) := by
  have hN : Integrable (fun ω : TwoCloudSpace q => ((sourceCount ω : ℕ) : ℝ))
      (twoCloudLaw q r) := integrable_sourceCount q r
  have hM : Integrable (fun ω : TwoCloudSpace q => ((targetCount ω : ℕ) : ℝ))
      (twoCloudLaw q r) := integrable_targetCount q r
  have hmax : Measurable fun ω : TwoCloudSpace q =>
      ((max (sourceCount ω) (targetCount ω) : ℕ) : ℝ) :=
    Measurable.comp measurable_from_nat
      ((measurable_sourceCount q).max (measurable_targetCount q))
  have hle : ∀ ω : TwoCloudSpace q,
      ((max (sourceCount ω) (targetCount ω) : ℕ) : ℝ) ≤
        ((sourceCount ω : ℕ) : ℝ) + ((targetCount ω : ℕ) : ℝ) := by
    intro ω
    have h : max (sourceCount ω) (targetCount ω) ≤ sourceCount ω + targetCount ω :=
      max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    exact_mod_cast h
  have hIntmax : Integrable (fun ω : TwoCloudSpace q =>
      ((max (sourceCount ω) (targetCount ω) : ℕ) : ℝ)) (twoCloudLaw q r) := by
    refine Integrable.mono' (hN.add hM) hmax.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hle ω
  calc ∫ ω, ((max (sourceCount ω) (targetCount ω) : ℕ) : ℝ) ∂(twoCloudLaw q r)
      ≤ ∫ ω, (((sourceCount ω : ℕ) : ℝ) + ((targetCount ω : ℕ) : ℝ))
          ∂(twoCloudLaw q r) := integral_mono hIntmax (hN.add hM) hle
    _ = (∫ ω, ((sourceCount ω : ℕ) : ℝ) ∂(twoCloudLaw q r)) +
          ∫ ω, ((targetCount ω : ℕ) : ℝ) ∂(twoCloudLaw q r) := integral_add hN hM
    _ = (r : ℝ) + (r : ℝ) := by rw [integral_sourceCount, integral_targetCount]
    _ = 2 * (r : ℝ) := by ring

/-- Integrability of the shifted truncated cloud value. -/
theorem integrable_shiftedValue (q : ℕ) (r : ℝ≥0) {G : ℝ} (hG0 : 0 ≤ G)
    {g : (Fin q → ℝ) → (Fin q → ℝ) → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ G) (t : ℝ) :
    Integrable (fun ω : TwoCloudSpace q =>
      cloudValueNat (fun ω i j => truncatedEdgeCost q (r : ℝ) g t ω i j + |t| * G)
        (sourceCount) (targetCount) ω) (twoCloudLaw q r) := by
  have hbase := integrable_poissonCubeTilted q r hG0 hg hgb t
  have hmin := integrable_min_counts q r
  have hae : (fun ω : TwoCloudSpace q =>
        cloudValueNat (fun ω i j => truncatedEdgeCost q (r : ℝ) g t ω i j + |t| * G)
          (sourceCount) (targetCount) ω) =ᵐ[twoCloudLaw q r]
      fun ω => poissonCubeTilted q (r : ℝ) g t ω +
        ((min (sourceCount ω) (targetCount ω) : ℕ) : ℝ) * (|t| * G) := by
    filter_upwards [cloudValueNat_truncated_eq_tilted_ae q r g t] with ω h1
    rw [cloudValueNat_shifted_eq, h1]
  exact (hbase.add (hmin.mul_const _)).congr hae.symm

/-- Integrability of the maximum of the two Poisson counts. -/
theorem integrable_max_counts (q : ℕ) (r : ℝ≥0) :
    Integrable (fun ω : TwoCloudSpace q =>
      ((max (sourceCount ω) (targetCount ω) : ℕ) : ℝ)) (twoCloudLaw q r) := by
  have hN : Integrable (fun ω : TwoCloudSpace q => ((sourceCount ω : ℕ) : ℝ))
      (twoCloudLaw q r) := integrable_sourceCount q r
  have hM : Integrable (fun ω : TwoCloudSpace q => ((targetCount ω : ℕ) : ℝ))
      (twoCloudLaw q r) := integrable_targetCount q r
  have hmax : Measurable fun ω : TwoCloudSpace q =>
      ((max (sourceCount ω) (targetCount ω) : ℕ) : ℝ) :=
    Measurable.comp measurable_from_nat
      ((measurable_sourceCount q).max (measurable_targetCount q))
  refine Integrable.mono' (hN.add hM) hmax.aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h : max (sourceCount ω) (targetCount ω) ≤ sourceCount ω + targetCount ω :=
    max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  calc ((max (sourceCount ω) (targetCount ω) : ℕ) : ℝ)
      ≤ ((sourceCount ω + targetCount ω : ℕ) : ℝ) := by exact_mod_cast h
    _ = (sourceCount ω : ℝ) + (targetCount ω : ℝ) := by push_cast; ring

/-- Integrability of the absolute count difference. -/
theorem integrable_abs_counts_sub (q : ℕ) (r : ℝ≥0) :
    Integrable (fun ω : TwoCloudSpace q =>
      |(sourceCount ω : ℝ) - (targetCount ω : ℝ)|) (twoCloudLaw q r) := by
  have hN : Integrable (fun ω : TwoCloudSpace q => ((sourceCount ω : ℕ) : ℝ))
      (twoCloudLaw q r) := integrable_sourceCount q r
  have hM : Integrable (fun ω : TwoCloudSpace q => ((targetCount ω : ℕ) : ℝ))
      (twoCloudLaw q r) := integrable_targetCount q r
  have hmeas : Measurable fun ω : TwoCloudSpace q =>
      |(sourceCount ω : ℝ) - (targetCount ω : ℝ)| :=
    continuous_abs.measurable.comp
      ((Measurable.comp measurable_from_nat (measurable_sourceCount q)).sub
        (Measurable.comp measurable_from_nat (measurable_targetCount q)))
  refine Integrable.mono' (hN.add hM) hmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_abs]
  have h1 : (0 : ℝ) ≤ (sourceCount ω : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (targetCount ω : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  simp only [Pi.add_apply]
  constructor <;> linarith

set_option maxHeartbeats 0 in
/-- Integrated dyadic upper bound for the shifted truncated cloud value, given
the per-level discrepancy bounds. -/
theorem integral_shiftedValue_le_hier (q : ℕ) (r : ℝ≥0) {G : ℝ} (hG0 : 0 ≤ G)
    {g : (Fin q → ℝ) → (Fin q → ℝ) → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ G) (t : ℝ) {K : ℕ} (hK : 0 < K)
    (D : Fin K → ℝ)
    (hDint : ∀ k : Fin K, Integrable (fun ω : TwoCloudSpace q =>
      ∑ c : Fin q → Fin (2 ^ (k : ℕ)),
        |(partitionCount ((dyadicCell q (k : ℕ)) ∘
            (fun i : Fin (sourceCount ω) => cubeTruncPoint (sourcePoint ω (i : ℕ)))) c : ℝ) -
          (partitionCount ((dyadicCell q (k : ℕ)) ∘
            (fun j : Fin (targetCount ω) => cubeTruncPoint (targetPoint ω (j : ℕ)))) c : ℝ)|)
      (twoCloudLaw q r))
    (hDbound : ∀ k : Fin K,
      MeasureTheory.integral (twoCloudLaw q r) (fun ω : TwoCloudSpace q =>
        ∑ c : Fin q → Fin (2 ^ (k : ℕ)),
          |(partitionCount ((dyadicCell q (k : ℕ)) ∘
              (fun i : Fin (sourceCount ω) => cubeTruncPoint (sourcePoint ω (i : ℕ)))) c : ℝ) -
            (partitionCount ((dyadicCell q (k : ℕ)) ∘
              (fun j : Fin (targetCount ω) => cubeTruncPoint (targetPoint ω (j : ℕ)))) c : ℝ)|)
        ≤ D k) :
    ∫ ω, cloudValueNat (fun ω i j => truncatedEdgeCost q (r : ℝ) g t ω i j + |t| * G)
        (sourceCount) (targetCount) ω ∂(twoCloudLaw q r)
      ≤ (r ^ (2 / (q : ℝ)) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) + 2 * (|t| * G)) *
          (2 * (r : ℝ)) +
        (1 / 2 : ℝ) * ∑ k : Fin K,
          (r ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ))) *
            (D k + Real.sqrt (2 * (r : ℝ))) := by
  classical
  let cell : (k : Fin K) → (Fin q → ℝ) → (Fin q → Fin (2 ^ (k : ℕ))) :=
    fun k => dyadicCell q (k : ℕ)
  have hnested : ∀ (k l : Fin K), k ≤ l → ∀ x y : Fin q → ℝ,
      cell l x = cell l y → cell k x = cell k y := by
    intro k l hkl x y h
    exact dyadicCell_nested_global hkl h
  let base : ℝ := r ^ (2 / (q : ℝ)) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) + 2 * (|t| * G)
  let weight : Fin K → ℝ := fun k => r ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ))
  have hbase0 : 0 ≤ base := by
    have hrpow : 0 ≤ r ^ (2 / (q : ℝ)) := Real.rpow_nonneg r.coe_nonneg _
    have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    have h1 : 0 ≤ r ^ (2 / (q : ℝ)) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) := by positivity
    have h2 : 0 ≤ 2 * (|t| * G) := by positivity
    dsimp [base]; linarith
  have hweight0 : ∀ k, 0 ≤ weight k := by
    intro k
    have hrpow : 0 ≤ r ^ (2 / (q : ℝ)) := Real.rpow_nonneg r.coe_nonneg _
    have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    dsimp [weight]
    positivity
  have hcost : ∀ ω : TwoCloudSpace q, ∀ i : Fin (sourceCount ω), ∀ j : Fin (targetCount ω),
      truncatedEdgeCost q (r : ℝ) g t ω (i : ℕ) (j : ℕ) + |t| * G ≤
        base + ∑ k : Fin K, weight k *
          partitionDistance (cell k (cubeTruncPoint (sourcePoint ω (i : ℕ))))
            (cell k (cubeTruncPoint (targetPoint ω (j : ℕ)))) := by
    intro ω i j
    exact shiftedEdgeCost_le_hier q (r := (r : ℝ)) (t := t) r.coe_nonneg hG0 hgb hK
      ω (i : ℕ) (j : ℕ)
  have hnonneg : ∀ ω : TwoCloudSpace q, ∀ i : Fin (sourceCount ω), ∀ j : Fin (targetCount ω),
      0 ≤ truncatedEdgeCost q (r : ℝ) g t ω (i : ℕ) (j : ℕ) + |t| * G := by
    intro ω i j
    exact shiftedEdgeCost_nonneg q r.coe_nonneg hG0 hgb ω (i : ℕ) (j : ℕ)
  have hV : Integrable (fun ω : TwoCloudSpace q =>
      PartialMatching.maxCardValue (fun i : Fin (sourceCount ω) => fun j : Fin (targetCount ω) =>
        truncatedEdgeCost q (r : ℝ) g t ω (i : ℕ) (j : ℕ) + |t| * G)) (twoCloudLaw q r) := by
    simpa only [cloudValueNat] using integrable_shiftedValue q r hG0 hg hgb t
  have hmax := integrable_max_counts q r
  have hdiff := integrable_abs_counts_sub q r
  have hmain := integral_maxCardValue_le_of_counts (P := twoCloudLaw q r) (cell := cell) hnested
    (base := base) hbase0 (weight := weight) hweight0
    (N := sourceCount) (M := targetCount)
    (x := fun ω (i : Fin (sourceCount ω)) => cubeTruncPoint (sourcePoint ω (i : ℕ)))
    (y := fun ω (j : Fin (targetCount ω)) => cubeTruncPoint (targetPoint ω (j : ℕ)))
    (cost := fun ω (i : Fin (sourceCount ω)) (j : Fin (targetCount ω)) =>
      truncatedEdgeCost q (r : ℝ) g t ω (i : ℕ) (j : ℕ) + |t| * G)
    hcost hnonneg hV hmax hDint hdiff (2 * (r : ℝ)) (integral_max_counts_le q r) D hDbound
    (Real.sqrt (2 * (r : ℝ))) (integral_abs_counts_sub_le q r)
  simpa only [cloudValueNat, base, weight] using hmain

end OTSelector.Probability
