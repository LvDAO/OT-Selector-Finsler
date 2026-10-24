import OTSelector.Probability.MarkedPressureBlockSubadditivity
import OTSelector.Analysis.Convex.SubadditiveLimit

/-!
# Poissonized marked pressure limit

The block-subadditivity engine applied to the scale-normalized marked pressure
`R ↦ P(R^q) / R^q` with the repair error
`gridRepairError q (gridRepairConstant q) C G t L`.  The pressure comparison of
`MarkedPressureBlockSubadditivity` supplies the block inequality at every
intensity, and `exists_gridLevel` chooses the hierarchy depth for each block
count.  The output is a concave, `G`-Lipschitz limit function of the tilt.
-/

open scoped BigOperators NNReal
open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace OTSelector.Probability

/-- **Poissonized marked pressure limit.**  For `q > 4`, the scale-normalized
marked pressure of two independent marked Poisson clouds with bounded,
quadratically homogeneous kinetic kernel and bounded probe converges as the
scale tends to infinity, to a concave `G`-Lipschitz function of the tilt. -/
theorem exists_markedScalePressure_limit
    (q : ℕ) (hq : 4 < q)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    {C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) :
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun R => markedScalePressure q A B α β kin g R t)
        atTop (𝓝 (p t))) ∧
      ConcaveOn ℝ Set.univ p ∧ LipschitzWith ⟨G, hG0⟩ p := by
  classical
  refine OTSelector.exists_tendsto_of_block_subadditive_of_tiltError
    (f := fun R t => markedScalePressure q A B α β kin g R t) hG0 ?_ ?_ ?_ ?_
    (fun t L => gridRepairError q (gridRepairConstant q) C G t L) ?_ ?_ ?_
  · exact exists_markedScalePressure_bound q hq α β hC0 hG0
      hkin hkin_nonneg hkin_bound hg hgb
  · intro R
    exact markedScalePressure_concaveOn q α β hC0 hG0 hkin hkin_bound hg hgb R
  · intro R t u
    exact markedScalePressure_lipschitz q α β hC0 hG0 hkin hkin_bound hg hgb R t u
  · intro t L hL
    exact continuousAt_markedScalePressure q α β hC0 hG0 hkin hkin_bound hg hgb hL
  · intro t L hL
    exact continuousAt_gridRepairError q (gridRepairConstant q) C G t hL
  · intro t
    exact tendsto_gridRepairError_atTop hq (gridRepairConstant q) C G t
  · intro t L hL δ hδ
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hm0 : 0 < m := hm
    haveI : NeZero m := ⟨hm0.ne'⟩
    obtain ⟨J, hJ, hJ2⟩ := exists_gridLevel m hm0
    have hpressure : ∀ R : ℝ≥0,
        markedPressure q A B α β R kin g t ≤
          (((m ^ q : ℕ) : ℝ)) *
              markedPressure q A B α β (R / ((m ^ q : ℕ) : ℝ≥0)) kin g t +
            gridRepairConstant q * (C + |t| * G) * (R : ℝ) *
              (Real.rpow ((R : ℝ) / ((m : ℝ) ^ q)) (2 / (q : ℝ) - 1 / 2) +
                Real.rpow ((R : ℝ) / ((m : ℝ) ^ q)) (-(1 / 2))) :=
      fun R => markedPressure_le_blockScale_add_repair q m J hq hm0 hJ hJ2
        α β R hC0 hG0 hkin hkin_nonneg hkin_bound hkin_homog hg hgb
    have := markedScalePressure_block_le (q := q) (m := m) (J := J) hq hm0 hJ hJ2
      (α := α) (β := β) hpressure hL
    linarith



/-! ## Transfer to the intensity variable -/

/-- The Poissonized pressure divided by the intensity inherits the scale limit,
along the intensity variable itself. -/
theorem tendsto_markedPressure_div
    (q : ℕ) (hq : 0 < q)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun R => markedScalePressure q A B α β kin g R t)
      atTop (𝓝 (p t))) :
    ∀ t, Tendsto (fun r : ℝ =>
      markedPressure q A B α β (Real.toNNReal r) kin g t / r) atTop (𝓝 (p t)) := by
  intro t
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hpow : Tendsto (fun r : ℝ => r ^ (1 / (q : ℝ))) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have hcomp := (hp t).comp hpow
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  change markedScalePressure q A B α β kin g (r ^ (1 / (q : ℝ))) t =
    markedPressure q A B α β (Real.toNNReal r) kin g t / r
  rw [markedScalePressure_of_pos q α β (Real.rpow_pos_of_pos hr _)]
  have hpowq : (r ^ (1 / (q : ℝ))) ^ q = r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    have hq1 : (1 / (q : ℝ)) * (q : ℝ) = 1 := by field_simp
    rw [hq1, Real.rpow_one]
  rw [hpowq]

end OTSelector.Probability
