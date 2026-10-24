import OTSelector.Probability.MarkedTilePressureUpperBound
import OTSelector.Probability.MarkedTilePressureLimit
import OTSelector.Probability.TileRepairErrorLimit
import OTSelector.Topology.Order.FiniteSumLimit

/-!
# The finite-tile pressure limit upper bound

Passing the fixed-intensity finite-tile comparison to scale `R ^ q` and letting
`R → ∞` gives the sharp finite-tile upper bound for the pressure limit: the
global pressure is at most the weighted sum of the local tile pressures.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {C A B : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
  [MeasurableSpace C] [MeasurableSingletonClass C] [MeasurableSpace A] [MeasurableSpace B]

/-- **Finite-tile pressure limit.**  For a finite family of tiles with weights
`w`, the limit of the encoded global pressure is at most the weighted sum of the
local pressure limits. -/
theorem exists_markedScalePressure_limit_tile_le_sum
    (q : ℕ) (hq : 4 < q)
    {w : C → ℝ≥0} (hw : ∑ c, w c = 1)
    {kin : C → A → B → (Fin q → ℝ) → ℝ} {g : C → A → B → ℝ}
    {Cb G Kcross : ℝ} (hCb0 : 0 ≤ Cb) (hG0 : 0 ≤ G) (hK0 : 0 ≤ Kcross)
    (hkin_meas : Measurable (fun p : C × A × B × (Fin q → ℝ) =>
      kin p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hkin_nonneg : ∀ c a b v, 0 ≤ kin c a b v)
    (hkin_bound : ∀ c a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hkin_homog : ∀ c a b (s : ℝ), 0 ≤ s → ∀ v : Fin q → ℝ,
      kin c a b (fun l => s * v l) = s ^ 2 * kin c a b v)
    (hg_meas : Measurable (fun p : C × A × B => g p.1 p.2.1 p.2.2))
    (hgb : ∀ c a b, |g c a b| ≤ G)
    (α : C → Measure A) [∀ c, IsProbabilityMeasure (α c)]
    (β : C → Measure B) [∀ c, IsProbabilityMeasure (β c)]
    [IsProbabilityMeasure (mixtureMarkLaw w α)]
    [IsProbabilityMeasure (mixtureMarkLaw w β)]
    (p : C → ℝ → ℝ)
    (hp : ∀ (c : C) (t : ℝ), Tendsto
      (fun R => markedScalePressure q A B (α c) (β c) (kin c) (g c) R t)
      atTop (𝓝 (p c t))) :
    ∃ pglobal : ℝ → ℝ,
      (∀ t, Tendsto (fun R => markedScalePressure q (C × A) (C × B)
        (mixtureMarkLaw w α) (mixtureMarkLaw w β)
        (tileKin q w kin Kcross) (tileProbe g) R t) atTop (𝓝 (pglobal t))) ∧
      (∀ t, pglobal t ≤ ∑ c : C, (w c : ℝ) * p c t) := by
  classical
  have hq0 : 0 < q := by omega
  have hwmeas : Measurable w := measurable_of_countable w
  have hwle : ∀ c, w c ≤ 1 := by
    intro c
    have h := Finset.single_le_sum (s := Finset.univ) (f := w)
      (fun i _ => by positivity) (Finset.mem_univ c)
    simpa [hw] using h
  obtain ⟨pglobal, hpg, -, -⟩ := exists_tilePressure_limit (q := q) hq
    (w := w) hwmeas hwle (mixtureMarkLaw w α) (mixtureMarkLaw w β)
    hCb0 hG0 hK0 hkin_meas hkin_nonneg hkin_bound hkin_homog hg_meas hgb
  refine ⟨pglobal, hpg, fun t => ?_⟩
  let Bc : C → ℝ → ℝ := fun c R =>
    markedPressure q A B (α c) (β c) (Real.toNNReal (R ^ q) * w c) (kin c) (g c) t / R ^ q
  let err : ℝ → ℝ := fun R =>
    ((((Real.toNNReal (R ^ q) : ℝ≥0) : ℝ) ^ (2 / (q : ℝ)) *
        (max Cb Kcross * (q : ℝ)) + |t| * G) *
      (1 / 2 * Real.sqrt (2 * ((Real.toNNReal (R ^ q) : ℝ≥0) : ℝ) *
        (Fintype.card C : ℝ)))) / R ^ q
  refine OTSelector.limit_le_sum_of_eventually_le
    (A := fun R => markedScalePressure q (C × A) (C × B)
      (mixtureMarkLaw w α) (mixtureMarkLaw w β)
      (tileKin q w kin Kcross) (tileProbe g) R t)
    Bc err (pglobal t) (fun c => (w c : ℝ) * p c t) (hpg t) ?_ ?_ ?_
  · intro c
    exact tendsto_markedPressure_scaled_div' hq0 (α c) (β c) (p c) (hp c) (w c) t
  · -- The error vanishes.
    have h := tendsto_tileRepairError_scale_zero (q := q) hq
      (max Cb Kcross * (q : ℝ)) G t (Fintype.card C) (by positivity)
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hRq : (0 : ℝ) < R ^ q := pow_pos hR q
    have hcoer : ((Real.toNNReal (R ^ q) : ℝ≥0) : ℝ) = R ^ q :=
      Real.coe_toNNReal _ hRq.le
    have hRpow : ((R : ℝ) ^ q) ^ (2 / (q : ℝ)) = R ^ 2 := by
      rw [← Real.rpow_natCast R q]
      rw [← Real.rpow_mul hR.le]
      have hqne : (q : ℝ) ≠ 0 := by positivity
      have hexp : (q : ℝ) * (2 / (q : ℝ)) = 2 := by field_simp
      rw [hexp]
      exact Real.rpow_two R
    simp only [err]
    rw [hcoer, hRpow]
    ring
  · -- The eventual comparison.
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hRq : (0 : ℝ) < R ^ q := pow_pos hR q
    have hmain := markedPressure_tile_le_sum (q := q) (hq := hq)
      (w := w) (hw := hw) (kin := kin) (g := g)
      (Cb := Cb) (G := G) (Kcross := Kcross)
      hCb0 hG0 hK0 hkin_meas hkin_nonneg hkin_bound hkin_homog hg_meas hgb
      α β (Real.toNNReal (R ^ q)) t
    rw [markedScalePressure_of_pos q (mixtureMarkLaw w α) (mixtureMarkLaw w β) hR]
    have hd := div_le_div_of_nonneg_right hmain hRq.le
    rw [add_div, Finset.sum_div] at hd
    exact hd

end OTSelector.Probability
