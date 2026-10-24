import OTSelector.Probability.MarkedTileExpectation
import OTSelector.Probability.MarkedTilePressureLimit
import OTSelector.Probability.TileRepairErrorLimit
import OTSelector.Probability.MarkedMixtureThinning
import OTSelector.Topology.Order.FiniteSumLimit

/-!
# The finite-tile pressure upper bound

For a finite family of tiles with weights `w`, the encoded tile model in the
marked cube has global pressure bounded by the weighted sum of the local tile
pressures.  This module proves the fixed-intensity inequality

`P_global(r) ≤ Σ c P_local,c(r * w c) + B(r) * (1/2) * sqrt (2 r card C)`

by integrating the deterministic tile repair, and then passes to the pressure
limit at scale `R ^ q`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {C A B : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
  [MeasurableSpace C] [MeasurableSingletonClass C] [MeasurableSpace A] [MeasurableSpace B]

/-- Measurability of the encoded pair of label clouds. -/
theorem measurable_cloudEncode_labelCloud_pair (c : C) :
    Measurable (fun ω : TwoMarkedCloudSpace q (C × A) (C × B) =>
      (cloudEncode (labelCloud c ω.1), cloudEncode (labelCloud c ω.2))) :=
  ((measurable_cloudEncode_labelCloud (q := q) (A := A) c).comp measurable_fst).prodMk
    ((measurable_cloudEncode_labelCloud (q := q) (A := B) c).comp measurable_snd)

/-- **Fixed-intensity finite-tile upper bound.** -/
theorem markedPressure_tile_le_sum
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
    (r : ℝ≥0) (t : ℝ) :
    markedPressure q (C × A) (C × B) (mixtureMarkLaw w α) (mixtureMarkLaw w β) r
        (tileKin q w kin Kcross) (tileProbe g) t ≤
      (∑ c : C, markedPressure q A B (α c) (β c) (r * w c) (kin c) (g c) t) +
        ((r : ℝ) ^ (2 / (q : ℝ)) * (max Cb Kcross * (q : ℝ)) + |t| * G) *
          (1 / 2 * Real.sqrt (2 * (r : ℝ) * (Fintype.card C : ℝ))) := by
  classical
  haveI hprobα : IsProbabilityMeasure (mixtureMarkLaw w α) :=
    mixtureMarkLaw_isProbability w α hw
  haveI hprobβ : IsProbabilityMeasure (mixtureMarkLaw w β) :=
    mixtureMarkLaw_isProbability w β hw
  have hq0 : 0 < q := by omega
  have hwle : ∀ c, w c ≤ 1 := by
    intro c
    have h := Finset.single_le_sum (s := Finset.univ) (f := w)
      (fun i _ => by positivity) (Finset.mem_univ c)
    simpa [hw] using h
  have hwmeas : Measurable w := measurable_of_countable w
  let Gd : Measure (TwoMarkedCloudSpace q (C × A) (C × B)) :=
    twoMarkedCloudLaw q (C × A) (C × B) (mixtureMarkLaw w α) (mixtureMarkLaw w β) r
  let Bnd : ℝ := (r : ℝ) ^ (2 / (q : ℝ)) * (max Cb Kcross * (q : ℝ)) + |t| * G
  have hB0 : 0 ≤ Bnd := by
    have h1 : 0 ≤ r ^ (2 / (q : ℝ)) * (max Cb Kcross * (q : ℝ)) := by positivity
    have h2 : 0 ≤ |t| * G := by positivity
    linarith
  -- Integrability of the global tilted value.
  have hIntTilt : Integrable
      (fun ω => markedTilted q (r : ℝ) (tileKin q w kin Kcross) (tileProbe g) t ω) Gd := by
    have hCmax : 0 ≤ max Cb Kcross := le_trans hCb0 (le_max_left _ _)
    have h := integrable_markedTilted (q := q) (A := C × A) (B := C × B)
      (α := mixtureMarkLaw w α) (β := mixtureMarkLaw w β) r
      (C := max Cb Kcross) (G := G) r.coe_nonneg hCmax hG0
      (kin := tileKin q w kin Kcross) (g := tileProbe g)
      (measurable_tileKin hwmeas hkin_meas)
      (abs_tileKin_le (q := q) (w := w) (kin := kin) (Kcross := Kcross)
        (Cb := Cb) hq0 hwle hkin_bound hCb0 hK0)
      (measurable_tileProbe hg_meas) (abs_tileProbe_le hG0 hgb) t
    simpa only [Gd] using h
  -- Integrability of the discrepancy.
  have hIntDisc : Integrable (tileLabelDiscrepancy (q := q) (C := C) (A := A) (B := B)) Gd := by
    simpa only [Gd, twoMarkedCloudLaw] using
      integrable_tileLabelDiscrepancy (q := q) (C := C) (A := A) (B := B)
        (mixtureMarkLaw w α) (mixtureMarkLaw w β) r
  -- The encoded thinning law, with the intensity coercions aligned.
  have hlawOf (c : C) :
      (twoMarkedCloudLaw q (C × A) (C × B) (mixtureMarkLaw w α) (mixtureMarkLaw w β)
        (Real.toNNReal (r : ℝ))).map
        (fun ω : TwoMarkedCloudSpace q (C × A) (C × B) =>
          (cloudEncode (labelCloud c ω.1), cloudEncode (labelCloud c ω.2))) =
      (twoMarkedCloudLaw q A B (α c) (β c)
        (Real.toNNReal ((r : ℝ) * (w c : ℝ)))).map
        (fun y : TwoMarkedCloudSpace q A B =>
          (cloudEncode (q := q) (A := A) y.1, cloudEncode (q := q) (A := B) y.2)) := by
    have hcoeR : Real.toNNReal (r : ℝ) = r := Real.toNNReal_coe
    have hcoeW : Real.toNNReal ((r : ℝ) * (w c : ℝ)) = r * w c := by
      rw [Real.toNNReal_mul (by positivity), Real.toNNReal_coe, Real.toNNReal_coe]
    simpa only [hcoeR, hcoeW] using
      map_labelCloudEncode_twoMarkedCloudLaw (q := q) (C := C) (A := A) (B := B)
        w hw α β r c
  -- Integrability of each tile block value.
  have hIntTile : ∀ c, Integrable
      (fun ω => tileBlockValue (q := q) w kin g Kcross (r : ℝ) t ω c) Gd := by
    intro c
    haveI : IsProbabilityMeasure (α c) := inferInstance
    haveI : IsProbabilityMeasure (β c) := inferInstance
    haveI : Nonempty A := nonempty_of_isProbabilityMeasure (α c)
    haveI : Nonempty B := nonempty_of_isProbabilityMeasure (β c)
    have hlocal : Integrable
        (fun y : TwoMarkedCloudSpace q A B =>
          markedTilted q ((r : ℝ) * (w c : ℝ)) (kin c) (g c) t y)
        (twoMarkedCloudLaw q A B (α c) (β c) (Real.toNNReal ((r : ℝ) * (w c : ℝ)))) := by
      have h := integrable_markedTilted (q := q) (A := A) (B := B)
        (α := α c) (β := β c) (r * w c) (C := Cb) (G := G)
        (r * w c).coe_nonneg hCb0 hG0 (kin := kin c) (g := g c)
        (hkin_meas.comp (by fun_prop : Measurable
          (fun p : (A × B) × (Fin q → ℝ) => (c, p.1.1, p.1.2, p.2))))
        (hkin_bound c) (hg_meas.comp (by fun_prop : Measurable
          (fun p : A × B => (c, p.1, p.2)))) (hgb c) t
      have hcoe2 : Real.toNNReal ((r : ℝ) * (w c : ℝ)) = r * w c := by
        rw [Real.toNNReal_mul (by positivity), Real.toNNReal_coe, Real.toNNReal_coe]
      simpa only [NNReal.coe_mul, hcoe2] using h
    have h := integrable_tileBlockValue_of_law (q := q) (hq := hq0)
      (w := w) (kin := kin) (g := g) (Kcross := Kcross) (r := (r : ℝ)) (t := t)
      (Cb := Cb) (G0 := G) r.coe_nonneg hkin_homog
      (mixtureMarkLaw w α) (mixtureMarkLaw w β)
      (αc := α c) (βc := β c) (c := c) hCb0 hG0
      (hkin_meas.comp (by fun_prop : Measurable
        (fun p : (A × B) × (Fin q → ℝ) => (c, p.1.1, p.1.2, p.2))))
      (hkin_bound c)
      (hg_meas.comp (by fun_prop : Measurable (fun p : A × B => (c, p.1, p.2))))
      (hgb c)
      (measurable_cloudEncode_labelCloud_pair (q := q) (C := C) (A := A) (B := B) c).aemeasurable
      (hlawOf c)
      hlocal
    simpa only [Gd, Real.toNNReal_coe] using h
  -- The deterministic comparison, integrated.
  have hIntTile' : ∀ c, Integrable
      (fun ω => tileBlockValue (q := q) w kin g Kcross (r : ℝ) t ω c)
      (twoMarkedCloudLaw q (C × A) (C × B) (mixtureMarkLaw w α) (mixtureMarkLaw w β)
        (Real.toNNReal (r : ℝ))) :=
    fun c => by simpa only [Real.toNNReal_coe] using hIntTile c
  have hIntDisc' : Integrable
      (tileLabelDiscrepancy (q := q) (C := C) (A := A) (B := B))
      (twoMarkedCloudLaw q (C × A) (C × B) (mixtureMarkLaw w α) (mixtureMarkLaw w β)
        (Real.toNNReal (r : ℝ))) := by
    simpa only [Real.toNNReal_coe] using hIntDisc
  have hIntTilt' : Integrable
      (fun ω => markedTilted q (r : ℝ) (tileKin q w kin Kcross) (tileProbe g) t ω)
      (twoMarkedCloudLaw q (C × A) (C × B) (mixtureMarkLaw w α) (mixtureMarkLaw w β)
        (Real.toNNReal (r : ℝ))) := by
    simpa only [Real.toNNReal_coe] using hIntTilt
  have hmain := markedPressure_le_sum_tile_add_discrepancy (q := q) (hq := hq0)
    (w := w) (kin := kin) (g := g) (Kcross := Kcross) (Cb := Cb) (G := G)
    (t := t) (r := (r : ℝ)) r.coe_nonneg hCb0 hG0 hK0 hwle
    (hkin_bound := hkin_bound) (hgb := hgb)
    (mixtureMarkLaw w α) (mixtureMarkLaw w β) hIntTile' hIntDisc' hIntTilt'
  simp only [Real.toNNReal_coe] at hmain
  -- Rewrite each tile integral as a local pressure.
  have htile (c : C) :
      ∫ ω, tileBlockValue (q := q) w kin g Kcross (r : ℝ) t ω c
        ∂(twoMarkedCloudLaw q (C × A) (C × B) (mixtureMarkLaw w α) (mixtureMarkLaw w β) r) =
        markedPressure q A B (α c) (β c) (r * w c) (kin c) (g c) t := by
    haveI : IsProbabilityMeasure (α c) := inferInstance
    haveI : IsProbabilityMeasure (β c) := inferInstance
    haveI : Nonempty A := nonempty_of_isProbabilityMeasure (α c)
    haveI : Nonempty B := nonempty_of_isProbabilityMeasure (β c)
    have hlocal : Integrable
        (fun y : TwoMarkedCloudSpace q A B =>
          markedTilted q ((r : ℝ) * (w c : ℝ)) (kin c) (g c) t y)
        (twoMarkedCloudLaw q A B (α c) (β c) (Real.toNNReal ((r : ℝ) * (w c : ℝ)))) := by
      have h := integrable_markedTilted (q := q) (A := A) (B := B)
        (α := α c) (β := β c) (r * w c) (C := Cb) (G := G)
        (r * w c).coe_nonneg hCb0 hG0 (kin := kin c) (g := g c)
        (hkin_meas.comp (by fun_prop : Measurable
          (fun p : (A × B) × (Fin q → ℝ) => (c, p.1.1, p.1.2, p.2))))
        (hkin_bound c) (hg_meas.comp (by fun_prop : Measurable
          (fun p : A × B => (c, p.1, p.2)))) (hgb c) t
      have hcoe2 : Real.toNNReal ((r : ℝ) * (w c : ℝ)) = r * w c := by
        rw [Real.toNNReal_mul (by positivity), Real.toNNReal_coe, Real.toNNReal_coe]
      simpa only [NNReal.coe_mul, hcoe2] using h
    have h := integral_tileBlockValue_eq (q := q) (hq := hq0)
      (w := w) (kin := kin) (g := g) (Kcross := Kcross) (r := (r : ℝ)) (t := t)
      (Cb := Cb) (G0 := G) r.coe_nonneg hkin_homog
      (mixtureMarkLaw w α) (mixtureMarkLaw w β)
      (αc := α c) (βc := β c) (c := c) hCb0 hG0
      (hkin_meas.comp (by fun_prop : Measurable
        (fun p : (A × B) × (Fin q → ℝ) => (c, p.1.1, p.1.2, p.2))))
      (hkin_bound c)
      (hg_meas.comp (by fun_prop : Measurable (fun p : A × B => (c, p.1, p.2))))
      (hgb c)
      (measurable_cloudEncode_labelCloud_pair (q := q) (C := C) (A := A) (B := B) c).aemeasurable
      (hlawOf c)
      hlocal
    have hcoe : Real.toNNReal ((r : ℝ) * (w c : ℝ)) = r * w c := by
      rw [Real.toNNReal_mul (by positivity), Real.toNNReal_coe, Real.toNNReal_coe]
    simpa only [hcoe, Real.toNNReal_coe] using h
  -- The discrepancy bound.
  have hdisc :
      ∫ ω, tileLabelDiscrepancy (q := q) (C := C) (A := A) (B := B) ω
        ∂(twoMarkedCloudLaw q (C × A) (C × B) (mixtureMarkLaw w α) (mixtureMarkLaw w β) r) ≤
        Real.sqrt (2 * (r : ℝ) * (Fintype.card C : ℝ)) := by
    have hlabelα : (mixtureMarkLaw w α).map Prod.fst =
        Measure.sum (fun c => (w c : ℝ≥0∞) • Measure.dirac c) := by
      rw [mixtureMarkLaw_fst, Measure.sum_fintype]
    have hlabelβ : (mixtureMarkLaw w β).map Prod.fst =
        Measure.sum (fun c => (w c : ℝ≥0∞) • Measure.dirac c) := by
      rw [mixtureMarkLaw_fst, Measure.sum_fintype]
    have h := integral_markLabelDiscrepancy_le (q := q) (C := C) (A := A) (B := B)
      (mixtureMarkLaw w α) (mixtureMarkLaw w β) r w hw hlabelα hlabelβ
    have hmeas_eq : (markedPoissonLaw q (C × A) (mixtureMarkLaw w α) r).prod
        (markedPoissonLaw q (C × B) (mixtureMarkLaw w β) r) =
        twoMarkedCloudLaw q (C × A) (C × B) (mixtureMarkLaw w α) (mixtureMarkLaw w β) r := rfl
    rw [hmeas_eq] at h
    exact h
  -- Assemble.
  rw [show markedPressure q (C × A) (C × B) (mixtureMarkLaw w α) (mixtureMarkLaw w β) r
      (tileKin q w kin Kcross) (tileProbe g) t =
      ∫ ω, markedTilted q (r : ℝ) (tileKin q w kin Kcross) (tileProbe g) t ω
        ∂(twoMarkedCloudLaw q (C × A) (C × B) (mixtureMarkLaw w α) (mixtureMarkLaw w β) r)
      from rfl] at hmain
  simp only [htile] at hmain
  have hcorr : Bnd * (1 / 2 *
      ∫ ω, tileLabelDiscrepancy (q := q) (C := C) (A := A) (B := B) ω
        ∂(twoMarkedCloudLaw q (C × A) (C × B) (mixtureMarkLaw w α) (mixtureMarkLaw w β) r)) ≤
      Bnd * (1 / 2 * Real.sqrt (2 * (r : ℝ) * (Fintype.card C : ℝ))) := by
    refine mul_le_mul_of_nonneg_left ?_ hB0
    exact mul_le_mul_of_nonneg_left hdisc (by norm_num)
  exact hmain.trans (add_le_add_right hcorr (∑ c : C,
    markedPressure q A B (α c) (β c) (r * w c) (kin c) (g c) t))

end OTSelector.Probability
