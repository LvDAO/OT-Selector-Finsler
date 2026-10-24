import OTSelector.Probability.MarkedTileRepair
import OTSelector.Probability.MarkedTileBlockIdentity
import OTSelector.Probability.MarkedTileDiscrepancy
import OTSelector.Probability.MarkedTileDiscrepancyIntegrable
import OTSelector.Probability.MarkedTilePressureLimit
import OTSelector.Probability.MarkedMixtureThinning
import OTSelector.Probability.MarkedMixtureThinning
import OTSelector.Probability.MarkedPoissonCube

/-!
# Integrated finite-tile comparison

This module integrates the deterministic tile decomposition of the marked
tilted value against the marked Poisson cloud law.  The output is the
expected-value comparison

`P_global(r) ≤ Σ c P_local,c(r * w c) + B(r) * (1/2) * E[discrepancy]`,

where the per-tile identities are taken as hypotheses supplied by the Poisson
thinning law of the mixture mark measure.  The discrepancy term is bounded by
`sqrt (2 r card C)` through the two-sample label-count law.

The hypotheses `hlaw` and `hmeas` are the label thinning statement of the
global mark measures, one tile at a time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {C A B : Type*} [Fintype C] [DecidableEq C]
  [MeasurableSpace C] [MeasurableSingletonClass C]
  [MeasurableSpace A] [MeasurableSpace B]

/-- The marked tilted value equals the block tilted value of the encoded block
data. -/
theorem markedTilted_eq_blockTiltedValue_cloudEncode
    (q : ℕ) {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (r t : ℝ)
    (z : MarkedCloudSpace q A) (w : MarkedCloudSpace q B) :
    markedTilted q r kin g t (z, w) =
      blockTiltedValue q r kin g t (cloudEncode z) (cloudEncode w) := rfl

/-- **One-tile integral identity.**  Assuming the encoded label thinning law for
tile `c`, the expected ambient block value of tile `c` is the local marked
pressure at intensity `r * w c`. -/
theorem integral_tileBlockValue_eq
    (q : ℕ) (hq : 0 < q)
    {w : C → ℝ≥0} {kin : C → A → B → (Fin q → ℝ) → ℝ} {g : C → A → B → ℝ}
    {Kcross r t Cb G0 : ℝ} (hr : 0 ≤ r)
    (hkin_homog : ∀ c a b (s : ℝ), 0 ≤ s → ∀ v : Fin q → ℝ,
      kin c a b (fun l => s * v l) = s ^ 2 * kin c a b v)
    (αg : Measure (C × A)) [IsProbabilityMeasure αg]
    (βg : Measure (C × B)) [IsProbabilityMeasure βg]
    [Nonempty A] [Nonempty B]
    (αc : Measure A) [IsProbabilityMeasure αc]
    (βc : Measure B) [IsProbabilityMeasure βc]
    (c : C) (hCb0 : 0 ≤ Cb) (hG0 : 0 ≤ G0)
    (hkin_meas : Measurable (Function.uncurry (fun p : A × B => kin c p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hg_meas : Measurable (Function.uncurry (g c)))
    (hgb : ∀ a b, |g c a b| ≤ G0)
    (hmeas : AEMeasurable
      (fun ω : TwoMarkedCloudSpace q (C × A) (C × B) =>
        (cloudEncode (labelCloud c ω.1), cloudEncode (labelCloud c ω.2)))
      (twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r)))
    (hlaw : (twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r)).map
      (fun ω : TwoMarkedCloudSpace q (C × A) (C × B) =>
        (cloudEncode (labelCloud c ω.1), cloudEncode (labelCloud c ω.2))) =
      (twoMarkedCloudLaw q A B αc βc (Real.toNNReal (r * (w c : ℝ)))).map
        (fun y : TwoMarkedCloudSpace q A B =>
          (cloudEncode (q := q) (A := A) y.1, cloudEncode (q := q) (A := B) y.2)))
    (hlocal : Integrable (fun y : TwoMarkedCloudSpace q A B =>
      markedTilted q (r * (w c : ℝ)) (kin c) (g c) t y)
      (twoMarkedCloudLaw q A B αc βc (Real.toNNReal (r * (w c : ℝ))))) :
    ∫ ω, tileBlockValue (q := q) w kin g Kcross r t ω c
        ∂(twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r)) =
      markedPressure q A B αc βc (Real.toNNReal (r * (w c : ℝ)))
        (kin c) (g c) t := by
  have hrwc : (0 : ℝ) ≤ r * (w c : ℝ) := mul_nonneg hr (by positivity)
  have hcoe : ((Real.toNNReal (r * (w c : ℝ))) : ℝ) = r * (w c : ℝ) :=
    Real.coe_toNNReal _ hrwc
  have hBlockMeas : Measurable
      (fun p : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) =>
        blockTiltedValue q (r * (w c : ℝ)) (kin c) (g c) t p.1 p.2) :=
    measurable_blockTiltedValue q (r * (w c : ℝ)) (C := Cb) (G := G0)
      hrwc hCb0 hG0 hkin_meas hkin_bound hg_meas hgb t
  have hencMeas : Measurable (fun y : TwoMarkedCloudSpace q A B =>
      (cloudEncode (q := q) (A := A) y.1, cloudEncode (q := q) (A := B) y.2)) :=
    ((measurable_cloudEncode (q := q) (A := A)).comp measurable_fst).prodMk
      ((measurable_cloudEncode (q := q) (A := B)).comp measurable_snd)
  calc ∫ ω, tileBlockValue (q := q) w kin g Kcross r t ω c
        ∂(twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r))
      = ∫ ω, markedTilted q (r * (w c : ℝ)) (kin c) (g c) t
          (labelCloud c ω.1, labelCloud c ω.2)
          ∂(twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r)) := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        exact tileBlockValue_eq (q := q) (C := C) (A := A) (B := B)
          (w := w) (kin := kin) (g := g) (Kcross := Kcross) (r := r) (t := t)
          hq hr hkin_homog ω c
    _ = ∫ ω, blockTiltedValue q (r * (w c : ℝ)) (kin c) (g c) t
          (cloudEncode (labelCloud c ω.1)) (cloudEncode (labelCloud c ω.2))
          ∂(twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r)) := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        exact markedTilted_eq_blockTiltedValue_cloudEncode (q := q) (kin := kin c)
          (g := g c) (r := r * (w c : ℝ)) (t := t)
          (z := labelCloud c ω.1) (w := labelCloud c ω.2)
    _ = ∫ p, blockTiltedValue q (r * (w c : ℝ)) (kin c) (g c) t p.1 p.2
          ∂((twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r)).map
            (fun ω : TwoMarkedCloudSpace q (C × A) (C × B) =>
              (cloudEncode (labelCloud c ω.1), cloudEncode (labelCloud c ω.2)))) := by
        rw [integral_map hmeas hBlockMeas.aestronglyMeasurable]
    _ = ∫ p, blockTiltedValue q (r * (w c : ℝ)) (kin c) (g c) t p.1 p.2
          ∂((twoMarkedCloudLaw q A B αc βc
            (Real.toNNReal (r * (w c : ℝ)))).map
            (fun y : TwoMarkedCloudSpace q A B =>
              (cloudEncode (q := q) (A := A) y.1, cloudEncode (q := q) (A := B) y.2))) := by
        rw [hlaw]
    _ = ∫ y, blockTiltedValue q (r * (w c : ℝ)) (kin c) (g c) t
          (cloudEncode (q := q) (A := A) y.1) (cloudEncode (q := q) (A := B) y.2)
          ∂(twoMarkedCloudLaw q A B αc βc (Real.toNNReal (r * (w c : ℝ)))) := by
        rw [integral_map hencMeas.aemeasurable hBlockMeas.aestronglyMeasurable]
    _ = ∫ y, markedTilted q (r * (w c : ℝ)) (kin c) (g c) t y
          ∂(twoMarkedCloudLaw q A B αc βc (Real.toNNReal (r * (w c : ℝ)))) := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        exact (markedTilted_eq_blockTiltedValue_cloudEncode (q := q) (kin := kin c)
          (g := g c) (r := r * (w c : ℝ)) (t := t) (z := y.1) (w := y.2)).symm
    _ = markedPressure q A B αc βc (Real.toNNReal (r * (w c : ℝ)))
          (kin c) (g c) t := by
        unfold markedPressure
        rw [hcoe]

/-- **Integrability of one tile block value** from the local integrability and
the encoded thinning law. -/
theorem integrable_tileBlockValue_of_law
    (q : ℕ) (hq : 0 < q)
    {w : C → ℝ≥0} {kin : C → A → B → (Fin q → ℝ) → ℝ} {g : C → A → B → ℝ}
    {Kcross r t Cb G0 : ℝ} (hr : 0 ≤ r)
    (hkin_homog : ∀ c a b (s : ℝ), 0 ≤ s → ∀ v : Fin q → ℝ,
      kin c a b (fun l => s * v l) = s ^ 2 * kin c a b v)
    (αg : Measure (C × A)) [IsProbabilityMeasure αg]
    (βg : Measure (C × B)) [IsProbabilityMeasure βg]
    [Nonempty A] [Nonempty B]
    {αc : Measure A} [IsProbabilityMeasure αc]
    {βc : Measure B} [IsProbabilityMeasure βc]
    (c : C) (hCb0 : 0 ≤ Cb) (hG0 : 0 ≤ G0)
    (hkin_meas : Measurable (Function.uncurry (fun p : A × B => kin c p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hg_meas : Measurable (Function.uncurry (g c)))
    (hgb : ∀ a b, |g c a b| ≤ G0)
    (hmeas : AEMeasurable
      (fun ω : TwoMarkedCloudSpace q (C × A) (C × B) =>
        (cloudEncode (labelCloud c ω.1), cloudEncode (labelCloud c ω.2)))
      (twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r)))
    (hlaw : (twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r)).map
      (fun ω : TwoMarkedCloudSpace q (C × A) (C × B) =>
        (cloudEncode (labelCloud c ω.1), cloudEncode (labelCloud c ω.2))) =
      (twoMarkedCloudLaw q A B αc βc (Real.toNNReal (r * (w c : ℝ)))).map
        (fun y : TwoMarkedCloudSpace q A B =>
          (cloudEncode (q := q) (A := A) y.1, cloudEncode (q := q) (A := B) y.2)))
    (hlocal : Integrable (fun y : TwoMarkedCloudSpace q A B =>
      markedTilted q (r * (w c : ℝ)) (kin c) (g c) t y)
      (twoMarkedCloudLaw q A B αc βc (Real.toNNReal (r * (w c : ℝ))))) :
    Integrable (fun ω => tileBlockValue (q := q) w kin g Kcross r t ω c)
      (twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r)) := by
  have hrwc : (0 : ℝ) ≤ r * (w c : ℝ) := mul_nonneg hr (by positivity)
  have hBlockMeas : Measurable
      (fun p : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) =>
        blockTiltedValue q (r * (w c : ℝ)) (kin c) (g c) t p.1 p.2) :=
    measurable_blockTiltedValue q (r * (w c : ℝ)) (C := Cb) (G := G0)
      hrwc hCb0 hG0 hkin_meas hkin_bound hg_meas hgb t
  have hencMeas : Measurable (fun y : TwoMarkedCloudSpace q A B =>
      (cloudEncode (q := q) (A := A) y.1, cloudEncode (q := q) (A := B) y.2)) :=
    ((measurable_cloudEncode (q := q) (A := A)).comp measurable_fst).prodMk
      ((measurable_cloudEncode (q := q) (A := B)).comp measurable_snd)
  -- Integrability of the block value under the encoded local law.
  have hBlockInt : Integrable
      (fun p : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) =>
        blockTiltedValue q (r * (w c : ℝ)) (kin c) (g c) t p.1 p.2)
      ((twoMarkedCloudLaw q A B αc βc (Real.toNNReal (r * (w c : ℝ)))).map
        (fun y : TwoMarkedCloudSpace q A B =>
          (cloudEncode (q := q) (A := A) y.1, cloudEncode (q := q) (A := B) y.2))) := by
    rw [integrable_map_measure hBlockMeas.aestronglyMeasurable hencMeas.aemeasurable]
    simpa only [Function.comp_def, ← markedTilted_eq_blockTiltedValue_cloudEncode] using hlocal
  have hBlockIntG : Integrable
      (fun p : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) =>
        blockTiltedValue q (r * (w c : ℝ)) (kin c) (g c) t p.1 p.2)
      ((twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r)).map
        (fun ω : TwoMarkedCloudSpace q (C × A) (C × B) =>
          (cloudEncode (labelCloud c ω.1), cloudEncode (labelCloud c ω.2)))) := by
    rwa [hlaw]
  have hcomp := (integrable_map_measure hBlockMeas.aestronglyMeasurable hmeas).mp hBlockIntG
  refine hcomp.congr (Eventually.of_forall fun ω => ?_)
  show blockTiltedValue q (r * (w c : ℝ)) (kin c) (g c) t
      (cloudEncode (labelCloud c ω.1)) (cloudEncode (labelCloud c ω.2)) =
    tileBlockValue (q := q) w kin g Kcross r t ω c
  rw [← markedTilted_eq_blockTiltedValue_cloudEncode]
  exact (tileBlockValue_eq (q := q) (C := C) (A := A) (B := B)
    (w := w) (kin := kin) (g := g) (Kcross := Kcross) (r := r) (t := t)
    hq hr hkin_homog ω c).symm

/-- **Expected finite-tile comparison.**  The global pressure is at most the
sum of the local tile pressures plus the uniform edge bound times half the
expected label discrepancy. -/
theorem markedPressure_le_sum_tile_add_discrepancy
    (q : ℕ) (hq : 0 < q)
    {w : C → ℝ≥0} {kin : C → A → B → (Fin q → ℝ) → ℝ} {g : C → A → B → ℝ}
    {Kcross Cb G t r : ℝ} (hr : 0 ≤ r) (hCb0 : 0 ≤ Cb) (hG0 : 0 ≤ G)
    (hK0 : 0 ≤ Kcross) (hwle : ∀ c, w c ≤ 1)
    (hkin_bound : ∀ c a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hgb : ∀ c a b, |g c a b| ≤ G)
    (αg : Measure (C × A)) [IsProbabilityMeasure αg]
    (βg : Measure (C × B)) [IsProbabilityMeasure βg]
    (hIntTile : ∀ c, Integrable
      (fun ω => tileBlockValue (q := q) w kin g Kcross r t ω c)
      (twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r)))
    (hIntDisc : Integrable (tileLabelDiscrepancy (q := q) (C := C) (A := A) (B := B))
      (twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r)))
    (hIntTilt : Integrable
      (fun ω => markedTilted q (r : ℝ) (tileKin q w kin Kcross) (tileProbe g) t ω)
      (twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r))) :
    markedPressure q (C × A) (C × B) αg βg
        (Real.toNNReal r) (tileKin q w kin Kcross) (tileProbe g) t ≤
      (∑ c : C, ∫ ω, tileBlockValue (q := q) w kin g Kcross r t ω c
        ∂(twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r))) +
      (r ^ (2 / (q : ℝ)) * (max Cb Kcross * (q : ℝ)) + |t| * G) *
        (1 / 2 * ∫ ω, tileLabelDiscrepancy (q := q) (C := C) (A := A) (B := B) ω
          ∂(twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r))) := by
  classical
  have hdet := markedTilted_le_tileBlockSum_add_discrepancy (q := q)
    (R := r) (t := t) (Cb := Cb) (G := G) (Kcross := Kcross)
    hq hr hCb0 hG0 hK0 hwle hkin_bound hgb
  have hIntSum : Integrable
      (fun ω => ∑ c : C, tileBlockValue (q := q) w kin g Kcross r t ω c)
      (twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r)) :=
    integrable_finset_sum _ fun c _ => hIntTile c
  have hIntScaled : Integrable
      (fun ω => (r ^ (2 / (q : ℝ)) * (max Cb Kcross * (q : ℝ)) + |t| * G) *
        (1 / 2 * tileLabelDiscrepancy (q := q) (C := C) (A := A) (B := B) ω))
      (twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r)) := by
    simpa only [mul_assoc] using
      hIntDisc.const_mul ((r ^ (2 / (q : ℝ)) * (max Cb Kcross * (q : ℝ)) + |t| * G) *
        (1 / 2))
  have hIntUpper : Integrable
      (fun ω => (∑ c : C, tileBlockValue (q := q) w kin g Kcross r t ω c) +
        (r ^ (2 / (q : ℝ)) * (max Cb Kcross * (q : ℝ)) + |t| * G) *
          (1 / 2 * tileLabelDiscrepancy (q := q) (C := C) (A := A) (B := B) ω))
      (twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r)) :=
    hIntSum.add hIntScaled
  have hmono : ∫ ω, markedTilted q (r : ℝ) (tileKin q w kin Kcross) (tileProbe g) t ω
        ∂(twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r)) ≤
      ∫ ω, ((∑ c : C, tileBlockValue (q := q) w kin g Kcross r t ω c) +
        (r ^ (2 / (q : ℝ)) * (max Cb Kcross * (q : ℝ)) + |t| * G) *
          (1 / 2 * tileLabelDiscrepancy (q := q) (C := C) (A := A) (B := B) ω))
        ∂(twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r)) := by
    refine integral_mono_ae hIntTilt hIntUpper ?_
    filter_upwards with ω
    simpa only [tileBlockValue, tileLabelDiscrepancy] using hdet ω
  have hsplit : ∫ ω, ((∑ c : C, tileBlockValue (q := q) w kin g Kcross r t ω c) +
        (r ^ (2 / (q : ℝ)) * (max Cb Kcross * (q : ℝ)) + |t| * G) *
          (1 / 2 * tileLabelDiscrepancy (q := q) (C := C) (A := A) (B := B) ω))
        ∂(twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r)) =
      (∑ c : C, ∫ ω, tileBlockValue (q := q) w kin g Kcross r t ω c
        ∂(twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r))) +
      (r ^ (2 / (q : ℝ)) * (max Cb Kcross * (q : ℝ)) + |t| * G) *
        (1 / 2 * ∫ ω, tileLabelDiscrepancy (q := q) (C := C) (A := A) (B := B) ω
          ∂(twoMarkedCloudLaw q (C × A) (C × B) αg βg (Real.toNNReal r))) := by
    rw [integral_add hIntSum hIntScaled]
    rw [integral_finsetSum (Finset.univ) (fun c _ => hIntTile c)]
    rw [integral_const_mul, integral_const_mul]
  unfold markedPressure
  rw [Real.coe_toNNReal _ hr]
  rw [hsplit] at hmono
  exact hmono

end OTSelector.Probability
