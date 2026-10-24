import OTSelector.Probability.MarkedPoissonCube
import OTSelector.Probability.MarkedPressureLimitBlock

/-!
# Tile models encoded in the marked cube model

A finite family of independent local cube models can be encoded in one marked
cube model: the mark space is `C × A`, the mark's first coordinate selects the
tile, and the kinetic kernel branches on the tile.  On pairs of points with the
same tile `c`, the ambient coefficient `r ^ (2/q)` together with the kernel
scaling `w c ^ (1/q)` reproduces exactly the local model at intensity
`r * w c`; across tiles the kernel is the bounded quadratic cross cost.

This module sets up the kernel and proves the structural properties required by
the marked-pressure machinery: measurability, nonnegativity, the quadratic
bound and quadratic homogeneity.
-/

open MeasureTheory Filter
open scoped NNReal Topology

noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {C A B : Type*} [DecidableEq C] [Fintype C]

/-- The tile-selecting kinetic kernel.  On a common tile `c` it evaluates the
local kernel at the displacement scaled by `w c ^ (1/q)`; across tiles it uses
the quadratic cross cost `Kcross * |v| ^ 2`. -/
noncomputable def tileKin (q : ℕ) (w : C → ℝ≥0)
    (kin : C → A → B → (Fin q → ℝ) → ℝ) (Kcross : ℝ) :
    (C × A) → (C × B) → (Fin q → ℝ) → ℝ :=
  fun a b v =>
    if a.1 = b.1 then
      kin a.1 a.2 b.2 (fun l => (w a.1 : ℝ) ^ (1 / (q : ℝ)) * v l)
    else Kcross * ∑ l, v l ^ 2

/-- The tile-selecting probe: the local probe on a common tile, zero across
tiles. -/
noncomputable def tileProbe (g : C → A → B → ℝ) : (C × A) → (C × B) → ℝ :=
  fun a b => if a.1 = b.1 then g a.1 a.2 b.2 else 0

/-- Measurability of the tile kinetic kernel, from joint measurability of the
local kernels in the tile index. -/
theorem measurable_tileKin
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSingletonClass C]
    {w : C → ℝ≥0} {kin : C → A → B → (Fin q → ℝ) → ℝ} {Kcross : ℝ}
    (hw : Measurable w)
    (hkin : Measurable (fun p : C × A × B × (Fin q → ℝ) =>
      kin p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Measurable (Function.uncurry (fun p : (C × A) × (C × B) =>
      tileKin q w kin Kcross p.1 p.2)) := by
  classical
  apply Measurable.ite
  · exact measurableSet_eq_fun
      (by fun_prop : Measurable (fun pv : ((C × A) × (C × B)) × (Fin q → ℝ) =>
        pv.1.1.1))
      (by fun_prop : Measurable (fun pv : ((C × A) × (C × B)) × (Fin q → ℝ) =>
        pv.1.2.1))
  · -- same-tile branch
    have hinner : Measurable (fun pv : ((C × A) × (C × B)) × (Fin q → ℝ) =>
        (pv.1.1.1, pv.1.1.2, pv.1.2.2,
          fun l => (w pv.1.1.1 : ℝ) ^ (1 / (q : ℝ)) * pv.2 l)) := by
      fun_prop
    exact hkin.comp hinner
  · -- cross-tile branch
    have hsum : Measurable (fun pv : ((C × A) × (C × B)) × (Fin q → ℝ) =>
        ∑ l, pv.2 l ^ 2) := by
      fun_prop
    exact hsum.const_mul Kcross

/-- Measurability of the tile probe. -/
theorem measurable_tileProbe
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSingletonClass C]
    {g : C → A → B → ℝ}
    (hg : Measurable (fun p : C × A × B => g p.1 p.2.1 p.2.2)) :
    Measurable (fun p : (C × A) × (C × B) =>
      tileProbe g p.1 p.2) := by
  classical
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_eq_fun
      (by fun_prop : Measurable (fun p : (C × A) × (C × B) => p.1.1))
      (by fun_prop : Measurable (fun p : (C × A) × (C × B) => p.2.1))
  · exact hg.comp (by fun_prop : Measurable
      (fun p : (C × A) × (C × B) => (p.1.1, p.1.2, p.2.2)))

/-- Nonnegativity of the tile kinetic kernel. -/
theorem tileKin_nonneg {w : C → ℝ≥0} {kin : C → A → B → (Fin q → ℝ) → ℝ}
    {Kcross : ℝ} (hkin : ∀ c a b v, 0 ≤ kin c a b v) (hK : 0 ≤ Kcross)
    (a : C × A) (b : C × B) (v : Fin q → ℝ) :
    0 ≤ tileKin q w kin Kcross a b v := by
  unfold tileKin
  split_ifs with h
  · exact hkin _ _ _ _
  · exact mul_nonneg hK (Finset.sum_nonneg fun l _ => sq_nonneg _)

/-- The quadratic bound for the tile kinetic kernel. -/
theorem abs_tileKin_le {w : C → ℝ≥0} {kin : C → A → B → (Fin q → ℝ) → ℝ}
    {Kcross Cb : ℝ} (hq : 0 < q) (hwle : ∀ c, w c ≤ 1)
    (hkin : ∀ c a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hCb : 0 ≤ Cb) (hK : 0 ≤ Kcross)
    (a : C × A) (b : C × B) (v : Fin q → ℝ) :
    |tileKin q w kin Kcross a b v| ≤ max Cb Kcross * ∑ l, v l ^ 2 := by
  unfold tileKin
  have hsum : (0 : ℝ) ≤ ∑ l, v l ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  split_ifs with h
  · have hscaled : |kin a.1 a.2 b.2
        (fun l => (w a.1 : ℝ) ^ (1 / (q : ℝ)) * v l)| ≤
        Cb * ∑ l, ((w a.1 : ℝ) ^ (1 / (q : ℝ)) * v l) ^ 2 := hkin _ _ _ _
    have hfac : ((w a.1 : ℝ) ^ (1 / (q : ℝ))) ^ 2 ≤ 1 := by
      have hw1 : (w a.1 : ℝ) ≤ 1 := by exact_mod_cast hwle a.1
      have h0 : (0 : ℝ) ≤ (w a.1 : ℝ) := by positivity
      have hsq : ((w a.1 : ℝ) ^ (1 / (q : ℝ))) ^ 2 = (w a.1 : ℝ) ^ (2 / (q : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
        congr 1
        ring
      rw [hsq]
      exact Real.rpow_le_one h0 hw1 (by positivity)
    have hsum' : (∑ l, ((w a.1 : ℝ) ^ (1 / (q : ℝ)) * v l) ^ 2) ≤
        ∑ l, v l ^ 2 := by
      apply Finset.sum_le_sum
      intro l _
      rw [mul_pow]
      have := mul_le_mul_of_nonneg_right hfac (sq_nonneg (v l))
      simpa only [one_mul] using this
    calc |kin _ _ _ _| ≤ Cb * ∑ l, ((w a.1 : ℝ) ^ (1 / (q : ℝ)) * v l) ^ 2 := hscaled
      _ ≤ Cb * ∑ l, v l ^ 2 := mul_le_mul_of_nonneg_left hsum' hCb
      _ ≤ max Cb Kcross * ∑ l, v l ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hsum
  · rw [abs_mul, abs_of_nonneg hK, abs_of_nonneg hsum]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hsum

/-- Quadratic homogeneity of the tile kinetic kernel. -/
theorem tileKin_homog {w : C → ℝ≥0} {kin : C → A → B → (Fin q → ℝ) → ℝ}
    {Kcross : ℝ}
    (hkin : ∀ c a b (s : ℝ), 0 ≤ s → ∀ v : Fin q → ℝ,
      kin c a b (fun l => s * v l) = s ^ 2 * kin c a b v)
    (a : C × A) (b : C × B) (s : ℝ) (hs : 0 ≤ s) (v : Fin q → ℝ) :
    tileKin q w kin Kcross a b (fun l => s * v l) =
      s ^ 2 * tileKin q w kin Kcross a b v := by
  unfold tileKin
  split_ifs with h
  · have harg : (fun l => (w a.1 : ℝ) ^ (1 / (q : ℝ)) * (s * v l)) =
        fun l => (s * (w a.1 : ℝ) ^ (1 / (q : ℝ))) * v l := by
      funext l; ring
    rw [harg, hkin _ _ _ _ (mul_nonneg hs (Real.rpow_nonneg (by positivity) _)) v]
    rw [hkin _ _ _ _ (Real.rpow_nonneg (by positivity) _) v]
    ring
  · have hsum : (∑ l, (s * v l) ^ 2) = s ^ 2 * ∑ l, v l ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [hsum]
    ring

/-- The probe bound for the tile probe. -/
theorem abs_tileProbe_le {g : C → A → B → ℝ} {G : ℝ}
    (hG : 0 ≤ G) (hg : ∀ c a b, |g c a b| ≤ G) (a : C × A) (b : C × B) :
    |tileProbe g a b| ≤ G := by
  unfold tileProbe
  split_ifs with h
  · exact hg _ _ _
  · simpa using hG

/-- **Pressure limit of the encoded tile model.**  The encoded tile kernel and
probe satisfy all hypotheses of the marked-pressure limit theorem. -/
theorem exists_tilePressure_limit
    (q : ℕ) (hq : 4 < q)
    [MeasurableSpace C] [MeasurableSingletonClass C] [MeasurableSpace A]
    [MeasurableSpace B]
    {w : C → ℝ≥0} (hw : Measurable w) (hwle : ∀ c, w c ≤ 1)
    (α : Measure (C × A)) [IsProbabilityMeasure α]
    (β : Measure (C × B)) [IsProbabilityMeasure β]
    {Cb G Kcross : ℝ} (hCb0 : 0 ≤ Cb) (hG0 : 0 ≤ G) (hK0 : 0 ≤ Kcross)
    {kin : C → A → B → (Fin q → ℝ) → ℝ} {g : C → A → B → ℝ}
    (hkin_meas : Measurable (fun p : C × A × B × (Fin q → ℝ) =>
      kin p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hkin_nonneg : ∀ c a b v, 0 ≤ kin c a b v)
    (hkin_bound : ∀ c a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hkin_homog : ∀ c a b (s : ℝ), 0 ≤ s → ∀ v : Fin q → ℝ,
      kin c a b (fun l => s * v l) = s ^ 2 * kin c a b v)
    (hg_meas : Measurable (fun p : C × A × B => g p.1 p.2.1 p.2.2))
    (hgb : ∀ c a b, |g c a b| ≤ G) :
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun R => markedScalePressure q (C × A) (C × B) α β
        (tileKin q w kin Kcross) (tileProbe g) R t) atTop (𝓝 (p t))) ∧
      ConcaveOn ℝ Set.univ p ∧ LipschitzWith ⟨G, hG0⟩ p := by
  have hq0 : 0 < q := by omega
  have hCg0 : 0 ≤ max Cb Kcross := le_trans hCb0 (le_max_left _ _)
  exact exists_markedScalePressure_limit q hq α β hCg0 hG0
    (measurable_tileKin hw hkin_meas)
    (tileKin_nonneg hkin_nonneg hK0)
    (abs_tileKin_le hq0 hwle hkin_bound hCb0 hK0)
    (tileKin_homog hkin_homog)
    (measurable_tileProbe hg_meas)
    (abs_tileProbe_le hG0 hgb)

end OTSelector.Probability
