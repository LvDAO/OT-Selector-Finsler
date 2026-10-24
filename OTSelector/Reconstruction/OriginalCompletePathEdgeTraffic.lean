import OTSelector.Reconstruction.MarkedStationaryValueLegalFullPathNonnegativeCampbell
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Exact original-edge readout of literal complete-path traffic and its momentum weights. -/
open Set Function Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- The complete physical-clock traffic of one unchanged original edge. -/
def legalMarkedCompletePathEdgeTraffic (q : ℕ)
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ)
    (h : (Fin q → ℝ) → ℝ≥0∞) (f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞)
    (e : LegalMarkedPhysicalEdge q) : ℝ≥0∞ :=
  ∫⁻ c : ℝ, h ((physicalPairAnchor e).1 + d ((physicalPairAnchor e).2, c)) *
    f ((physicalPairAnchor e).2, c) ∂volume

theorem measurable_legalMarkedCompletePathEdgeTraffic {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f) :
    Measurable (legalMarkedCompletePathEdgeTraffic q d h f) := by
  have hG : Measurable (fun z : LegalMarkedPhysicalEdge q × ℝ ↦
      h ((physicalPairAnchor z.1).1 + d ((physicalPairAnchor z.1).2, z.2)) *
        f ((physicalPairAnchor z.1).2, z.2)) :=
    (hh.comp ((measurable_physicalPairAnchor.fst.comp measurable_fst).add
      (hd.comp ((measurable_physicalPairAnchor.snd.comp measurable_fst).prodMk
        measurable_snd)))).mul
      (hf.comp ((measurable_physicalPairAnchor.snd.comp measurable_fst).prodMk measurable_snd))
  exact hG.lintegral_prod_right'

/-- Literal full-scene traffic integrates the per-edge quantity against the original first plan. -/
theorem legalMarkedCompletePathTraffic_eq_lintegral_edges {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f) (s : LegalMarkedOptimalInputScene q) :
    legalMarkedCompletePathTraffic q d h f s =
      ∫⁻ e, legalMarkedCompletePathEdgeTraffic q d h f e
        ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)) := by
  have hG : Measurable (fun z : ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) × ℝ ↦
      h (z.1.1 + d (z.1.2, z.2)) * f (z.1.2, z.2)) :=
    (hh.comp (measurable_fst.fst.add
      (hd.comp (measurable_fst.snd.prodMk measurable_snd)))).mul
      (hf.comp (measurable_fst.snd.prodMk measurable_snd))
  unfold legalMarkedCompletePathTraffic
  rw [physicalScenePairKernel_apply, lintegral_map hG.lintegral_prod_right'
    measurable_physicalPairAnchor]
  rfl

/-- Finite actual scene traffic yields genuine integrable real per-edge traffic. -/
theorem integrable_toReal_legalMarkedCompletePathEdgeTraffic {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f) (s : LegalMarkedOptimalInputScene q)
    (hfinite : legalMarkedCompletePathTraffic q d h f s ≠ ∞) :
    Integrable (fun e ↦ (legalMarkedCompletePathEdgeTraffic q d h f e).toReal)
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) := by
  apply integrable_toReal_of_lintegral_ne_top
    (measurable_legalMarkedCompletePathEdgeTraffic d hd hh hf).aemeasurable
  rw [← legalMarkedCompletePathTraffic_eq_lintegral_edges d hd hh hf s]
  exact hfinite

/-- The real observable is exactly the integral of the same original per-edge traffic. -/
theorem toReal_legalMarkedCompletePathTraffic_eq_integral_edges {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f) (s : LegalMarkedOptimalInputScene q)
    (hfinite : legalMarkedCompletePathTraffic q d h f s ≠ ∞) :
    (legalMarkedCompletePathTraffic q d h f s).toReal =
      ∫ e, (legalMarkedCompletePathEdgeTraffic q d h f e).toReal
        ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)) := by
  rw [legalMarkedCompletePathTraffic_eq_lintegral_edges d hd hh hf s] at hfinite ⊢
  exact (integral_toReal
    (measurable_legalMarkedCompletePathEdgeTraffic d hd hh hf).aemeasurable
    (ae_lt_top (measurable_legalMarkedCompletePathEdgeTraffic d hd hh hf) hfinite)).symm

/-- A paired-mark momentum weight factors out of its own original edge's physical-clock integral. -/
theorem legalMarkedCompletePathEdgeTraffic_markWeight {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ)
    (h : (Fin q → ℝ) → ℝ≥0∞) (f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞)
    (p : PhysicalPairPalmMark (Fin q) → ℝ) (e : LegalMarkedPhysicalEdge q) :
    legalMarkedCompletePathEdgeTraffic q d h (fun z ↦ ENNReal.ofReal (p z.1) * f z) e =
      ENNReal.ofReal (p (physicalPairAnchor e).2) *
        legalMarkedCompletePathEdgeTraffic q d h f e := by
  unfold legalMarkedCompletePathEdgeTraffic
  simp_rw [mul_left_comm (h _)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Weighted real traffic integrates actual momentum times original edge traffic. -/
theorem toReal_legalMarkedCompletePathTraffic_markWeight {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f)
    (p : PhysicalPairPalmMark (Fin q) → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (s : LegalMarkedOptimalInputScene q)
    (hfinite : legalMarkedCompletePathTraffic q d h
      (fun z ↦ ENNReal.ofReal (p z.1) * f z) s ≠ ∞) :
    (legalMarkedCompletePathTraffic q d h (fun z ↦ ENNReal.ofReal (p z.1) * f z) s).toReal =
      ∫ e, p (physicalPairAnchor e).2 * (legalMarkedCompletePathEdgeTraffic q d h f e).toReal
        ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)) := by
  rw [toReal_legalMarkedCompletePathTraffic_eq_integral_edges d hd
    (f := fun z ↦ ENNReal.ofReal (p z.1) * f z) hh
    ((hp.comp measurable_fst).ennreal_ofReal.mul hf) s hfinite]
  apply integral_congr_ae
  filter_upwards [] with e
  rw [legalMarkedCompletePathEdgeTraffic_markWeight, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (hp0 _)]

/-- Finite weighted literal scene traffic supplies integrability of the actual
momentum times the original per-edge clock traffic. -/
theorem integrable_legalMarkedCompletePathEdgeTraffic_markWeight {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f)
    (p : PhysicalPairPalmMark (Fin q) → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (s : LegalMarkedOptimalInputScene q)
    (hfinite : legalMarkedCompletePathTraffic q d h
      (fun z ↦ ENNReal.ofReal (p z.1) * f z) s ≠ ∞) :
    Integrable
      (fun e ↦ p (physicalPairAnchor e).2 *
        (legalMarkedCompletePathEdgeTraffic q d h f e).toReal)
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) := by
  have hi := integrable_toReal_legalMarkedCompletePathEdgeTraffic d hd
    (f := fun z ↦ ENNReal.ofReal (p z.1) * f z) hh
    ((hp.comp measurable_fst).ennreal_ofReal.mul hf) s hfinite
  apply hi.congr
  filter_upwards [] with e
  rw [legalMarkedCompletePathEdgeTraffic_markWeight, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (hp0 _)]

/-- Bounded actual contributor momentum makes weighted literal traffic finite,
using only finite unweighted traffic from the same original scene. -/
theorem legalMarkedCompletePathTraffic_markWeight_lt_top_of_contributor_bound {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f)
    (p : PhysicalPairPalmMark (Fin q) → ℝ) (hp : Measurable p)
    (s : LegalMarkedOptimalInputScene q) (A : Set (LegalMarkedPhysicalEdge q))
    (hfinite : legalMarkedCompletePathTraffic q d h f s ≠ ∞)
    (hzero : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)),
      e ∉ A → legalMarkedCompletePathEdgeTraffic q d h f e = 0)
    {H : ℝ} (hbound : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)),
      e ∈ A → p (physicalPairAnchor e).2 ≤ H) :
    legalMarkedCompletePathTraffic q d h (fun z ↦ ENNReal.ofReal (p z.1) * f z) s < ∞ := by
  rw [legalMarkedCompletePathTraffic_eq_lintegral_edges d hd
    (f := fun z ↦ ENNReal.ofReal (p z.1) * f z) hh
    ((hp.comp measurable_fst).ennreal_ofReal.mul hf) s]
  have hi : (∫⁻ e, legalMarkedCompletePathEdgeTraffic q d h f e
      ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q))) ≠ ∞ := by
    rw [← legalMarkedCompletePathTraffic_eq_lintegral_edges d hd hh hf s]
    exact hfinite
  calc
    _ ≤ ∫⁻ e, ENNReal.ofReal H * legalMarkedCompletePathEdgeTraffic q d h f e
        ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)) := by
      apply lintegral_mono_ae
      filter_upwards [hzero, hbound] with e hze hbe
      rw [legalMarkedCompletePathEdgeTraffic_markWeight]
      by_cases he : e ∈ A
      · gcongr
        exact hbe he
      · rw [hze he, mul_zero, mul_zero]
    _ = ENNReal.ofReal H * ∫⁻ e, legalMarkedCompletePathEdgeTraffic q d h f e
        ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hi)

end OTSelector.Reconstruction
