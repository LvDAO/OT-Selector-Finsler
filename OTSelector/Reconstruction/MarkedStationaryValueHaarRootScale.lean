import OTSelector.Reconstruction.MarkedStationaryValueHaarRootBoundary
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Exact actual cube radii for an original diverging finite sample mass. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- The positive centered cube radius with prescribed original mass N in
q transverse dimensions. -/
def haarRootRadius (q : ℕ) (N : ℝ) : ℝ := N ^ (1 / (q : ℝ)) / 2

theorem haarRootRadius_pos (q : ℕ) {N : ℝ} (hN : 0 < N) :
    0 < haarRootRadius q N := by
  exact div_pos (Real.rpow_pos_of_pos hN _) (by norm_num)

/-- The chosen actual root cube has exactly the original sample's mass. -/
theorem haarRootRadius_mass (q : ℕ) (hq : 0 < q) {N : ℝ} (hN : 0 < N) :
    (2 * haarRootRadius q N) ^ q = N := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hbase : 2 * haarRootRadius q N = N ^ (1 / (q : ℝ)) := by
    unfold haarRootRadius
    ring
  rw [hbase, ← Real.rpow_natCast, ← Real.rpow_mul hN.le]
  have hm : 1 / (q : ℝ) * (q : ℝ) = 1 := by field_simp
  rw [hm, Real.rpow_one]

theorem volume_haarRootCube_radius (ι : Type*) [Fintype ι]
    (hq : 0 < Fintype.card ι) {N : ℝ} (hN : 0 < N) :
    volume (haarRootCube ι (haarRootRadius (Fintype.card ι) N)) = ENNReal.ofReal N := by
  rw [volume_haarRootCube ι (haarRootRadius_pos _ hN).le, haarRootRadius_mass _ hq hN]

/-- Every diverging original sample mass supplies diverging actual cube roots. -/
theorem tendsto_haarRootRadius (q : ℕ) (hq : 0 < q)
    {N : ℕ → ℝ} (hN : Tendsto N atTop atTop) :
    Tendsto (fun n ↦ haarRootRadius q (N n)) atTop atTop := by
  have he : (0 : ℝ) < 1 / (q : ℝ) := by exact one_div_pos.mpr (by exact_mod_cast hq)
  exact ((tendsto_rpow_atTop he).comp hN).atTop_div_const (by norm_num)

end OTSelector.Reconstruction
