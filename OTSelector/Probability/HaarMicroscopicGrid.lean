import OTSelector.Probability.HaarAffineCube
import OTSelector.Probability.MicroscopicGridScale

/-! Original Haar microbox intensities at the actual integer microscopic grid.
The Haar Jacobian is produced once, independently of sample size and corners. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Probability
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {q : ℕ}

/-- Actual original Haar masses, with arbitrary moving grid corners, have the
correct count intensity at every fixed microscopic scale. No mass-limit or
coordinate-Jacobian premise is supplied by the caller. -/
theorem exists_original_haar_microscopic_grid_intensities
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    (hq : 0 < q) {L : ℝ} (hL : 0 < L) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (origin : ℝ → Fin q → ℝ) (markMass : ℝ≥0),
      Tendsto (fun N : ℝ ↦ N * (μ (affineHaarCube e (origin N)
        (microscopicGridOrder q L N : ℝ≥0)⁻¹)).toReal * (markMass : ℝ))
        atTop (𝓝 ((c : ℝ) * (markMass : ℝ) * L ^ q)) := by
  obtain ⟨c, hc, hcube⟩ := exists_original_affineHaarCube_laws μ e
  refine ⟨c, hc, fun origin markMass ↦ ?_⟩
  have hlim := (tendsto_microscopicGrid_density_mass hq hL (c : ℝ)).mul_const (markMass : ℝ)
  have hlim' : Tendsto
      (fun N : ℝ ↦ N * (c : ℝ) * microscopicGridSide q L N ^ q * (markMass : ℝ))
      atTop (𝓝 ((c : ℝ) * (markMass : ℝ) * L ^ q)) := by
    have heq : ((c : ℝ) * L ^ q) * (markMass : ℝ) =
        (c : ℝ) * (markMass : ℝ) * L ^ q := by ring
    rw [heq] at hlim
    exact hlim
  apply Tendsto.congr' _ hlim'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
  have hm : 0 < (microscopicGridOrder q L N : ℝ≥0) :=
    Nat.cast_pos.mpr (microscopicGridOrder_pos q hL hN)
  rw [(hcube (origin N) _ (inv_pos.mpr hm)).1]
  simp only [ENNReal.coe_toReal, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_inv,
    NNReal.coe_natCast, microscopicGridSide]
  ring

end OTSelector.Probability
