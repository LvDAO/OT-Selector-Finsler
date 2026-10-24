import OTSelector.Reconstruction.FinslerRelativeLawClassCubeBinomial

/-! Positive integer microscopic grids with the original large-N scale unchanged. -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The original rounded microscopic order with its zero-sample order set to
at least one, so every literal half-open box is defined. -/
def positiveMicroscopicGridOrder (q : ℕ) (L : ℝ) (N : ℕ) : ℕ :=
  max 1 (microscopicGridOrder q L N)

instance positiveMicroscopicGridOrder_neZero (q : ℕ) (L : ℝ) (N : ℕ) :
    NeZero (positiveMicroscopicGridOrder q L N) :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℕ) < 1) (le_max_left _ _))⟩

/-- Literal side length in the positive uniform partition. -/
def positiveMicroscopicGridSide (q : ℕ) (L : ℝ) (N : ℕ) : ℝ :=
  (positiveMicroscopicGridOrder q L N : ℝ)⁻¹

theorem positiveMicroscopicGridSide_nonneg (q : ℕ) (L : ℝ) (N : ℕ) :
    0 ≤ positiveMicroscopicGridSide q L N := inv_nonneg.mpr (Nat.cast_nonneg _)

theorem positiveMicroscopicGridOrder_eq_of_pos (q : ℕ) {L : ℝ} (hL : 0 < L)
    {N : ℕ} (hN : 0 < N) :
    positiveMicroscopicGridOrder q L N = microscopicGridOrder q L N :=
  max_eq_right (microscopicGridOrder_pos q hL (Nat.cast_pos.mpr hN))

theorem positiveMicroscopicGridOrder_eventually_eq (q : ℕ) {L : ℝ} (hL : 0 < L) :
    ∀ᶠ N : ℕ in atTop, positiveMicroscopicGridOrder q L N = microscopicGridOrder q L N := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact positiveMicroscopicGridOrder_eq_of_pos q hL (by omega)

theorem positiveMicroscopicGridSide_eventually_eq (q : ℕ) {L : ℝ} (hL : 0 < L) :
    ∀ᶠ N : ℕ in atTop, positiveMicroscopicGridSide q L N = microscopicGridSide q L N := by
  filter_upwards [positiveMicroscopicGridOrder_eventually_eq q hL] with N hN
  simp only [positiveMicroscopicGridSide, microscopicGridSide, hN]

theorem tendsto_positiveMicroscopicGridOrder {q : ℕ} (hq : 0 < q) {L : ℝ} (hL : 0 < L) :
    Tendsto (positiveMicroscopicGridOrder q L) atTop atTop :=
  ((tendsto_microscopicGridOrder hq hL).comp tendsto_natCast_atTop_atTop).congr'
    ((positiveMicroscopicGridOrder_eventually_eq q hL).mono fun _ h ↦ h.symm)

theorem tendsto_positiveMicroscopicGridSide {q : ℕ} (hq : 0 < q) {L : ℝ} (hL : 0 < L) :
    Tendsto (positiveMicroscopicGridSide q L) atTop (𝓝 0) :=
  ((tendsto_microscopicGridSide hq hL).comp tendsto_natCast_atTop_atTop).congr'
    ((positiveMicroscopicGridSide_eventually_eq q hL).mono fun _ h ↦ h.symm)

theorem tendsto_positiveMicroscopicGrid_mass {q : ℕ} (hq : 0 < q) {L : ℝ} (hL : 0 < L) :
    Tendsto (fun N : ℕ ↦ (N : ℝ) * positiveMicroscopicGridSide q L N ^ q)
      atTop (𝓝 (L ^ q)) := by
  apply Tendsto.congr' _ ((tendsto_microscopicGrid_mass hq hL).comp tendsto_natCast_atTop_atTop)
  filter_upwards [positiveMicroscopicGridSide_eventually_eq q hL] with N hN
  simp only [Function.comp_def, hN]

/-- The same actual full-cube count probability on the everywhere positive grid. -/
def positiveMicroscopicCubeProbability (q : ℕ) (density : ℝ≥0) (L : ℝ) (N : ℕ) : I :=
  ⟨min ((density : ℝ) * positiveMicroscopicGridSide q L N ^ q) 1,
    le_min (mul_nonneg density.coe_nonneg (pow_nonneg (positiveMicroscopicGridSide_nonneg q L N) q))
      (by norm_num), min_le_right _ _⟩

theorem positiveMicroscopicCubeProbability_eventually_eq (q : ℕ) (density : ℝ≥0)
    {L : ℝ} (hL : 0 < L) :
    ∀ᶠ N : ℕ in atTop,
      positiveMicroscopicCubeProbability q density L N = microscopicCubeProbability q density L N := by
  filter_upwards [positiveMicroscopicGridSide_eventually_eq q hL] with N hN
  apply Subtype.ext
  change min _ 1 = min _ 1
  rw [hN]

end OTSelector.Reconstruction
