import OTSelector.Reconstruction.FinslerOriginalPressureDensityScale
import OTSelector.Reconstruction.FinslerConcreteUpperOriginalMacroGridScale

/-! Fixed microscopic sides and missing-volume accuracies can be chosen after
their actual original pressure and legal-repair limits, before any samples. -/
open Set Filter
open scoped Topology BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction

/-- Finite original cells may choose different microscopic sides while
retaining any prescribed positive loss budget. The signed pressure costs
are controlled by their true limits; no uniform sign assumption is used. -/
theorem exists_finite_family_pressure_sides_and_accuracy
    {Cells : Type*} [Fintype Cells]
    (F rate : Cells → ℝ → ℝ) (target ε : Cells → ℝ)
    (hF : ∀ c, Tendsto (F c) atTop (𝓝 (target c)))
    (hε : ∀ c, 0 < ε c) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ scale δ : Cells → ℝ,
      (∀ c, 0 < scale c) ∧ (∀ c, 0 < δ c) ∧ (∀ c, δ c ≤ ε c) ∧
      (Finset.univ.sum (fun (c : Cells) ↦ F c (scale c) + δ c * |rate c (scale c)|)) ≤ (∑ c, target c) + ζ := by
  classical
  let denom := (Fintype.card Cells : ℝ) + 1
  let tol := ζ / (2 * denom)
  have hdenom : 0 < denom := by dsimp only [denom]; positivity
  have htol : 0 < tol := div_pos hζ (mul_pos (by norm_num) hdenom)
  have hchoice (c : Cells) : ∃ L : ℝ, 0 < L ∧ F c L ≤ target c + tol := by
    have hevent := ((hF c).eventually (Iio_mem_nhds (by linarith : target c < target c + tol))).and
      (eventually_gt_atTop (0 : ℝ))
    obtain ⟨L,hL,hpos⟩ := hevent.exists
    exact ⟨L,hpos,hL.le⟩
  choose scale hscale hbound using hchoice
  let δ := fun c ↦ min (ε c) (tol / (|rate c (scale c)| + 1))
  have hδ (c : Cells) : 0 < δ c :=
    lt_min (hε c) (div_pos htol (by positivity))
  have hδle (c : Cells) : δ c ≤ ε c := min_le_left _ _
  have hcost (c : Cells) : δ c * |rate c (scale c)| ≤ tol := by
    calc
      _ ≤ (tol / (|rate c (scale c)| + 1)) * |rate c (scale c)| :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg _)
      _ ≤ (tol / (|rate c (scale c)| + 1)) * (|rate c (scale c)| + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = tol := div_mul_cancel₀ _ (by positivity)
  refine ⟨scale,δ,hscale,hδ,hδle,?_⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ ↦
    add_le_add (hbound c) (hcost c))
  have htolSum : (∑ _ : Cells, (2 * tol)) ≤ ζ := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc
      (Fintype.card Cells : ℝ) * (2 * tol) ≤ denom * (2 * tol) :=
        mul_le_mul_of_nonneg_right (by dsimp only [denom]; linarith) (by positivity)
      _ = ζ := by dsimp only [tol]; field_simp
  calc
    _ ≤ ∑ c, ((target c + tol) + tol) := hsum
    _ = (∑ c, target c) + ∑ _ : Cells, (2 * tol) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ ≤ _ := add_le_add (le_refl _) htolSum

end OTSelector.Reconstruction
