import OTSelector.Probability.InterleavedDyadicSummability

/-! Compact regular birth has one elapsed-time dyadic index. Its physical
sqrt(s) gain and complete original count-tail term have a summable threshold. -/
noncomputable section
namespace OTSelector.Probability

/-- The actual regular-birth level profile, including all fixed physical and
clock-cover constants, is summable over the single elapsed-time scale. -/
theorem exists_summable_original_regularBirth_levels
    {K₀ E s₀ A B c : ℝ} (hK₀ : 0 ≤ K₀) (hE : 0 ≤ E) (hs₀ : 0 ≤ s₀)
    (hc : 0 < c) :
    ∃ C > 0, Summable (fun j : ℕ ↦
      A * Real.sqrt (interleavedLevelThreshold K₀ C 0 j * E) *
        Real.sqrt (s₀ / (2 : ℝ) ^ j) +
      B * ((2 : ℝ) ^ j * Real.exp (-c * interleavedLevelThreshold K₀ C 0 j))) := by
  let C := (Real.log 2 + 1) / c
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := div_pos (by linarith) hc
  have hcc : c * C = Real.log 2 + 1 := by dsimp [C]; field_simp
  have hdecay : Real.log 2 < c * C := by linarith
  let ρ : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ))
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg (by norm_num) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hgood := summable_sqrt_levelThreshold_geometric hK₀ hC.le hE
    hρ0 hρ1 hρ0 hρ1
  have hgoodj := hgood.comp_injective (fun _ _ h ↦ congrArg Prod.snd h :
    Function.Injective (fun j : ℕ ↦ ((0 : ℕ), j)))
  have hbadj := (summable_interleaved_exceptional (K₀ := K₀) hdecay).comp_injective
    (fun _ _ h ↦ congrArg Prod.snd h : Function.Injective (fun j : ℕ ↦ ((0 : ℕ), j)))
  have hgoodj' : Summable (fun j : ℕ ↦
      Real.sqrt (interleavedLevelThreshold K₀ C 0 j * E) * ρ ^ j) := by
    simpa only [Function.comp_def, pow_zero, mul_one] using hgoodj
  have hall := (hgoodj'.mul_left (A * Real.sqrt s₀)).add (hbadj.mul_left B)
  refine ⟨C, hC, hall.congr ?_⟩
  intro j
  have hscale : Real.sqrt (s₀ / (2 : ℝ) ^ j) = Real.sqrt s₀ * ρ ^ j := by
    rw [Real.sqrt_eq_rpow, dyadicScale_rpow_eq_geometric hs₀, ← Real.sqrt_eq_rpow]
  simp only [Function.comp_def, hscale]
  ring

end OTSelector.Probability
