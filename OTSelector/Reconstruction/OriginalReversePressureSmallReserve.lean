import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.LiminfLimsup

/-! Remove a vanishing genuine reserve after the physical pressure dilation. -/
open Filter Topology
noncomputable section
namespace OTSelector.Reconstruction

/-- Keep the same candidate and its original tilt while the physical unit
pressure tilt changes by the exact dilation factor. Continuity then removes
the reserve without selecting new minimizers at each reserve size. -/
theorem originalPressure_le_sameCandidate_of_scaled_reserve_bounds
    {q : ℕ} (hq : 2 < q) {p : ℝ → ℝ} {τ value C L : ℝ}
    (hp : ContinuousAt p τ)
    (hbound : ∀ ρ : ℝ, 0 < ρ →
      p (τ*(1+ρ)^(2/(q : ℝ))) ≤
        (1+ρ)^(-(1-2/(q : ℝ))) *
          (value+C*ρ^(1-2/(q : ℝ))+L*ρ)) :
    p τ ≤ value := by
  have hqR : (2 : ℝ) < q := by exact_mod_cast hq
  have he : 0 < 1-2/(q : ℝ) := by
    rw [sub_pos,div_lt_one (by linarith : (0 : ℝ) < q)]
    exact hqR
  have hρ : Tendsto (fun ρ : ℝ ↦ ρ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hbase : Tendsto (fun ρ : ℝ ↦ 1+ρ) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using tendsto_const_nhds.add hρ
  have hpower (a : ℝ) : Tendsto (fun ρ : ℝ ↦ (1+ρ)^a) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using hbase.rpow_const (p := a) (Or.inl one_ne_zero)
  have hleft : Tendsto (fun ρ : ℝ ↦ p (τ*(1+ρ)^(2/(q : ℝ))))
      (𝓝[>] (0 : ℝ)) (𝓝 (p τ)) := by
    apply hp.tendsto.comp
    simpa using (hpower (2/(q : ℝ))).const_mul τ
  have herr : Tendsto (fun ρ : ℝ ↦ ρ^(1-2/(q : ℝ))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hh := (tendsto_rpow_neg_nhdsGT_zero (y := -(1-2/(q : ℝ))) (by linarith)).inv_tendsto_atTop
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with ρ hρpos
    change (ρ^(-(1-2/(q : ℝ))))⁻¹ = ρ^(1-2/(q : ℝ))
    rw [Real.rpow_neg hρpos.le]
    simp
  have hright : Tendsto (fun ρ : ℝ ↦ (1+ρ)^(-(1-2/(q : ℝ))) *
      (value+C*ρ^(1-2/(q : ℝ))+L*ρ)) (𝓝[>] (0 : ℝ)) (𝓝 value) := by
    simpa using (hpower (-(1-2/(q : ℝ)))).mul
      ((tendsto_const_nhds.add (herr.const_mul C)).add (hρ.const_mul L))
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with ρ hρpos
  exact hbound ρ hρpos

end OTSelector.Reconstruction
