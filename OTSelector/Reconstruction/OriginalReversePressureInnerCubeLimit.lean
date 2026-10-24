import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Vanishing-volume holes preserve the same signed candidate pressure. -/
open Filter Topology
noncomputable section
namespace OTSelector.Reconstruction

/-- After the genuine inner-cube comparison has been established, its
vanishing hole budget disappears without a sign assumption on the retained
candidate value or a uniform coercivity assumption on its kinetic coefficient. -/
theorem originalPressure_le_sameCandidate_of_vanishing_innerCube
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {q : ℕ} (hq : 2 < q) {s : ι → ℝ}
    {p value C L : ℝ} (hs : Tendsto s l (𝓝 1))
    (hbound : ∀ᶠ i in l,
      p ≤ (s i)^q*value+C*(1-(s i)^q)^(1-2/(q : ℝ))+L*(1-(s i)^q)) :
    p ≤ value := by
  have hqR : (2 : ℝ) < q := by exact_mod_cast hq
  have he : 0 < 1-2/(q : ℝ) := by
    rw [sub_pos,div_lt_one (by linarith : (0 : ℝ) < q)]
    exact hqR
  have hp : Tendsto (fun i ↦ (s i)^q) l (𝓝 1) := by simpa using hs.pow q
  have hh : Tendsto (fun i ↦ 1-(s i)^q) l (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (1 : ℝ)) l (𝓝 1)).sub hp
  have herr := hh.rpow_const_nhds_zero he
  have hlim : Tendsto (fun i ↦ (s i)^q*value+
      C*(1-(s i)^q)^(1-2/(q : ℝ))+L*(1-(s i)^q)) l (𝓝 value) := by
    simpa using ((hp.mul_const value).add (herr.const_mul C)).add (hh.const_mul L)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hbound

end OTSelector.Reconstruction
