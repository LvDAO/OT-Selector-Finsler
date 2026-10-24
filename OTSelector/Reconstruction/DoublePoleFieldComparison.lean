import OTSelector.Reconstruction.PositivePoleLoewnerComparison

/-!
# Internal two-sided comparison for a genuine positive double-pole field

A smooth actual remainder has uniform two-sided scalar bounds on a smaller compact
neighborhood. Combined with the same field's uniform positivity, this internally produces
the geometric constants comparing it with its actual fixed pole plus identity.
-/

open Set Matrix
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The geometric double-pole comparison is a consequence of the genuine positive field
and continuous actual remainder. Its residue and remainder need not commute. -/
theorem exists_doublePole_field_comparison
    {W R : ℝ→Matrix ι ι ℝ} {G : Matrix ι ι ℝ} {ε κ : ℝ}
    (hε : 0<ε) (hκ : 0<κ) (hG : G.PosSemidef)
    (hR : ContinuousOn R (Ioo (-ε) ε))
    (hW : ∀s∈Ioo 0 ε, (W s-κ•1).PosSemidef)
    (hpole : ∀s∈Ioo 0 ε, W s=(s^2)⁻¹•G+R s) :
    ∃ δ : ℝ, δ>0 ∧ δ<ε ∧ ∃ c : ℝ, c>0 ∧ ∃ C : ℝ, C>0 ∧ ∀s∈Ioo 0 δ,
      (W s-c•((s^2)⁻¹•G+1)).PosSemidef ∧
      (C•((s^2)⁻¹•G+1)-W s).PosSemidef := by
  let δ := ε/2
  have hδ : 0<δ := half_pos hε
  have hδε : δ<ε := half_lt_self hε
  have hsub : Icc (-δ) δ ⊆ Ioo (-ε) ε := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  obtain ⟨M,hM,hRbound⟩ := exists_compact_remainder_scalar_bounds isCompact_Icc (hR.mono hsub)
  obtain ⟨c,hc,C,hC,hcompare⟩ :=
    exists_positive_matrix_remainder_comparison_constants (ι:=ι) hκ hM
  refine ⟨δ,hδ,hδε,c,hc,C,hC,fun s hs ↦ ?_⟩
  have hsε : s∈Ioo 0 ε := ⟨hs.1,hs.2.trans hδε⟩
  have hsδ : s∈Icc (-δ) δ := ⟨by linarith [hs.1],hs.2.le⟩
  have hP : ((s^2)⁻¹•G).PosSemidef := hG.smul (inv_nonneg.mpr (sq_nonneg s))
  have hWHerm := (posDef_of_scalar_identity_lower_bound hκ (hW s hsε)).isHermitian
  have hRHerm : (R s).IsHermitian := by
    have heq : R s=W s-(s^2)⁻¹•G := by rw [hpole s hsε]; abel
    rw [heq]
    exact hWHerm.sub hP.isHermitian
  obtain ⟨hRu,hRl⟩ := hRbound s hsδ hRHerm
  exact hcompare (W s) ((s^2)⁻¹•G) (R s) hP (hW s hsε) hRu hRl (hpole s hsε)

end OTSelector.Reconstruction
