import OTSelector.Reconstruction.OriginalStageClockSlabs

/-! Original separated clock laws produce actual finite half-open analytic stages. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- The closed hull of a short true clock slab has only one original colour. -/
theorem originalClockSlab_monochrome {μ ν : Measure ℝ} {δ D s t : ℝ}
    (hsep : ConditionalClockSupportBounds μ ν δ D) (hwidth : t - s < δ) :
    μ (Icc s t) = 0 ∨ ν (Icc s t) = 0 := by
  by_cases hμ : μ (Icc s t) = 0
  · exact Or.inl hμ
  · right
    by_contra hν
    obtain ⟨a, ha, has⟩ := scalarBin_exists_mem_support_of_mass_ne_zero μ hμ
    obtain ⟨b, hb, hbs⟩ := scalarBin_exists_mem_support_of_mass_ne_zero ν hν
    have hgap := hsep.separated a has b hbs
    rw [Real.dist_eq] at hgap
    have hab : |a - b| ≤ t - s := abs_le.mpr ⟨by linarith [ha.1, hb.2], by linarith [ha.2, hb.1]⟩
    linarith

/-- The two actual half-open slab laws are monochrome even when a threshold carries an
atom. Both endpoint conventions lie in the same short closed hull. -/
theorem originalClockHalfOpenSlab_monochrome {μ ν : Measure ℝ} {δ D s t : ℝ}
    (hsep : ConditionalClockSupportBounds μ ν δ D) (hwidth : t - s < δ) :
    μ (Ico s t) = 0 ∨ ν (Ioc s t) = 0 := by
  rcases originalClockSlab_monochrome hsep hwidth with hs | ht
  · exact Or.inl (measure_mono_null Ico_subset_Icc_self hs)
  · exact Or.inr (measure_mono_null Ioc_subset_Icc_self ht)

/-- A genuine uniform finite grid can have arbitrarily short cells while keeping the
original two outer clock thresholds exactly. Its formula remains meaningful beyond the
last stage solely to make all comparisons of thresholds direct. -/
theorem exists_originalStageClockGrid {lo hi δ : ℝ} (hlt : lo < hi) (hδ : 0 < δ) :
    ∃ G : OriginalStageClockGrid, 0 < G.count ∧ G.cut 0 = lo ∧ G.cut G.count = hi ∧
      ∀ i : Fin G.count, G.cut (i + 1) - G.cut i < δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((hi - lo) / δ)
  have hnpos : (0 : ℝ) < n := lt_trans (div_pos (sub_pos.mpr hlt) hδ) hn
  have hn0 : 0 < n := by exact_mod_cast hnpos
  have hstep : 0 < (hi - lo) / (n : ℝ) := div_pos (sub_pos.mpr hlt) hnpos
  let G : OriginalStageClockGrid :=
    { count := n
      cut := fun k ↦ lo + (k : ℝ) * ((hi - lo) / n)
      strictMono := by
        intro a b hab
        have hab' : (a : ℝ) < b := by exact_mod_cast hab
        simpa only [add_comm] using add_lt_add_left (mul_lt_mul_of_pos_right hab' hstep) lo }
  refine ⟨G, hn0, ?_, ?_, ?_⟩
  · simp [G]
  · dsimp [G]
    field_simp
    ring
  · intro i
    have hsmall : (hi - lo) / (n : ℝ) < δ := (div_lt_iff₀ hnpos).mpr (by
      simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hn)
    dsimp [G]
    push_cast
    nlinarith

/-- Original laws on the actual open clock window produce their own finite analytic
stages: literal source Ico and target Ioc, exact total measures, and internal single-colour
proofs. Empty stages and adjacent stages of one colour are retained. -/
theorem exists_originalMonochromeClockSlabs {μ ν : Measure ℝ} {δ D lo hi : ℝ}
    (hsep : ConditionalClockSupportBounds μ ν δ D) (hδ : 0 < δ) (hlt : lo < hi)
    (hμ : ∀ᵐ x ∂μ, x ∈ Ioo lo hi) (hν : ∀ᵐ x ∂ν, x ∈ Ioo lo hi) :
    ∃ G : OriginalStageClockGrid, 0 < G.count ∧ G.cut 0 = lo ∧ G.cut G.count = hi ∧
      (∑ i, μ.restrict (G.sourceCell i)) = μ ∧
      (∑ i, ν.restrict (G.targetCell i)) = ν ∧
      ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0 := by
  obtain ⟨G, hn, hlo, hhi, hwidth⟩ := exists_originalStageClockGrid hlt hδ
  have hμ' : ∀ᵐ x ∂μ, x ∈ Ico (G.cut 0) (G.cut G.count) := by
    filter_upwards [hμ] with x hx
    rw [hlo, hhi]
    exact ⟨hx.1.le, hx.2⟩
  have hν' : ∀ᵐ x ∂ν, x ∈ Ioc (G.cut 0) (G.cut G.count) := by
    filter_upwards [hν] with x hx
    rw [hlo, hhi]
    exact ⟨hx.1, hx.2.le⟩
  exact ⟨G, hn, hlo, hhi, (G.sum_restrict μ ν hμ' hν').1,
    (G.sum_restrict μ ν hμ' hν').2,
    fun i ↦ originalClockHalfOpenSlab_monochrome hsep (hwidth i)⟩

end OTSelector.Reconstruction
