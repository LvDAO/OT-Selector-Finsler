import OTSelector.Reconstruction.FinslerPhysicalSceneRootedStrictClockExhaustion

/-! Any two strictly forward choices in an open clock interval fit one common
rational strict window inside that same interval. The collection is countable
and imposes no global ordering between the source and target clock supports. -/

open Set
noncomputable section
namespace OTSelector.Reconstruction

/-- A possible split between two legal targets has one common rational
interior window, without truncating either original plan. -/
theorem exists_strictClock_window_for_two_targets
    {ι : Type*} [Fintype ι] {lo hi : ℝ}
    {x y z : (ι → ℝ) × ℝ}
    (hx : x.2 ∈ Ioo lo hi) (hy : y.2 ∈ Ioo lo hi) (hz : z.2 ∈ Ioo lo hi)
    (hxy : x.2 < y.2) (hxz : x.2 < z.2) :
    ∃ q : RationalScalarPairWindow,
      lo < (q.val.1 : ℝ) ∧ (q.val.2.1 : ℝ) < hi ∧
      (x, y) ∈ physicalSceneStrictClockRegion q ∧
      (x, z) ∈ physicalSceneStrictClockRegion q := by
  obtain ⟨l, hlo, hl⟩ := exists_rat_btwn (lt_min hx.1 (lt_min hy.1 hz.1))
  obtain ⟨r, hr, hrhi⟩ := exists_rat_btwn (max_lt hx.2 (max_lt hy.2 hz.2))
  obtain ⟨d, hd0, hd⟩ := exists_rat_btwn (lt_min (sub_pos.mpr hxy) (sub_pos.mpr hxz))
  have hlx : (l : ℝ) < x.2 := hl.trans_le (min_le_left _ _)
  have hly : (l : ℝ) < y.2 := hl.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hlz : (l : ℝ) < z.2 := hl.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hxr : x.2 < (r : ℝ) := (le_max_left _ _).trans_lt hr
  have hyr : y.2 < (r : ℝ) := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hr
  have hzr : z.2 < (r : ℝ) := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hr
  have hlr : l < r := by exact_mod_cast hlx.trans hxr
  have hdpos : (0 : ℚ) < d := by exact_mod_cast hd0
  refine ⟨⟨(l, r, d), hlr, hdpos⟩, hlo, hrhi, ?_, ?_⟩
  · exact ⟨⟨hlx, hxr⟩, ⟨hly, hyr⟩, hd.trans_le (min_le_left _ _)⟩
  · exact ⟨⟨hlx, hxr⟩, ⟨hlz, hzr⟩, hd.trans_le (min_le_right _ _)⟩

end OTSelector.Reconstruction
