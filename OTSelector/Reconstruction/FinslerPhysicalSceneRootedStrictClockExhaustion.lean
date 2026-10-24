import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicTaylorLegalRectangles

/-!
# Countable strict-clock bins inside the original scalar-pair window

Every finite strictly legal clock exchange lies in rational closed source and
target bins with the original gap screen. These bins provide countable tests
for one common almost-sure physical support statement.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace RationalScalarPairWindow

/-- Every strict four-clock exchange admits rational closed bins inside the
same original scalar interval, with the same original positive gap screen. -/
theorem exists_physicalScene_rational_clock_bins (q : RationalScalarPairWindow)
    (S T : Fin 2 → ℝ)
    (hS : ∀ i, S i ∈ Ioo (q.val.1 : ℝ) (q.val.2.1 : ℝ))
    (hT : ∀ j, T j ∈ Ioo (q.val.1 : ℝ) (q.val.2.1 : ℝ))
    (hgap : ∀ i j, (q.val.2.2 : ℝ) < T j - S i) :
    ∃ sL sR tL tR : ℚ,
      Icc (sL : ℝ) (sR : ℝ) ⊆ Icc (q.val.1 : ℝ) (q.val.2.1 : ℝ) ∧
      Icc (tL : ℝ) (tR : ℝ) ⊆ Icc (q.val.1 : ℝ) (q.val.2.1 : ℝ) ∧
      (q.val.2.2 : ℝ) ≤ (tL : ℝ) - (sR : ℝ) ∧
      (∀ i, S i ∈ Ioo (sL : ℝ) (sR : ℝ)) ∧
      (∀ j, T j ∈ Ioo (tL : ℝ) (tR : ℝ)) := by
  let lo : ℝ := q.val.1
  let hi : ℝ := q.val.2.1
  let d : ℝ := q.val.2.2
  let smin := min (S 0) (S 1)
  let smax := max (S 0) (S 1)
  let tmin := min (T 0) (T 1)
  let tmax := max (T 0) (T 1)
  have hsmin : lo < smin := lt_min (hS 0).1 (hS 1).1
  have hsmax : smax < hi := max_lt (hS 0).2 (hS 1).2
  have htmin : lo < tmin := lt_min (hT 0).1 (hT 1).1
  have htmax : tmax < hi := max_lt (hT 0).2 (hT 1).2
  have hg : d < tmin - smax := by
    change d < min (T 0) (T 1) - max (S 0) (S 1)
    rcases le_total (S 0) (S 1) with hs | hs <;>
      rcases le_total (T 0) (T 1) with ht | ht
    · simpa only [min_eq_left ht, max_eq_right hs] using hgap 1 0
    · simpa only [min_eq_right ht, max_eq_right hs] using hgap 1 1
    · simpa only [min_eq_left ht, max_eq_left hs] using hgap 0 0
    · simpa only [min_eq_right ht, max_eq_left hs] using hgap 0 1
  obtain ⟨sL, hsLlo, hsLhi⟩ := exists_rat_btwn hsmin
  obtain ⟨sR, hsRlo, hsRhi⟩ := exists_rat_btwn
    (lt_min hsmax (show smax < tmin - d by linarith))
  have hsRgap : (sR : ℝ) + d < tmin := by
    have hh := hsRhi.trans_le (min_le_right hi (tmin - d))
    linarith
  obtain ⟨tL, htLlo, htLhi⟩ := exists_rat_btwn (max_lt htmin hsRgap)
  obtain ⟨tR, htRlo, htRhi⟩ := exists_rat_btwn htmax
  refine ⟨sL, sR, tL, tR, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨hsLlo.le.trans hx.1, hx.2.trans (hsRhi.trans_le (min_le_left hi (tmin - d))).le⟩
  · intro x hx
    exact ⟨((le_max_left lo ((sR : ℝ) + d)).trans_lt htLlo).le.trans hx.1,
      hx.2.trans htRhi.le⟩
  · have hh := (le_max_right lo ((sR : ℝ) + d)).trans_lt htLlo
    change d ≤ (tL : ℝ) - (sR : ℝ)
    linarith
  · intro k
    fin_cases k
    · exact ⟨hsLhi.trans_le (min_le_left _ _), (le_max_left _ _).trans_lt hsRlo⟩
    · exact ⟨hsLhi.trans_le (min_le_right _ _), (le_max_right _ _).trans_lt hsRlo⟩
  · intro k
    fin_cases k
    · exact ⟨htLhi.trans_le (min_le_left _ _), (le_max_left _ _).trans_lt htRlo⟩
    · exact ⟨htLhi.trans_le (min_le_right _ _), (le_max_right _ _).trans_lt htRlo⟩

end RationalScalarPairWindow

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
local notation "V" => ι → ℝ
local notation "Endpoint" => V × ℝ
local notation "Edge" => Endpoint × Endpoint

/-- Strict original clocks in the retained original scalar interval. -/
def physicalSceneStrictClockRegion (q : RationalScalarPairWindow) : Set Edge :=
  {e | e.1.2 ∈ Ioo (q.val.1 : ℝ) (q.val.2.1 : ℝ) ∧
    e.2.2 ∈ Ioo (q.val.1 : ℝ) (q.val.2.1 : ℝ) ∧ (q.val.2.2 : ℝ) < e.2.2 - e.1.2}

/-- A bounded actual source/target clock box, with its original separate clocks. -/
def physicalSceneClockRadiusBox (R sL sR tL tR : ℝ) : Set Edge :=
  {e | (e.1.2 ∈ Ioo sL sR ∧ e.2.2 ∈ Ioo tL tR) ∧ ‖e.1.1‖ < R ∧ ‖e.2.1‖ < R}

/-- Closed clock bins fit inside the same original scalar-pair window. -/
def physicalSceneClockBinsValid (q : RationalScalarPairWindow) (sL sR tL tR : ℝ) : Prop :=
  Icc sL sR ⊆ Icc (q.val.1 : ℝ) (q.val.2.1 : ℝ) ∧
    Icc tL tR ⊆ Icc (q.val.1 : ℝ) (q.val.2.1 : ℝ) ∧ (q.val.2.2 : ℝ) ≤ tL - sR

/-- Rational closed clock bins and integral spatial radii place every strictly
legal support exchange on one common probability-one event. -/
theorem ae_tagged_strictClock_twoCycle_of_countable_bounded_boxes
    (P : Measure Ω) (tag : Ω → V) (π : Ω → Measure Edge)
    (K : Set V) (c : V → Endpoint → Endpoint → ℝ) (q : RationalScalarPairWindow)
    (hbox : ∀ (N : ℕ) (sL sR tL tR : ℚ),
      physicalSceneClockBinsValid q sL sR tL tR →
      ∀ᵐ ω ∂P, tag ω ∈ K →
        IsTwoCycleMonotoneOn (c (tag ω))
          (physicalSceneClockRadiusBox (N : ℝ) sL sR tL tR)
          ((π ω).support ∩ physicalSceneClockRadiusBox (N : ℝ) sL sR tL tR)) :
    ∀ᵐ ω ∂P, tag ω ∈ K →
      IsTwoCycleMonotoneOn (c (tag ω)) (physicalSceneStrictClockRegion q)
        ((π ω).support ∩ physicalSceneStrictClockRegion q) := by
  classical
  have hall : ∀ᵐ ω ∂P, ∀ (N : ℕ) (sL sR tL tR : ℚ),
      physicalSceneClockBinsValid q sL sR tL tR → tag ω ∈ K →
        IsTwoCycleMonotoneOn (c (tag ω))
          (physicalSceneClockRadiusBox (N : ℝ) sL sR tL tR)
          ((π ω).support ∩ physicalSceneClockRadiusBox (N : ℝ) sL sR tL tR) := by
    apply ae_all_iff.mpr
    intro N
    apply ae_all_iff.mpr
    intro sL
    apply ae_all_iff.mpr
    intro sR
    apply ae_all_iff.mpr
    intro tL
    apply ae_all_iff.mpr
    intro tR
    by_cases hv : physicalSceneClockBinsValid q sL sR tL tR
    · exact (hbox N sL sR tL tR hv).mono fun _ h _ ↦ h
    · exact ae_of_all _ fun _ h ↦ False.elim (hv h)
  filter_upwards [hall] with ω hω htag
  intro x y x' y' hxy hxy' hcross hcross'
  let S : Fin 2 → ℝ := ![x.2, x'.2]
  let T : Fin 2 → ℝ := ![y.2, y'.2]
  have hS (i : Fin 2) : S i ∈ Ioo (q.val.1 : ℝ) (q.val.2.1 : ℝ) := by
    fin_cases i
    · exact hxy.2.1
    · exact hxy'.2.1
  have hT (i : Fin 2) : T i ∈ Ioo (q.val.1 : ℝ) (q.val.2.1 : ℝ) := by
    fin_cases i
    · exact hxy.2.2.1
    · exact hxy'.2.2.1
  have hgap (i j : Fin 2) : (q.val.2.2 : ℝ) < T j - S i := by
    fin_cases i <;> fin_cases j
    · exact hxy.2.2.2
    · exact hcross.2.2
    · exact hcross'.2.2
    · exact hxy'.2.2.2
  obtain ⟨sL, sR, tL, tR, hs, ht, hg, hSb, hTb⟩ :=
    q.exists_physicalScene_rational_clock_bins S T hS hT hgap
  obtain ⟨N, hN⟩ := exists_nat_gt (max (max ‖x.1‖ ‖x'.1‖) (max ‖y.1‖ ‖y'.1‖))
  have hxN : ‖x.1‖ < (N : ℝ) :=
    ((le_max_left ‖x.1‖ ‖x'.1‖).trans (le_max_left _ _)).trans_lt hN
  have hxN' : ‖x'.1‖ < (N : ℝ) :=
    ((le_max_right ‖x.1‖ ‖x'.1‖).trans (le_max_left _ _)).trans_lt hN
  have hyN : ‖y.1‖ < (N : ℝ) :=
    ((le_max_left ‖y.1‖ ‖y'.1‖).trans (le_max_right _ _)).trans_lt hN
  have hyN' : ‖y'.1‖ < (N : ℝ) :=
    ((le_max_right ‖y.1‖ ‖y'.1‖).trans (le_max_right _ _)).trans_lt hN
  have hmono := hω N sL sR tL tR ⟨hs, ht, hg⟩ htag
  exact hmono x y x' y' ⟨hxy.1, ⟨⟨hSb 0, hTb 0⟩, hxN, hyN⟩⟩
    ⟨hxy'.1, ⟨⟨hSb 1, hTb 1⟩, hxN', hyN'⟩⟩
    ⟨⟨hSb 0, hTb 1⟩, hxN, hyN'⟩ ⟨⟨hSb 1, hTb 0⟩, hxN', hyN⟩

end OTSelector.Reconstruction
