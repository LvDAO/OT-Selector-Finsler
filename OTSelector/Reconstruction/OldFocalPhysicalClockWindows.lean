import OTSelector.MeasureTheory.FiniteClockWindowPartition

/-! One fixed finite subdivision covers every old physical inward-clock shell.
It retains the original half-open convention and has uniformly short windows. -/
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1000000

/-- Old physical shells have length `t`, with the same fixed finite window count. -/
def oldPhysicalClockWindowWidth (cap t : ℝ) : ℝ :=
  birthPhysicalClockWindowWidth cap ((8 / 9 : ℝ) * t)

def oldPhysicalClockWindowReference (cap t : ℝ) (ell : ℕ) : ℝ :=
  t + (ell : ℝ) * oldPhysicalClockWindowWidth cap t

def oldPhysicalClockWindowMask (cap t : ℝ) (ell : ℕ) : ℝ → ℝ≥0∞ :=
  birthPhysicalClockWindowMask cap t ((8 / 9 : ℝ) * t) ell

theorem oldPhysicalClockWindow_spec {cap t : ℝ} (hcap : 0 < cap) (ht : 0 < t) :
    0 < birthPhysicalClockWindowCount cap ∧
      0 < oldPhysicalClockWindowWidth cap t ∧
      oldPhysicalClockWindowWidth cap t ≤ cap * t ∧
      (birthPhysicalClockWindowCount cap : ℝ) * oldPhysicalClockWindowWidth cap t = t := by
  have h := birthPhysicalClockWindow_spec hcap (show 0 < (8 / 9 : ℝ) * t by positivity)
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · change birthPhysicalClockWindowWidth cap ((8 / 9 : ℝ) * t) ≤ cap * t
    exact h.2.2.1.trans (by nlinarith)
  · change (birthPhysicalClockWindowCount cap : ℝ) *
      birthPhysicalClockWindowWidth cap ((8 / 9 : ℝ) * t) = t
    nlinarith [h.2.2.2]

theorem measurable_oldPhysicalClockWindowMask (cap t : ℝ) (ell : ℕ) :
    Measurable (oldPhysicalClockWindowMask cap t ell) :=
  measurable_birthPhysicalClockWindowMask cap t _ ell

theorem oldPhysicalClockWindowMask_le_one (cap t : ℝ) (ell : ℕ) (x : ℝ) :
    oldPhysicalClockWindowMask cap t ell x ≤ 1 :=
  birthPhysicalClockWindowMask_le_one cap t _ ell x

theorem oldPhysicalClockWindowMask_ne_zero_iff (cap t : ℝ) (ell : ℕ) (x : ℝ) :
    oldPhysicalClockWindowMask cap t ell x ≠ 0 ↔
      x ∈ Ioc (oldPhysicalClockWindowReference cap t ell)
        (oldPhysicalClockWindowReference cap t ell + oldPhysicalClockWindowWidth cap t) := by
  classical
  have heq : clockGridBand t (birthPhysicalClockWindowWidth cap ((8 / 9 : ℝ) * t)) ell =
      Ioc (oldPhysicalClockWindowReference cap t ell)
        (oldPhysicalClockWindowReference cap t ell + oldPhysicalClockWindowWidth cap t) := by
    ext x
    simp only [clockGridBand, oldPhysicalClockWindowReference, oldPhysicalClockWindowWidth,
      mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by nlinarith⟩
  simp only [oldPhysicalClockWindowMask, birthPhysicalClockWindowMask, heq]
  by_cases hx : x ∈ Ioc (oldPhysicalClockWindowReference cap t ell)
      (oldPhysicalClockWindowReference cap t ell + oldPhysicalClockWindowWidth cap t) <;>
    simp [hx]

/-- The finite half-open windows cover exactly the original old shell. -/
theorem sum_oldPhysicalClockWindowMask {cap t : ℝ} (hcap : 0 < cap) (ht : 0 < t)
    {x : ℝ} (hx : x ∈ Ioc t (2 * t)) :
    (∑ ell ∈ Finset.range (birthPhysicalClockWindowCount cap),
      oldPhysicalClockWindowMask cap t ell x) = 1 := by
  apply sum_birthPhysicalClockWindowMask hcap (show 0 < (8 / 9 : ℝ) * t by positivity)
  constructor <;> linarith [hx.1, hx.2]

/-- Both closed endpoints stay inside the unchanged old physical shell. -/
theorem oldPhysicalClockWindow_inward_bounds {cap t : ℝ} (hcap : 0 < cap) (ht : 0 < t)
    {ell : ℕ} (hell : ell < birthPhysicalClockWindowCount cap)
    {x : ℝ} (hx : x ∈ Icc (oldPhysicalClockWindowReference cap t ell)
      (oldPhysicalClockWindowReference cap t ell + oldPhysicalClockWindowWidth cap t)) :
    x ∈ Icc t (2 * t) := by
  have hs := oldPhysicalClockWindow_spec hcap ht
  have he := clockGridBand_endpoints t hs.2.1.le hell
  rw [hs.2.2.2] at he
  dsimp [oldPhysicalClockWindowReference] at hx
  constructor <;> linarith [hx.1, hx.2, he.1, he.2.1]

/-- The old-side inequality supplies a genuine reference short leg, uniformly
on every physical subwindow, including either original endpoint orientation. -/
theorem oldPhysicalClockWindow_reference_nearLeg_bounds {cap t y d : ℝ}
    (hcap : 0 < cap) (hcapU : cap ≤ 1 / 4) (ht : 0 < t)
    (hy : 0 < y) (hold : y < d)
    {ell : ℕ} (hell : ell < birthPhysicalClockWindowCount cap)
    (hx : y + d ∈ Ioc (oldPhysicalClockWindowReference cap t ell)
      (oldPhysicalClockWindowReference cap t ell + oldPhysicalClockWindowWidth cap t)) :
    t / 4 ≤ oldPhysicalClockWindowReference cap t ell - y ∧
      oldPhysicalClockWindowReference cap t ell - y ≤ 2 * t := by
  have hs := oldPhysicalClockWindow_spec hcap ht
  have hwidth : oldPhysicalClockWindowWidth cap t ≤ t / 4 :=
    hs.2.2.1.trans (by nlinarith)
  have href := oldPhysicalClockWindow_inward_bounds hcap ht hell
    (show oldPhysicalClockWindowReference cap t ell ∈
      Icc (oldPhysicalClockWindowReference cap t ell)
        (oldPhysicalClockWindowReference cap t ell + oldPhysicalClockWindowWidth cap t) by
      exact ⟨le_rfl, le_add_of_nonneg_right hs.2.1.le⟩)
  constructor <;> linarith [hx.1, hx.2, href.1, href.2]

end OTSelector.Reconstruction
