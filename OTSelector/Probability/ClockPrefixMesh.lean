import Mathlib.Data.Finset.Card
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith

/-!
# Clock Prefix Mesh

Conditions: Monotone real readouts with an indexed cover by brackets and endpoint/target-increment bounds; only the actual point index set is finite in the counting specialization.

Objects: Deterministic error interpolation between anchors, including a true finite prefix-count deviation bound.

Proof detail: Use monotonicity to trap each value between neighboring anchor values and add the target-mesh increment; specialize to counts and distribution increments.

Relation to primary sources: Elementary monotone interpolation analogous to the quantile-grid step in the cited proof. The abstract bracket index need not be finite or globally ordered; the count readout uses a finite point set.

References:
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 2.4, Theorem 2.4.9 proof, pp. 79–80. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=87
-/
/-! Finite deterministic clock meshes control every original prefix count. -/
open Set MeasureTheory
open scoped Classical
noncomputable section
namespace OTSelector.Probability

/-- Monotonicity interpolates endpoint errors with only the reference mass
between the two original thresholds. -/
theorem abs_sub_le_of_monotone_bracket
    (F G : ℝ → ℝ) (hF : Monotone F) (hG : Monotone G)
    {lo hi c a b : ℝ} (hlc : lo ≤ c) (hch : c ≤ hi)
    (hl : |F lo - G lo| ≤ a) (hh : |F hi - G hi| ≤ a)
    (hgap : G hi - G lo ≤ b) : |F c - G c| ≤ a + b := by
  obtain ⟨hll, hlu⟩ := abs_le.mp hl
  obtain ⟨hhl, hhu⟩ := abs_le.mp hh
  have hFl := hF hlc
  have hFh := hF hch
  have hGl := hG hlc
  have hGh := hG hch
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A deterministic family of brackets transfers finitely many threshold
estimates to all thresholds in its covered clock set. -/
theorem abs_sub_le_of_monotone_mesh
    {ι : Type*} (F G : ℝ → ℝ) (hF : Monotone F) (hG : Monotone G)
    (lo hi : ι → ℝ) (S : Set ℝ) (a b : ℝ)
    (hcover : ∀ c ∈ S, ∃ j, lo j ≤ c ∧ c ≤ hi j)
    (hl : ∀ j, |F (lo j) - G (lo j)| ≤ a)
    (hh : ∀ j, |F (hi j) - G (hi j)| ≤ a)
    (hgap : ∀ j, G (hi j) - G (lo j) ≤ b) :
    ∀ c ∈ S, |F c - G c| ≤ a + b := by
  intro c hc
  obtain ⟨j, hjl, hjh⟩ := hcover c hc
  exact abs_sub_le_of_monotone_bracket F G hF hG hjl hjh (hl j) (hh j) (hgap j)

/-- The actual finite prefix count, with multiplicities preserved. -/
def finiteClockPrefixCount {I : Type*} [Fintype I] (clock : I → ℝ) (c : ℝ) : ℕ :=
  (Finset.univ.filter (fun i ↦ clock i ≤ c)).card

theorem monotone_finiteClockPrefixCount {I : Type*} [Fintype I] (clock : I → ℝ) :
    Monotone (finiteClockPrefixCount clock) := by
  intro c d hcd
  apply Finset.card_le_card
  intro i hi
  obtain ⟨him, hic⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨him, hic.trans hcd⟩

/-- Every threshold of the same finite clock sample is controlled by the
mesh errors and the largest original marginal strip mass. -/
theorem finiteClockPrefixCount_mesh_bound
    {I ι : Type*} [Fintype I] (clock : I → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (V : ℝ) (hV : 0 ≤ V)
    (lo hi : ι → ℝ) (S : Set ℝ) (a b : ℝ)
    (horder : ∀ j, lo j ≤ hi j)
    (hcover : ∀ c ∈ S, ∃ j, lo j ≤ c ∧ c ≤ hi j)
    (hl : ∀ j, |(finiteClockPrefixCount clock (lo j) : ℝ) - V * μ.real (Iic (lo j))| ≤ a)
    (hh : ∀ j, |(finiteClockPrefixCount clock (hi j) : ℝ) - V * μ.real (Iic (hi j))| ≤ a)
    (hstrip : ∀ j, μ.real (Ioc (lo j) (hi j)) ≤ b) :
    ∀ c ∈ S, |(finiteClockPrefixCount clock c : ℝ) - V * μ.real (Iic c)| ≤ a + V * b := by
  apply abs_sub_le_of_monotone_mesh
    (fun c ↦ (finiteClockPrefixCount clock c : ℝ))
    (fun c ↦ V * μ.real (Iic c))
    (fun _ _ h ↦ Nat.cast_le.mpr (monotone_finiteClockPrefixCount clock h))
    (fun _ _ h ↦ mul_le_mul_of_nonneg_left (measureReal_mono (Iic_subset_Iic.mpr h)) hV)
    lo hi S a (V * b) hcover hl hh
  intro j
  have heq : μ.real (Iic (hi j)) - μ.real (Iic (lo j)) =
      μ.real (Ioc (lo j) (hi j)) := by
    rw [← Iic_sdiff_Iic]
    exact (measureReal_sdiff (Iic_subset_Iic.mpr (horder j)) measurableSet_Iic).symm
  rw [← mul_sub, heq]
  exact mul_le_mul_of_nonneg_left (hstrip j) hV

end OTSelector.Probability
