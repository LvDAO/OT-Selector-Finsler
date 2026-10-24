import OTSelector.Probability.CavitySemidiscreteTargetBlockPacking
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Exact averaging over translated cubic grids

The half-open cube is an actual fundamental domain for the coordinate lattice.
Its periodization identity converts finite disjoint-source exchange bounds into
an integral bound for all translated cycle witnesses.
-/

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable (ι : Type*) [Fintype ι]

/-- A phase cell for the coordinate lattice of spacing `K`. -/
def cavityGridPhaseCell (K : ℝ) : Set (ι → ℝ) :=
  Set.pi Set.univ (fun _ ↦ Set.Ioc 0 K)

/-- Coordinatewise translations by integer multiples of the grid spacing. -/
abbrev CavityGridLattice (K : ℝ) := ι → AddSubgroup.zmultiples K

theorem measurableSet_cavityGridPhaseCell (K : ℝ) :
    MeasurableSet (cavityGridPhaseCell ι K) :=
  MeasurableSet.pi (Set.to_countable _) (fun _ _ ↦ measurableSet_Ioc)

instance cavityGrid_vaddInvariantMeasure (K : ℝ) :
    VAddInvariantMeasure (CavityGridLattice ι K) (ι → ℝ) volume := by
  refine ⟨fun g s _ ↦ ?_⟩
  change volume ((fun x : ι → ℝ ↦ (fun i ↦ (g i : ℝ)) + x) ⁻¹' s) = volume s
  exact measure_preimage_add volume (fun i ↦ (g i : ℝ)) s

omit [Fintype ι] in
/-- Each point has exactly one coordinate-lattice translate in the phase cell. -/
theorem existsUnique_vadd_mem_cavityGridPhaseCell (K : ℝ) (hK : 0 < K) (x : ι → ℝ) :
    ∃! g : CavityGridLattice ι K, g +ᵥ x ∈ cavityGridPhaseCell ι K := by
  classical
  have hex : ∀ i, ∃! g : AddSubgroup.zmultiples K, (g : ℝ) + x i ∈ Ioc 0 K := by
    intro i
    have hb : Bijective (codRestrict (fun n : ℤ ↦ n • K) (AddSubgroup.zmultiples K) _) :=
      (Equiv.ofInjective (fun n : ℤ ↦ n • K) (zsmul_left_strictMono hK).injective).bijective
    refine hb.existsUnique_iff.2 ?_
    simpa only [add_comm (x i), zero_add] using! existsUnique_add_zsmul_mem_Ioc hK (x i) 0
  choose g hg huniq using hex
  refine ⟨g, ?_, ?_⟩
  · exact fun i _ ↦ hg i
  · intro g' hg'
    funext i
    exact huniq i (g' i) (hg' i (mem_univ i))

/-- The coordinate phase cell is an actual fundamental domain for Lebesgue measure. -/
theorem isAddFundamentalDomain_cavityGridPhaseCell (K : ℝ) (hK : 0 < K) :
    IsAddFundamentalDomain (CavityGridLattice ι K) (cavityGridPhaseCell ι K) volume :=
  IsAddFundamentalDomain.mk' (measurableSet_cavityGridPhaseCell ι K).nullMeasurableSet
    (existsUnique_vadd_mem_cavityGridPhaseCell ι K hK)

/-- The coarse cube based at a spatial root. -/
def cavityGridCube (K : ℝ) (z : ι → ℝ) : Set (ι → ℝ) :=
  {x | x - z ∈ cavityGridPhaseCell ι K}

omit [Fintype ι] in
/-- Cubes from a single shifted lattice are pointwise disjoint, including boundaries. -/
theorem pairwise_disjoint_cavityGridCube (K : ℝ) (hK : 0 < K) (z : ι → ℝ) :
    Pairwise (fun g h : CavityGridLattice ι K ↦
      Disjoint (cavityGridCube ι K (g +ᵥ z)) (cavityGridCube ι K (h +ᵥ z))) := by
  intro g h hne
  apply Set.disjoint_left.2
  intro x hxg hxh
  have heqv (v : CavityGridLattice ι K) : -v +ᵥ (x - z) = x - (v +ᵥ z) := by
    ext i
    change -(v i : ℝ) + (x i - z i) = x i - ((v i : ℝ) + z i)
    ring
  have heq : -g = -h := (existsUnique_vadd_mem_cavityGridPhaseCell ι K hK (x - z)).unique
    (by rw [heqv]; exact hxg) (by rw [heqv]; exact hxh)
  exact hne (neg_injective heq)

theorem volume_cavityGridPhaseCell (K : ℝ) :
    volume (cavityGridPhaseCell ι K) = ENNReal.ofReal K ^ Fintype.card ι := by
  simp only [cavityGridPhaseCell, Real.volume_pi_Ioc, sub_zero, Finset.prod_const,
    Finset.card_univ]

/-- Averaging the actual lattice translates over one phase cell counts every spatial
root exactly once. -/
theorem lintegral_cavityGrid_periodization (K : ℝ) (hK : 0 < K)
    (W : (ι → ℝ) → ℝ≥0∞) (hW : Measurable W) :
    (∫⁻ z in cavityGridPhaseCell ι K, ∑' g : CavityGridLattice ι K, W (g +ᵥ z)) =
      ∫⁻ z, W z := by
  have hm : ∀ g : CavityGridLattice ι K,
      AEMeasurable (fun z ↦ W (g +ᵥ z)) (volume.restrict (cavityGridPhaseCell ι K)) :=
    fun g ↦ (hW.comp (measurable_const_vadd g)).aemeasurable
  rw [lintegral_tsum hm]
  exact (isAddFundamentalDomain_cavityGridPhaseCell ι K hK).lintegral_eq_tsum'' W |>.symm

/-- Bounds for every finite packing imply a spatial integral bound, with the exact
phase-cell volume factor. -/
theorem lintegral_le_of_cavityGrid_finite_packing (K : ℝ) (hK : 0 < K)
    (W : (ι → ℝ) → ℝ≥0∞) (hW : Measurable W) (B : ℝ≥0∞)
    (hpack : ∀ z ∈ cavityGridPhaseCell ι K, ∀ s : Finset (CavityGridLattice ι K),
      ∑ g ∈ s, W (g +ᵥ z) ≤ B) :
    (∫⁻ z, W z) ≤ B * ENNReal.ofReal K ^ Fintype.card ι := by
  rw [← lintegral_cavityGrid_periodization ι K hK W hW]
  calc
    _ ≤ ∫⁻ _ in cavityGridPhaseCell ι K, B := by
      apply setLIntegral_mono' (measurableSet_cavityGridPhaseCell ι K)
      intro z hz
      exact ENNReal.summable.tsum_le_of_sum_le (hpack z hz)
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ, volume_cavityGridPhaseCell]

end OTSelector.Probability
