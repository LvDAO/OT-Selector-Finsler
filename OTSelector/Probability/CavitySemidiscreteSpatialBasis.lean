import OTSelector.Probability.CavitySemidiscreteSpatialRooting
import OTSelector.Transport.CyclicMonotonicity.CountableRectangleSupport

/-!
# A countable spatially bounded basis for actual cycle witnesses
-/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal Classical

noncomputable section
namespace OTSelector.Probability

variable {ι A : Type*} [Fintype ι] [TopologicalSpace A] [SecondCountableTopology A]

/-- A fixed countable source basis whose spatial projections are bounded. -/
def cavitySpatialBasis : Set (Set ((ι → ℝ) × A)) :=
  {U ∈ countableBasis ((ι → ℝ) × A) | ∃ R : ℝ, 0 ≤ R ∧ ∀ s ∈ U, ‖s.1‖ ≤ R}

theorem countable_cavitySpatialBasis : (cavitySpatialBasis (ι := ι) (A := A)).Countable :=
  (countable_countableBasis _).mono (fun _ h ↦ h.1)

/-- Bounding only the spatial coordinate retains a basis of the full marked space. -/
theorem isTopologicalBasis_cavitySpatialBasis :
    IsTopologicalBasis (cavitySpatialBasis (ι := ι) (A := A)) := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro U hU
    exact isOpen_of_mem_countableBasis hU.1
  · intro s U hs hU
    have ho : IsOpen (U ∩ Prod.fst ⁻¹' Metric.ball 0 (‖s.1‖ + 1)) :=
      hU.inter (Metric.isOpen_ball.preimage continuous_fst)
    have hm : s ∈ U ∩ Prod.fst ⁻¹' Metric.ball 0 (‖s.1‖ + 1) :=
      ⟨hs, by simp only [mem_preimage, Metric.mem_ball, dist_zero_right]; linarith⟩
    obtain ⟨V, hV, hsV, hsub⟩ := (isBasis_countableBasis _).exists_subset_of_mem_open hm ho
    refine ⟨V, ⟨hV, ‖s.1‖ + 1, by positivity, ?_⟩, hsV, hsub.trans inter_subset_left⟩
    intro x hx
    exact (show ‖x.1‖ < ‖s.1‖ + 1 by
      simpa only [mem_preimage, Metric.mem_ball, dist_zero_right] using (hsub hx).2).le

theorem nonempty_of_mem_cavitySpatialBasis {U : Set ((ι → ℝ) × A)}
    (hU : U ∈ cavitySpatialBasis) : U.Nonempty := nonempty_of_mem_countableBasis hU.1

/-- Every pair of these source basis sets fits one actual phase cube. -/
theorem exists_phaseCell_of_cavitySpatialBasis
    {U V : Set ((ι → ℝ) × A)} (hU : U ∈ cavitySpatialBasis) (hV : V ∈ cavitySpatialBasis) :
    ∃ K : ℝ, 0 < K ∧ ∃ offset : ι → ℝ,
      ∀ s ∈ U ∪ V, s.1 - offset ∈ cavityGridPhaseCell ι K := by
  obtain ⟨R, hR, hUbound⟩ := hU.2
  obtain ⟨T, hT, hVbound⟩ := hV.2
  let L := max R T
  have hL : 0 ≤ L := hR.trans (le_max_left _ _)
  refine ⟨2 * L + 2, by positivity, fun _ ↦ -L - 1, ?_⟩
  intro s hs
  have hsL : ‖s.1‖ ≤ L := hs.elim
    (fun h ↦ (hUbound s h).trans (le_max_left _ _))
    (fun h ↦ (hVbound s h).trans (le_max_right _ _))
  intro i _
  have hi : |s.1 i| ≤ L := (norm_le_pi_norm s.1 i).trans hsL
  have hilo := (abs_le.mp hi).1
  have hihi := (abs_le.mp hi).2
  change 0 < s.1 i - (-L - 1) ∧ s.1 i - (-L - 1) ≤ 2 * L + 2
  constructor <;> linarith

end OTSelector.Probability
