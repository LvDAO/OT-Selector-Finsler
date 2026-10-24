import OTSelector.PointProcess.LocalConfigurationAtomLimit
import OTSelector.PointProcess.LocalConfigurationTuple

/-!
# Open pair witnesses in the original integer cloud

An open relation witnessed by two occupied sites persists under vague convergence.
For finite original arrays this event is the union of the corresponding label-pair
events. No simplicity or convergence of factorial moment measures is required.
-/

open MeasureTheory Set Function Filter Topology
open scoped BigOperators Classical ENNReal

namespace OTSelector.PointProcess.LocalConfiguration

variable {X : Type*} [MetricSpace X] {base : X}

noncomputable local instance pairWitnessTopology :
    TopologicalSpace (LocalConfiguration base) := vagueTopology base

/-- The original cloud has two occupied sites satisfying a specified pair relation. -/
def HasPairIn (R : Set (X × X)) (c : LocalConfiguration base) : Prop :=
  ∃ x y, multiplicity c x ≠ 0 ∧ multiplicity c y ≠ 0 ∧ (x, y) ∈ R

/-- Open pair witnesses persist without any simplicity premise. -/
theorem isOpen_hasPairIn [ProperSpace X] {R : Set (X × X)} (hR : IsOpen R) :
    IsOpen {c : LocalConfiguration base | HasPairIn R c} := by
  rw [isOpen_iff_mem_nhds]
  rintro c ⟨x, y, hx, hy, hxy⟩
  obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.1 hR (x, y) hxy
  filter_upwards [eventually_exists_atom_near_of_tendsto tendsto_id hx he,
    eventually_exists_atom_near_of_tendsto tendsto_id hy he]
    with d ⟨x', hx', hmx⟩ ⟨y', hy', hmy⟩
  refine ⟨x', y', hmx, hmy, hball ?_⟩
  exact max_lt hx' hy'

section Measure

variable [MeasurableSpace X] [BorelSpace X]

/-- Pair witnesses in the actual tuple are exactly original label-pair witnesses. -/
theorem hasPairIn_ofTuple_iff {n : ℕ} (points : Fin n → X) (R : Set (X × X)) :
    HasPairIn R (ofTuple base points) ↔ ∃ i j, (points i, points j) ∈ R := by
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    obtain ⟨i, rfl⟩ := (multiplicity_ofTuple_ne_zero_iff points x).1 hx
    obtain ⟨j, rfl⟩ := (multiplicity_ofTuple_ne_zero_iff points y).1 hy
    exact ⟨i, j, hxy⟩
  · rintro ⟨i, j, hij⟩
    exact ⟨points i, points j,
      (multiplicity_ofTuple_ne_zero_iff points (points i)).2 ⟨i, rfl⟩,
      (multiplicity_ofTuple_ne_zero_iff points (points j)).2 ⟨j, rfl⟩, hij⟩

/-- The finite original pair union bound, valid on any original sample space. -/
theorem measure_hasPairIn_ofTuple_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (Y : Ω → Fin n → X) (R : Set (X × X)) :
    P {ω | HasPairIn R (ofTuple base (Y ω))} ≤
      ∑ i, ∑ j, P {ω | (Y ω i, Y ω j) ∈ R} := by
  have hset : {ω | HasPairIn R (ofTuple base (Y ω))} =
      ⋃ i, ⋃ j, {ω | (Y ω i, Y ω j) ∈ R} := by
    ext ω
    simp only [mem_ofPred_eq, hasPairIn_ofTuple_iff, mem_iUnion]
  rw [hset]
  exact (measure_iUnion_le _).trans (by
    simpa only [tsum_fintype] using
      ENNReal.tsum_le_tsum (fun i ↦ measure_iUnion_le
        (fun j ↦ {ω | (Y ω i, Y ω j) ∈ R})))

end Measure
end OTSelector.PointProcess.LocalConfiguration
