import OTSelector.Reconstruction.SplicedExpectedPressure

/-!
# Simultaneous pressure replacement on finitely many original tiles

Disjoint edge events may carry different geometric frames and reference costs.
Their replacements are combined in the original global assignment problem,
without splitting or balancing any of its samples.
-/

open Set MeasureTheory Matrix
open scoped BigOperators

noncomputable section
namespace OTSelector.Reconstruction

variable {ι κ Tile : Type*} [Fintype Tile]

/-- Replace the cost on each disjoint tile and retain the original cost elsewhere. -/
def finiteTileSplice (Q : Tile → Set (ι × κ)) (c : Matrix ι κ ℝ)
    (d : Tile → Matrix ι κ ℝ) : Matrix ι κ ℝ := by
  classical
  exact fun i j ↦ c i j + ∑ k, if (i, j) ∈ Q k then d k i j - c i j else 0

/-- On a selected tile the simultaneous replacement is exactly its prescribed cost. -/
theorem finiteTileSplice_on (Q : Tile → Set (ι × κ)) (c : Matrix ι κ ℝ)
    (d : Tile → Matrix ι κ ℝ) (hQ : Pairwise (fun k l ↦ Disjoint (Q k) (Q l)))
    {k : Tile} {i : ι} {j : κ} (hk : (i, j) ∈ Q k) :
    finiteTileSplice Q c d i j = d k i j := by
  classical
  have hsum : (∑ l, if (i, j) ∈ Q l then d l i j - c i j else 0) =
      d k i j - c i j := by
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro l _ hl
      have hnot : (i, j) ∉ Q l := fun h ↦ Set.disjoint_left.mp (hQ hl) h hk
      simp [hnot]
    · simp
  unfold finiteTileSplice
  rw [hsum]
  ring

/-- Outside every tile the simultaneous replacement is exactly the original cost. -/
theorem finiteTileSplice_outside (Q : Tile → Set (ι × κ)) (c : Matrix ι κ ℝ)
    (d : Tile → Matrix ι κ ℝ) {i : ι} {j : κ} (hq : ∀ k, (i, j) ∉ Q k) :
    finiteTileSplice Q c d i j = c i j := by
  classical
  simp [finiteTileSplice, hq]

/-- The finite tile replacement is entrywise measurable for measurable original
costs, tile events and each tile's own reference array. -/
theorem measurable_finiteTileSplice {Ω : Type*} [MeasurableSpace Ω]
    (Q : Ω → Tile → Set (ι × κ)) (c : Ω → Matrix ι κ ℝ)
    (d : Ω → Tile → Matrix ι κ ℝ)
    (hQ : ∀ k i j, MeasurableSet {ξ | (i, j) ∈ Q ξ k})
    (hc : ∀ i j, Measurable (fun ξ ↦ c ξ i j))
    (hd : ∀ k i j, Measurable (fun ξ ↦ d ξ k i j)) :
    ∀ i j, Measurable (fun ξ ↦ finiteTileSplice (Q ξ) (c ξ) (d ξ) i j) := by
  classical
  intro i j
  exact (hc i j).add (Finset.measurable_sum _ (fun k _ ↦
    Measurable.ite (hQ k i j) ((hd k i j).sub (hc i j)) measurable_const))

/-- Simultaneous relative replacement is valid on all edges, including those
outside every original tile. -/
theorem finiteTileSplice_relative (Q : Tile → Set (ι × κ)) (c : Matrix ι κ ℝ)
    (d : Tile → Matrix ι κ ℝ) (hQ : Pairwise (fun k l ↦ Disjoint (Q k) (Q l)))
    {ε : ℝ} (hε : 0 ≤ ε) (hc : ∀ i j, 0 ≤ c i j)
    (hlocal : ∀ k i j, (i, j) ∈ Q k → |c i j - d k i j| ≤ ε * d k i j) :
    ∀ i j, |c i j - finiteTileSplice Q c d i j| ≤ ε * finiteTileSplice Q c d i j := by
  intro i j
  by_cases h : ∃ k, (i, j) ∈ Q k
  · obtain ⟨k, hk⟩ := h
    rw [finiteTileSplice_on Q c d hQ hk]
    exact hlocal k i j hk
  · have hn : ∀ k, (i, j) ∉ Q k := by simpa using h
    rw [finiteTileSplice_outside Q c d hn, sub_self, abs_zero]
    exact mul_nonneg hε (hc i j)

/-- Bounded original and tile probes remain uniformly bounded after replacement. -/
theorem finiteTileSplice_probe_bound (Q : Tile → Set (ι × κ)) (g : Matrix ι κ ℝ)
    (h : Tile → Matrix ι κ ℝ) (hQ : Pairwise (fun k l ↦ Disjoint (Q k) (Q l)))
    {G : ℝ} (hg : ∀ i j, |g i j| ≤ G)
    (hh : ∀ k i j, (i, j) ∈ Q k → |h k i j| ≤ G) :
    ∀ i j, |finiteTileSplice Q g h i j| ≤ G := by
  intro i j
  by_cases he : ∃ k, (i, j) ∈ Q k
  · obtain ⟨k, hk⟩ := he
    rw [finiteTileSplice_on Q g h hQ hk]
    exact hh k i j hk
  · rw [finiteTileSplice_outside Q g h (by simpa using he)]
    exact hg i j

/-- The common local probe error extends to the full original sample problem. -/
theorem finiteTileSplice_probe_error (Q : Tile → Set (ι × κ)) (g : Matrix ι κ ℝ)
    (h : Tile → Matrix ι κ ℝ) (hQ : Pairwise (fun k l ↦ Disjoint (Q k) (Q l)))
    {B : ℝ} (hB : 0 ≤ B)
    (hh : ∀ k i j, (i, j) ∈ Q k → |g i j - h k i j| ≤ B) :
    ∀ i j, |g i j - finiteTileSplice Q g h i j| ≤ B := by
  intro i j
  by_cases he : ∃ k, (i, j) ∈ Q k
  · obtain ⟨k, hk⟩ := he
    rw [finiteTileSplice_on Q g h hQ hk]
    exact hh k i j hk
  · rw [finiteTileSplice_outside Q g h (by simpa using he), sub_self, abs_zero]
    exact hB

/-- Simultaneous finite-tile replacement controls the actual global expected
pressure, using original edge integrability. Individual tiles are not balanced
or separately optimized. -/
theorem expected_finiteTileSplice_pressure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n)
    (Q : Ω → Tile → Set (Fin n × Fin n))
    (c g : Ω → Matrix (Fin n) (Fin n) ℝ)
    (d h : Ω → Tile → Matrix (Fin n) (Fin n) ℝ)
    (t ε G B : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hB : 0 ≤ B)
    (hQ : ∀ k i j, MeasurableSet {ξ | (i, j) ∈ Q ξ k})
    (hdisjoint : ∀ᵐ ξ ∂P, Pairwise (fun k l ↦ Disjoint (Q ξ k) (Q ξ l)))
    (hc : ∀ i j, Measurable (fun ξ ↦ c ξ i j))
    (hg : ∀ i j, Measurable (fun ξ ↦ g ξ i j))
    (hd : ∀ k i j, Measurable (fun ξ ↦ d ξ k i j))
    (hh : ∀ k i j, Measurable (fun ξ ↦ h ξ k i j))
    (hci : ∀ i j, Integrable (fun ξ ↦ c ξ i j) P)
    (hcn : ∀ᵐ ξ ∂P, ∀ i j, 0 ≤ c ξ i j)
    (hlocal : ∀ᵐ ξ ∂P, ∀ k i j, (i, j) ∈ Q ξ k →
      |c ξ i j - d ξ k i j| ≤ ε * d ξ k i j)
    (hgb : ∀ᵐ ξ ∂P, ∀ i j, |g ξ i j| ≤ G)
    (hhb : ∀ᵐ ξ ∂P, ∀ k i j, (i, j) ∈ Q ξ k → |h ξ k i j| ≤ G)
    (hgh : ∀ᵐ ξ ∂P, ∀ k i j, (i, j) ∈ Q ξ k → |g ξ i j - h ξ k i j| ≤ B) :
    let dQ := fun ξ ↦ finiteTileSplice (Q ξ) (c ξ) (d ξ)
    let hQ := fun ξ ↦ finiteTileSplice (Q ξ) (g ξ) (h ξ)
    Integrable (fun ξ ↦ perturbedAssignmentValue (c ξ) (g ξ) t / n) P ∧
      Integrable (fun ξ ↦ perturbedAssignmentValue (dQ ξ) (hQ ξ) t / n) P ∧
      |(∫ ξ, perturbedAssignmentValue (c ξ) (g ξ) t / n ∂P) -
        ∫ ξ, perturbedAssignmentValue (dQ ξ) (hQ ξ) t / n ∂P| ≤
      ε * ((∫ ξ, perturbedAssignmentValue (dQ ξ) (hQ ξ) t / n ∂P) + |t| * G) + |t| * B := by
  let dQ := fun ξ ↦ finiteTileSplice (Q ξ) (c ξ) (d ξ)
  let hQ' := fun ξ ↦ finiteTileSplice (Q ξ) (g ξ) (h ξ)
  have hdm := measurable_finiteTileSplice Q c d hQ hc hd
  have hhm := measurable_finiteTileSplice Q g h hQ hg hh
  have hrel : ∀ᵐ ξ ∂P, ∀ i j, |c ξ i j - dQ ξ i j| ≤ ε * dQ ξ i j := by
    filter_upwards [hdisjoint, hcn, hlocal] with ξ hdis hnon hloc
    exact finiteTileSplice_relative (Q ξ) (c ξ) (d ξ) hdis hε0 hnon hloc
  have hbound : ∀ᵐ ξ ∂P, ∀ i j, |hQ' ξ i j| ≤ G := by
    filter_upwards [hdisjoint, hgb, hhb] with ξ hdis hgbξ hhbξ
    exact finiteTileSplice_probe_bound (Q ξ) (g ξ) (h ξ) hdis hgbξ hhbξ
  have herr : ∀ᵐ ξ ∂P, ∀ i j, |g ξ i j - hQ' ξ i j| ≤ B := by
    filter_upwards [hdisjoint, hgh] with ξ hdis hghξ
    exact finiteTileSplice_probe_error (Q ξ) (g ξ) (h ξ) hdis hB hghξ
  have hdi (i j : Fin n) : Integrable (fun ξ ↦ dQ ξ i j) P := by
    apply ((hci i j).norm.div_const (1 - ε)).mono' (hdm i j).aestronglyMeasurable
    filter_upwards [hrel] with ξ hrelξ
    exact abs_le_div_of_relative_error hε0 hε1 (hrelξ i j)
  have hhi (i j : Fin n) : Integrable (fun ξ ↦ hQ' ξ i j) P := by
    apply (integrable_const G).mono' (hhm i j).aestronglyMeasurable
    filter_upwards [hbound] with ξ hboundξ
    exact hboundξ i j
  have hvalue : Integrable (fun ξ ↦ perturbedAssignmentValue (dQ ξ) (hQ' ξ) t / n) P := by
    have hi := Probability.integrable_assignmentValue P
      (fun ξ ↦ perturbedEdgeCost (dQ ξ) (hQ' ξ) t)
      (fun i j ↦ (hdm i j).add ((hhm i j).const_mul t))
      (fun i j ↦ (hdi i j).add ((hhi i j).const_mul t))
    simpa only [perturbedAssignmentValue, perturbedEdgeCost_zero] using hi.div_const (n : ℝ)
  have hb := expected_perturbedAssignmentValue_div_abs_sub_le_relative hn c g dQ hQ'
    t ε G B hε0 hε1.le hc hg hvalue hrel hbound herr
  exact ⟨hb.1, hvalue, hb.2⟩

end OTSelector.Reconstruction
