import OTSelector.Reconstruction.RelativePressureComparison

/-!
# Local cost replacement inside the original global assignment problem

Only edges in the chosen core use the frozen cost and probe. Every other edge
retains its original cost and probe, so all assignments remain feasible and the
relative comparison applies to the original global minimum.
-/

open Set Matrix

noncomputable section
namespace OTSelector.Reconstruction

/-- Replace the original cost only on the selected edge event. -/
def spliceEdgeCost {ι κ : Type*} (Q : Set (ι × κ)) (c d : Matrix ι κ ℝ) : Matrix ι κ ℝ := by
  classical
  exact fun i j ↦ if (i, j) ∈ Q then d i j else c i j

@[simp] theorem spliceEdgeCost_of_mem {ι κ : Type*} {Q : Set (ι × κ)}
    (c d : Matrix ι κ ℝ) {i j} (h : (i, j) ∈ Q) : spliceEdgeCost Q c d i j = d i j := by
  simp [spliceEdgeCost, h]

@[simp] theorem spliceEdgeCost_of_notMem {ι κ : Type*} {Q : Set (ι × κ)}
    (c d : Matrix ι κ ℝ) {i j} (h : (i, j) ∉ Q) : spliceEdgeCost Q c d i j = c i j := by
  simp [spliceEdgeCost, h]

/-- Relative error below one controls the replacement cost by the original cost. -/
theorem abs_le_div_of_relative_error {c d ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hrel : |c - d| ≤ ε * d) : |d| ≤ |c| / (1 - ε) := by
  apply (le_div_iff₀ (sub_pos.mpr hε1)).mpr
  have ht : |d| ≤ |c - d| + |c| := by
    simpa only [sub_zero, abs_sub_comm d c] using abs_sub_le d c 0
  have hd := mul_le_mul_of_nonneg_left (le_abs_self d) hε0
  nlinarith only [ht, hrel, hd]

/-- The local relative estimate extends to all edges because the nonnegative
original cost is retained exactly outside the core. -/
theorem spliceEdgeCost_relative {ι κ : Type*} (Q : Set (ι × κ))
    (c d : Matrix ι κ ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ∀ i j, 0 ≤ c i j)
    (hlocal : ∀ i j, (i, j) ∈ Q → |c i j - d i j| ≤ ε * d i j) :
    ∀ i j, |c i j - spliceEdgeCost Q c d i j| ≤ ε * spliceEdgeCost Q c d i j := by
  intro i j
  by_cases hq : (i, j) ∈ Q
  · simpa only [spliceEdgeCost_of_mem c d hq] using hlocal i j hq
  · simpa only [spliceEdgeCost_of_notMem c d hq, sub_self, abs_zero]
      using mul_nonneg hε (hc i j)

/-- Keeping the original probe off the core retains the same uniform probe bound. -/
theorem spliceEdgeCost_probe_bound {ι κ : Type*} (Q : Set (ι × κ))
    (g h : Matrix ι κ ℝ) {G : ℝ}
    (hg : ∀ i j, |g i j| ≤ G)
    (hh : ∀ i j, (i, j) ∈ Q → |h i j| ≤ G) :
    ∀ i j, |spliceEdgeCost Q g h i j| ≤ G := by
  intro i j
  by_cases hq : (i, j) ∈ Q
  · simpa only [spliceEdgeCost_of_mem g h hq] using hh i j hq
  · simpa only [spliceEdgeCost_of_notMem g h hq] using hg i j

/-- Probe error vanishes identically off the chosen core event. -/
theorem spliceEdgeCost_probe_error {ι κ : Type*} (Q : Set (ι × κ))
    (g h : Matrix ι κ ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hlocal : ∀ i j, (i, j) ∈ Q → |g i j - h i j| ≤ B) :
    ∀ i j, |g i j - spliceEdgeCost Q g h i j| ≤ B := by
  intro i j
  by_cases hq : (i, j) ∈ Q
  · simpa only [spliceEdgeCost_of_mem g h hq] using hlocal i j hq
  · simpa only [spliceEdgeCost_of_notMem g h hq, sub_self, abs_zero] using hB

/-- Replacing only core edges compares the same two global assignment minima;
no restriction requires all sample pairs or optimal assignment edges to lie in the core. -/
theorem spliced_perturbedAssignmentValue_div_abs_sub_le {n : ℕ} (hn : 0 < n)
    (Q : Set (Fin n × Fin n)) (c g d h : Matrix (Fin n) (Fin n) ℝ)
    (t ε G B : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hB : 0 ≤ B)
    (hc : ∀ i j, 0 ≤ c i j)
    (hlocal : ∀ i j, (i, j) ∈ Q → |c i j - d i j| ≤ ε * d i j)
    (hg : ∀ i j, |g i j| ≤ G)
    (hh : ∀ i j, (i, j) ∈ Q → |h i j| ≤ G)
    (hgh : ∀ i j, (i, j) ∈ Q → |g i j - h i j| ≤ B) :
    |perturbedAssignmentValue c g t / n -
      perturbedAssignmentValue (spliceEdgeCost Q c d) (spliceEdgeCost Q g h) t / n| ≤
      ε * (perturbedAssignmentValue (spliceEdgeCost Q c d) (spliceEdgeCost Q g h) t / n +
        |t| * G) + |t| * B :=
  perturbedAssignmentValue_div_abs_sub_le_relative hn c g _ _ t ε G B hε0 hε1
    (spliceEdgeCost_relative Q c d hε0 hc hlocal)
    (spliceEdgeCost_probe_bound Q g h hg hh) (spliceEdgeCost_probe_error Q g h hB hgh)

end OTSelector.Reconstruction
