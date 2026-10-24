import OTSelector.Reconstruction.SplicedPressureComparison
import OTSelector.Reconstruction.RelativeExpectedPressure

/-!
# Expected pressure after replacing only core edges

The frozen comparison uses the original cost outside the measurable core event.
For relative errors strictly below one, integrability of the original edges
already supplies integrability of the spliced comparison and its actual pressure.
-/

open Set MeasureTheory Matrix

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

/-- A measurable edge event preserves measurability of a spliced edge array. -/
theorem measurable_spliceEdgeCost {Ω ι κ : Type*} [MeasurableSpace Ω]
    (Q : Ω → Set (ι × κ)) (c d : Ω → Matrix ι κ ℝ)
    (hQ : ∀ i j, MeasurableSet {ξ | (i, j) ∈ Q ξ})
    (hc : ∀ i j, Measurable (fun ξ ↦ c ξ i j))
    (hd : ∀ i j, Measurable (fun ξ ↦ d ξ i j)) :
    ∀ i j, Measurable (fun ξ ↦ spliceEdgeCost (Q ξ) (c ξ) (d ξ) i j) := by
  classical
  intro i j
  exact Measurable.ite (hQ i j) (hd i j) (hc i j)

/-- Relative replacement below one transfers integrability from each original edge
without assuming integrability of the frozen cost outside the selected event. -/
theorem integrable_spliceEdgeCost_of_relative {Ω ι κ : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (Q : Ω → Set (ι × κ)) (c d : Ω → Matrix ι κ ℝ)
    (hQ : ∀ i j, MeasurableSet {ξ | (i, j) ∈ Q ξ})
    (hc : ∀ i j, Measurable (fun ξ ↦ c ξ i j))
    (hd : ∀ i j, Measurable (fun ξ ↦ d ξ i j))
    (hci : ∀ i j, Integrable (fun ξ ↦ c ξ i j) P)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hcn : ∀ᵐ ξ ∂P, ∀ i j, 0 ≤ c ξ i j)
    (hlocal : ∀ᵐ ξ ∂P, ∀ i j, (i, j) ∈ Q ξ →
      |c ξ i j - d ξ i j| ≤ ε * d ξ i j) :
    ∀ i j, Integrable (fun ξ ↦ spliceEdgeCost (Q ξ) (c ξ) (d ξ) i j) P := by
  intro i j
  apply ((hci i j).norm.div_const (1 - ε)).mono'
    ((measurable_spliceEdgeCost Q c d hQ hc hd i j).aestronglyMeasurable)
  filter_upwards [hcn, hlocal] with ξ hcnξ hlocalξ
  exact abs_le_div_of_relative_error hε0 hε1
    (spliceEdgeCost_relative (Q ξ) (c ξ) (d ξ) hε0 hcnξ hlocalξ i j)

/-- The spliced actual finite pressure is integrable using only original edge
integrability and a bounded spliced probe. -/
theorem integrable_spliced_perturbedAssignmentValue_div
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {n : ℕ}
    (Q : Ω → Set (Fin n × Fin n)) (c g d h : Ω → Matrix (Fin n) (Fin n) ℝ)
    (t ε G : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hQ : ∀ i j, MeasurableSet {ξ | (i, j) ∈ Q ξ})
    (hc : ∀ i j, Measurable (fun ξ ↦ c ξ i j))
    (hg : ∀ i j, Measurable (fun ξ ↦ g ξ i j))
    (hd : ∀ i j, Measurable (fun ξ ↦ d ξ i j))
    (hh : ∀ i j, Measurable (fun ξ ↦ h ξ i j))
    (hci : ∀ i j, Integrable (fun ξ ↦ c ξ i j) P)
    (hcn : ∀ᵐ ξ ∂P, ∀ i j, 0 ≤ c ξ i j)
    (hlocal : ∀ᵐ ξ ∂P, ∀ i j, (i, j) ∈ Q ξ →
      |c ξ i j - d ξ i j| ≤ ε * d ξ i j)
    (hgb : ∀ᵐ ξ ∂P, ∀ i j, |g ξ i j| ≤ G)
    (hhb : ∀ᵐ ξ ∂P, ∀ i j, (i, j) ∈ Q ξ → |h ξ i j| ≤ G) :
    Integrable (fun ξ ↦ perturbedAssignmentValue (spliceEdgeCost (Q ξ) (c ξ) (d ξ))
      (spliceEdgeCost (Q ξ) (g ξ) (h ξ)) t / n) P := by
  have hdm := measurable_spliceEdgeCost Q c d hQ hc hd
  have hhm := measurable_spliceEdgeCost Q g h hQ hg hh
  have hdi := integrable_spliceEdgeCost_of_relative Q c d hQ hc hd hci hε0 hε1 hcn hlocal
  have hhi (i j : Fin n) : Integrable
      (fun ξ ↦ spliceEdgeCost (Q ξ) (g ξ) (h ξ) i j) P := by
    apply (integrable_const G).mono' (hhm i j).aestronglyMeasurable
    filter_upwards [hgb, hhb] with ξ hgbξ hhbξ
    exact spliceEdgeCost_probe_bound (Q ξ) (g ξ) (h ξ) hgbξ hhbξ i j
  have hi := Probability.integrable_assignmentValue P
    (fun ξ ↦ perturbedEdgeCost (spliceEdgeCost (Q ξ) (c ξ) (d ξ))
      (spliceEdgeCost (Q ξ) (g ξ) (h ξ)) t)
    (fun i j ↦ (hdm i j).add ((hhm i j).const_mul t))
    (fun i j ↦ (hdi i j).add ((hhi i j).const_mul t))
  simpa only [perturbedAssignmentValue, perturbedEdgeCost_zero] using hi.div_const (n : ℝ)

/-- A core-only relative replacement controls the two original global expected
pressures. Both integrability conclusions are produced from the original edge law. -/
theorem expected_spliced_perturbedAssignmentValue_div_abs_sub_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n)
    (Q : Ω → Set (Fin n × Fin n)) (c g d h : Ω → Matrix (Fin n) (Fin n) ℝ)
    (t ε G B : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hB : 0 ≤ B)
    (hQ : ∀ i j, MeasurableSet {ξ | (i, j) ∈ Q ξ})
    (hc : ∀ i j, Measurable (fun ξ ↦ c ξ i j))
    (hg : ∀ i j, Measurable (fun ξ ↦ g ξ i j))
    (hd : ∀ i j, Measurable (fun ξ ↦ d ξ i j))
    (hh : ∀ i j, Measurable (fun ξ ↦ h ξ i j))
    (hci : ∀ i j, Integrable (fun ξ ↦ c ξ i j) P)
    (hcn : ∀ᵐ ξ ∂P, ∀ i j, 0 ≤ c ξ i j)
    (hlocal : ∀ᵐ ξ ∂P, ∀ i j, (i, j) ∈ Q ξ →
      |c ξ i j - d ξ i j| ≤ ε * d ξ i j)
    (hgb : ∀ᵐ ξ ∂P, ∀ i j, |g ξ i j| ≤ G)
    (hhb : ∀ᵐ ξ ∂P, ∀ i j, (i, j) ∈ Q ξ → |h ξ i j| ≤ G)
    (hgh : ∀ᵐ ξ ∂P, ∀ i j, (i, j) ∈ Q ξ → |g ξ i j - h ξ i j| ≤ B) :
    let dQ := fun ξ ↦ spliceEdgeCost (Q ξ) (c ξ) (d ξ)
    let hQ := fun ξ ↦ spliceEdgeCost (Q ξ) (g ξ) (h ξ)
    Integrable (fun ξ ↦ perturbedAssignmentValue (c ξ) (g ξ) t / n) P ∧
      Integrable (fun ξ ↦ perturbedAssignmentValue (dQ ξ) (hQ ξ) t / n) P ∧
      |(∫ ξ, perturbedAssignmentValue (c ξ) (g ξ) t / n ∂P) -
        ∫ ξ, perturbedAssignmentValue (dQ ξ) (hQ ξ) t / n ∂P| ≤
      ε * ((∫ ξ, perturbedAssignmentValue (dQ ξ) (hQ ξ) t / n ∂P) + |t| * G) + |t| * B := by
  have hdi := integrable_spliced_perturbedAssignmentValue_div Q c g d h t ε G hε0 hε1
    hQ hc hg hd hh hci hcn hlocal hgb hhb
  have hcompare := expected_perturbedAssignmentValue_div_abs_sub_le_relative hn c g
    (fun ξ ↦ spliceEdgeCost (Q ξ) (c ξ) (d ξ))
    (fun ξ ↦ spliceEdgeCost (Q ξ) (g ξ) (h ξ)) t ε G B hε0 hε1.le hc hg hdi
    (by
      filter_upwards [hcn, hlocal] with ξ hcnξ hlocalξ
      exact spliceEdgeCost_relative (Q ξ) (c ξ) (d ξ) hε0 hcnξ hlocalξ)
    (by
      filter_upwards [hgb, hhb] with ξ hgbξ hhbξ
      exact spliceEdgeCost_probe_bound (Q ξ) (g ξ) (h ξ) hgbξ hhbξ)
    (by
      filter_upwards [hgh] with ξ hghξ
      exact spliceEdgeCost_probe_error (Q ξ) (g ξ) (h ξ) hB hghξ)
  exact ⟨hcompare.1, hdi, hcompare.2⟩

end OTSelector.Reconstruction
