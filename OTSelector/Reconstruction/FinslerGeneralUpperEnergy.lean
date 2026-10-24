import OTSelector.Reconstruction.FinslerPopulationWholePairTypes
import OTSelector.Reconstruction.PopulationTypedOptimalEnergy
import OTSelector.Reconstruction.PopulationTypedSubplanEnergy

/-!
# Uniform original Finsler assignment and tilted optimal energy

The finite complete calibrated atlas, original RN marking and distribution-free
cube hierarchy produce the energy bound directly from the physical populations.
The constant is fixed before the sample size and before a bounded probe tilt.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold Metric Matrix OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators Classical
noncomputable section
universe u v w
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

variable {E : Type u} {M : Type v} {Z : Type w}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace Z]
  [MeasurableSpace.CountablySeparated Z] [MeasurableEq Z]
  {F : ContinuousFinslerNorm E M} {pot : M → ℝ}

/-- A complete smooth strongly convex Finsler population in dimension at least
six has uniformly bounded microscopic assignment pressure and actual base energy
on the entire measurable fractional tilted optimal face. -/
theorem exists_uniform_original_finsler_energy
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 pot)
    {a : M → Z} (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain pot ↦ (a x.val, pot x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain pot, ∀ y ∈ F.potentialRegularDomain pot,
        (a x = a y ∧ pot x ≤ pot y) ↔ pot y - pot x = dist x y)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain pot)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain pot)
    (π : Measure (M × M)) [IsFiniteMeasure π] (hπ : Vlasov.IsCoupling π μ ν)
    (hcal : let _inst : MetricSpace M := F.metricSpace
      ∀ᵐ p ∂π, pot p.2 - pot p.1 = dist p.1 p.2) :
    let q := Module.finrank ℝ E - 1
    let cost := fun x y ↦ (F.lengthEDist x y).toReal - pot y + pot x
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      let P₀ := (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
      let c := fun ξ : (Fin n → M) × (Fin n → M) ↦
        fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (ξ.1 i) (ξ.2 j);
      (Integrable (fun ξ ↦ perturbedAssignmentValue (c ξ) 0 0 / n) P₀ ∧
        (∫ ξ, perturbedAssignmentValue (c ξ) 0 0 / n ∂P₀) ≤ C) ∧
      ∀ (probe : M → M → ℝ) (τ G : ℝ),
        (∀ᵐ p ∂μ.prod ν, |probe p.1 p.2| ≤ G) →
        ∀ W : ((Fin n → M) × (Fin n → M)) → Matrix (Fin n) (Fin n) ℝ,
          (∀ i j, Measurable (fun ξ ↦ W ξ i j)) →
          (∀ᵐ ξ ∂P₀, OptimalFractionalAssignment
            (perturbedEdgeCost (c ξ) (fun i j ↦ probe (ξ.1 i) (ξ.2 j)) τ) (W ξ)) →
          Integrable (fun ξ ↦ fractionalAssignmentCost (c ξ) (W ξ) / n) P₀ ∧
          (∫ ξ, fractionalAssignmentCost (c ξ) (W ξ) / n ∂P₀) ≤ C + 2 * |τ| * G := by
  obtain ⟨T, hT, ⟨D⟩⟩ := exists_populationTypedCostData_of_calibrated_coupling hF hcomplete
    hu ha hinj horder hA hB hAB hμA hνB hμreg hνreg π hπ hcal
  let _instT : Fintype T := hT
  let _instMeasurableT : MeasurableSpace (Option T) := ⊤
  have hq : 4 < Module.finrank ℝ E - 1 := by omega
  let C : ℝ := D.quadraticConstant * dyadicMatchingConstant (Module.finrank ℝ E - 1) *
      (Fintype.card (Option T) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) +
    D.globalBound * Real.sqrt (2 * Fintype.card (Option T))
  have hC : 0 ≤ C := add_nonneg
    (mul_nonneg (mul_nonneg D.quadratic_nonneg (dyadicMatchingConstant_pos hq).le)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (mul_nonneg D.bound_nonneg (Real.sqrt_nonneg _))
  refine ⟨C + 1, by linarith, ?_⟩
  intro n hn
  have hzero := D.original_scaled_pressure_uniform hq hn hπ
  refine ⟨⟨hzero.1, hzero.2.trans (by dsimp [C]; linarith)⟩, ?_⟩
  intro probe τ G hg W hW hopt
  have h := D.original_tilted_optimal_energy_uniform hq hn hπ probe τ G hg W hW hopt
  exact ⟨h.1, h.2.trans (by dsimp [C]; linarith)⟩

end OTSelector.Reconstruction
