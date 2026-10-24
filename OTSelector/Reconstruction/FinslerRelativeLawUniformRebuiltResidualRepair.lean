import OTSelector.Reconstruction.FinslerRelativeLawResidualEnergyBound
import OTSelector.Reconstruction.FinslerRelativeLawOriginalWindowPopulation
import OTSelector.Finite.OrderedBinGraph

/-!
The actual rebuilt retained and residual original population has a quantitative
original-iid full competitor. Its normalized residual energy depends on the
explicit original residual mass bound, with all geometric constants chosen
before the rebuilt coupling, finite reference cells and window loss.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators Classical

noncomputable section
universe u v w
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- An exact rebuilt coupling of the original probabilities is finite. -/
theorem isFiniteMeasure_of_rebuiltOriginalCoupling
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (χ ξ : Measure (X × X))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hwhole : Vlasov.IsCoupling (χ + ξ) μ ν) : IsFiniteMeasure (χ + ξ) := by
  let _instMapProbability : IsProbabilityMeasure ((χ + ξ).map Prod.fst) := hwhole.1.symm ▸ inferInstance
  let _instWholeProbability : IsProbabilityMeasure (χ + ξ) := Measure.isProbabilityMeasure_of_map Prod.fst
  infer_instance

variable {E : Type u} {M : Type v} {Z : Type w}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace Z]
  [MeasurableSpace.CountablySeparated Z] [MeasurableEq Z]
  {F : ContinuousFinslerNorm E M} {pot : M → ℝ}

/-- The explicit original rebuilt retained/residual population has an actual
original-iid full competitor with quantitative small residual energy. All
geometric constants are fixed before the rebuilt whole coupling and its cells. -/
theorem exists_uniform_original_rebuilt_residual_repair
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
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

    (hdim : 4 < Module.finrank ℝ E - 1) :
    ∃ (T : Type (max u v)) (hT : Fintype T) (C₀ C₁ : ℝ),
      let _inst : Fintype T := hT
      0 ≤ C₀ ∧ 0 ≤ C₁ ∧
      ∀ (χ ξ : Measure (M × M)) (hwhole : Vlasov.IsCoupling (χ + ξ) μ ν),
        let _instWholeFinite : IsFiniteMeasure (χ + ξ) :=
          isFiniteMeasure_of_rebuiltOriginalCoupling μ ν χ ξ hwhole
        (let _inst : MetricSpace M := F.metricSpace
          ∀ᵐ p ∂χ + ξ, pot p.2 - pot p.1 = dist p.1 p.2) →
        ∀ (G : Set Z) (B : ℝ), 0 ≤ B → ξ univ ≤ ENNReal.ofReal B + (μ.map a) Gᶜ →
        let hξ : ξ ≤ χ + ξ := Measure.le_add_left le_rfl
        ∃ D : PopulationTypedCostData (χ + ξ) μ ν T (Module.finrank ℝ E - 1)
          (fun x y ↦ (F.lengthEDist x y).toReal - pot y + pot x),
          let _instMarks : MeasurableSpace (Option (Bool × T)) := ⊤
          ∀ n : ℕ, 0 < n →
            let R := D.refineSubplan ξ hξ
            let β := B + (μ.map a).real Gᶜ
            ∃ K : ℕ,
              (∀ i : Fin n, Measurable (fun sample ↦
                taggedHierarchyAssignment K (R.sourceSample n) (R.targetSample n) sample i)) ∧
              Integrable (D.subplanAttributedEnergy ξ hξ n K) (R.markedLaw n) ∧
              ((n : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) / n) *
                (∫ sample, D.subplanAttributedEnergy ξ hξ n K sample ∂R.markedLaw n) ≤
                C₀ * β ^ (1 - 2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) +
                C₁ * (n : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ) - 1 / 2) * Real.sqrt β := by
  obtain ⟨T, hT, C, Bnd, hC, hBnd, hdata⟩ :=
    exists_uniform_populationTypedCostData_of_calibrated_coupling hF hcomplete hu ha hinj
      horder hA hB hAB hμA hνB hμreg hνreg
  let _instT : Fintype T := hT
  let q := Module.finrank ℝ E - 1
  let C₀ := C * dyadicMatchingConstant q * (Fintype.card T : ℝ) ^ (2 / (q : ℝ))
  let C₁ := Bnd * Real.sqrt (2 * Fintype.card T)
  have hC₀ : 0 ≤ C₀ := mul_nonneg
    (mul_nonneg hC (dyadicMatchingConstant_pos hdim).le) (Real.rpow_nonneg (by positivity) _)
  have hC₁ : 0 ≤ C₁ := mul_nonneg hBnd (Real.sqrt_nonneg _)
  refine ⟨T, hT, C₀, C₁, hC₀, hC₁, ?_⟩
  intro χ ξ hwhole
  let _instWholeFinite : IsFiniteMeasure (χ + ξ) := isFiniteMeasure_of_rebuiltOriginalCoupling μ ν χ ξ hwhole
  dsimp only
  intro hcal G B hB hmass
  let _instMapProbability : IsProbabilityMeasure ((χ + ξ).map Prod.fst) := hwhole.1.symm ▸ inferInstance
  let _instWholeProbability : IsProbabilityMeasure (χ + ξ) := Measure.isProbabilityMeasure_of_map Prod.fst
  let _instLabelProbability : IsProbabilityMeasure (μ.map a) := Measure.isProbabilityMeasure_map ha.aemeasurable
  obtain ⟨D, hDC, hDB⟩ := hdata (χ + ξ) inferInstance hwhole hcal
  let hξ : ξ ≤ χ + ξ := Measure.le_add_left le_rfl
  let β := B + (μ.map a).real Gᶜ
  have hβ : 0 ≤ β := add_nonneg hB measureReal_nonneg
  have hmassβ : ξ univ ≤ ENNReal.ofReal β :=
    original_residual_mass_le_ofReal_add_label_complement (μ.map a) G ξ B hB hmass
  refine ⟨D, ?_⟩
  let _instMarks : MeasurableSpace (Option (Bool × T)) := ⊤
  intro n hn
  obtain ⟨K, hm, hi, he⟩ := D.fixed_subplan_full_competitor_of_mass_bound hdim hn hwhole ξ hξ β hβ hmassβ
  exact ⟨K, hm, hi, by simpa only [hDC, hDB, C₀, C₁, q, β] using he⟩

end OTSelector.Reconstruction
