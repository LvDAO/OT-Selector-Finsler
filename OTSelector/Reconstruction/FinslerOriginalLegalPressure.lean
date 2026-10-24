import OTSelector.Reconstruction.FinslerOriginalIIDCosts
import OTSelector.Reconstruction.FinslerOriginalLegalTypes
import OTSelector.Reconstruction.MarkedStationaryValueLegalTypes
import OTSelector.Reconstruction.MarkedStationaryValuePhysicalRepairLimit
import OTSelector.Geometry.Finsler.HopfRinow
import OTSelector.Transport.Coupling.OptimalPlanExistence

/-!
# Original iid physical pressure from the actual clock-legal pressure

The calibrated original coupling determines its own scalar bins. Their RN
marking gives a square-root legal-cardinality deficit on the unchanged physical
iid arrays. Completing the actual legal optimum in the original physical graph
therefore has vanishing normalized cost when `q > 4`.
-/

open Set Function Matrix MeasureTheory Manifold OTSelector.Geometry Filter
open scoped Topology ContDiff ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]

/-- Expected full physical assignment cost, normalized by the original count. -/
def finslerOriginalIIDPressure (F : ContinuousFinslerNorm E M) (μ ν : Measure M)
    (u : M → ℝ) (g : M × M → ℝ) (scale t : ℝ) (n : ℕ) : ℝ :=
  (∫ ξ : (Fin n → M) × (Fin n → M),
    perturbedAssignmentValue (finslerOriginalSampleCost F u scale ξ)
      (originalSampleProbe g ξ) t
    ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))) / (n : ℝ)

/-- Expected actual maximum-cardinality optimum under the original strict clock
order, with the same endpoints, physical costs and sample-size normalization. -/
def finslerOriginalIIDLegalPressure (F : ContinuousFinslerNorm E M) (μ ν : Measure M)
    (u : M → ℝ) (g : M × M → ℝ) (scale t : ℝ) (n : ℕ) : ℝ :=
  (∫ ξ : (Fin n → M) × (Fin n → M),
    PartialMatching.legalMaximumValue
      (scalarClockLegalGraph (fun i ↦ u (ξ.1 i)) (fun j ↦ u (ξ.2 j)))
      (perturbedEdgeCost (finslerOriginalSampleCost F u scale ξ)
        (originalSampleProbe g ξ) t)
    ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))) / (n : ℝ)

/-- The original calibrated compact-support problem supplies its own count and
physical cost constants. The estimate is uniform in sample size, nonnegative
scaling and tilt; it imposes no realized sample balance. -/
theorem exists_finsler_originalIID_legal_pressure_comparison [SecondCountableTopology M]
    (F : ContinuousFinslerNorm E M)
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (π : Measure (M × M)) [IsFiniteMeasure π] (hπ : Vlasov.IsCoupling π μ ν)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) {u : M → ℝ}
    (hu : let _instOriginalLegalPressureMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (hcal : ∀ᵐ p ∂π, (F.lengthEDist p.1 p.2).toReal = u p.2 - u p.1)
    {g : M × M → ℝ} (hg : Measurable g) (G : ℝ≥0) (hgb : ∀ p, |g p| ≤ G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, ∀ scale t : ℝ, 0 ≤ scale →
      finslerOriginalIIDPressure F μ ν u g scale t n ≤
        finslerOriginalIIDLegalPressure F μ ν u g scale t n +
          C * (scale * D + |t| * (G : ℝ)) * Real.sqrt (n : ℝ) / (n : ℝ) := by
  let _instOriginalLegalPressureProofMetric : MetricSpace M := F.metricSpace
  obtain ⟨gap, hgap, hclock, bins, _⟩ :=
    exists_finsler_original_legal_scalar_types π hπ hA hB hAB hμ hν hu hcal
  let _instOriginalLegalPressureTags :
      MeasurableSpace (Option (Unit × Fin bins.count × Fin bins.count)) := ⊤
  have hsource : ∀ᵐ p ∂π, p.1 ∈ A :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [hπ.1]; exact hμ)
  have htarget : ∀ᵐ p ∂π, p.2 ∈ B :=
    ae_of_ae_map measurable_snd.aemeasurable (by rw [hπ.2]; exact hν)
  have hI : ∀ᵐ p ∂π, u p.1 ∈ u '' A ∪ u '' B ∧ u p.2 ∈ u '' A ∪ u '' B := by
    filter_upwards [hsource, htarget] with p hs ht
    exact ⟨Or.inl ⟨p.1, hs, rfl⟩, Or.inr ⟨p.2, ht, rfl⟩⟩
  let C : ℝ := (1 / 2 : ℝ) * Real.sqrt
    (2 * (Fintype.card (Option (Unit × Fin bins.count × Fin bins.count)) : ℝ))
  obtain ⟨D, hD, hbounds⟩ := exists_finsler_originalIID_edge_bound F μ ν hA hB hμ hν hu G hgb
  refine ⟨C, by dsimp [C]; positivity, D, hD, ?_⟩
  intro n scale t hscale
  let P := (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
  let c := fun ξ : (Fin n → M) × (Fin n → M) ↦ finslerOriginalSampleCost F u scale ξ
  let probe := fun ξ : (Fin n → M) × (Fin n → M) ↦ originalSampleProbe g ξ
  let allowed := fun ξ : (Fin n → M) × (Fin n → M) ↦
    scalarClockLegalGraph (fun i ↦ u (ξ.1 i)) (fun j ↦ u (ξ.2 j))
  have hallowed (S) : MeasurableSet {ξ | allowed ξ = S} :=
    measurableSet_scalarClockLegalGraph_eq
      (fun i (ξ : (Fin n → M) × (Fin n → M)) ↦ u (ξ.1 i))
      (fun j (ξ : (Fin n → M) × (Fin n → M)) ↦ u (ξ.2 j))
      (fun _ ↦ hu.continuous.measurable.comp (by fun_prop))
      (fun _ ↦ hu.continuous.measurable.comp (by fun_prop)) S
  have hc : ∀ i j, Measurable (fun ξ ↦ c ξ i j) :=
    measurable_finslerOriginalSampleCost F hu scale n
  have hp : ∀ i j, Measurable (fun ξ ↦ probe ξ i j) := measurable_originalSampleProbe hg n
  have hbound := hbounds n scale t hscale
  have hB0 : 0 ≤ scale * D + |t| * (G : ℝ) := by positivity
  have hphys := integrable_assignmentValue_of_ae_bound P c probe t hc hp hB0 hbound
  have hlegal := integrable_legalMaximumValue_of_ae_bound P allowed hallowed
    (fun ξ ↦ perturbedEdgeCost (c ξ) (probe ξ) t)
    (fun i j ↦ (hc i j).add ((hp i j).const_mul t)) hB0 hbound
  have hmissing := scalarBinPopulationTypes_integral_legalMaximumCard_defect_nat
    bins hgap (fun _ : M × M ↦ ()) u u π μ ν hπ measurable_const
    hu.continuous.measurable hu.continuous.measurable hI hclock n
  exact integral_assignmentValue_le_legalMaximumValue_add_sqrt P allowed c probe t
    (scale * D + |t| * (G : ℝ)) C hB0
    (hbound.mono fun _ hξ i j ↦ (le_abs_self _).trans (hξ i j))
    hphys hlegal hmissing.1 hmissing.2

/-- In the high-dimensional regime the original physical completion has a
nonnegative, explicit vanishing error. Both pressures use the unchanged iid law. -/
theorem exists_finsler_originalIID_legal_pressure_vanishing_error [SecondCountableTopology M]
    (F : ContinuousFinslerNorm E M)
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (π : Measure (M × M)) [IsFiniteMeasure π] (hπ : Vlasov.IsCoupling π μ ν)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) {u : M → ℝ}
    (hu : let _instOriginalLegalVanishingMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (hcal : ∀ᵐ p ∂π, (F.lengthEDist p.1 p.2).toReal = u p.2 - u p.1)
    {g : M × M → ℝ} (hg : Measurable g) (G : ℝ≥0) (hgb : ∀ p, |g p| ≤ G)
    {q : ℝ} (hq : 4 < q) (t : ℝ) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (𝓝 0) ∧
      ∀ n, finslerOriginalIIDPressure F μ ν u g
          (((n + 1 : ℕ) : ℝ) ^ (2 / q)) t (n + 1) ≤
        finslerOriginalIIDLegalPressure F μ ν u g
          (((n + 1 : ℕ) : ℝ) ^ (2 / q)) t (n + 1) + error n := by
  obtain ⟨C, hC, D, hD, hcomp⟩ :=
    exists_finsler_originalIID_legal_pressure_comparison F μ ν π hπ hA hB hAB hμ hν
      hu hcal hg G hgb
  refine ⟨physicalLegalRepairError q C D (|t| * (G : ℝ)),
    fun n ↦ physicalLegalRepairError_nonneg hC hD.le (by positivity) n,
    tendsto_physicalLegalRepairError_zero hq C D (|t| * (G : ℝ)), ?_⟩
  intro n
  exact hcomp (n + 1) _ t (by positivity)

/-- Completeness supplies the countable topology, and the manuscript's `d ≥ 6`
supplies the required exponent. No geometric condition on selected directions
or prescribed balance of the source and target populations is added. -/
theorem exists_complete_finsler_originalIID_legal_pressure_vanishing_error
    (F : ContinuousFinslerNorm E M)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (π : Measure (M × M)) [IsFiniteMeasure π] (hπ : Vlasov.IsCoupling π μ ν)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) {u : M → ℝ}
    (hu : let _instCompleteOriginalLegalMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (hcal : ∀ᵐ p ∂π, (F.lengthEDist p.1 p.2).toReal = u p.2 - u p.1)
    {g : M × M → ℝ} (hg : Measurable g) (G : ℝ≥0) (hgb : ∀ p, |g p| ≤ G) (t : ℝ) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (𝓝 0) ∧
      ∀ n, finslerOriginalIIDPressure F μ ν u g
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) t (n + 1) ≤
        finslerOriginalIIDLegalPressure F μ ν u g
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) t (n + 1) +
          error n := by
  let _instCompleteOriginalLegalProofMetric : MetricSpace M := F.metricSpace
  let _instCompleteOriginalLegalProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instCompleteOriginalLegalSecondCountable : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace _instCompleteOriginalLegalProper
  have hq : 4 < (Module.finrank ℝ E : ℝ) - 1 := by
    have hd : (6 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hdim
    linarith
  exact exists_finsler_originalIID_legal_pressure_vanishing_error F μ ν π hπ hA hB hAB hμ hν
    hu hcal hg G hgb hq t

/-- The compact original probabilities produce the calibration and legal
pressure comparison internally. A selected population optimizer, a given dual
potential and scalar-bin balance are not hypotheses. -/
theorem exists_complete_finsler_originalIID_legal_pressure_data
    (F : ContinuousFinslerNorm E M)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) :
    let _instOriginalLegalDataMetric : MetricSpace M := F.metricSpace
    ∃ u : M → ℝ, LipschitzWith 1 u ∧
      ∀ g : M × M → ℝ, Measurable g → ∀ G : ℝ≥0, (∀ p, |g p| ≤ G) → ∀ t : ℝ,
        ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (𝓝 0) ∧
          ∀ n, finslerOriginalIIDPressure F μ ν u g
              (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) t (n + 1) ≤
            finslerOriginalIIDLegalPressure F μ ν u g
              (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) t (n + 1) +
              error n := by
  let _instOriginalLegalDataProofMetric : MetricSpace M := F.metricSpace
  obtain ⟨u, π, hu, hopt, hcal, _⟩ := exists_calibrated_optimalCoupling_of_compact_carrier
    μ ν (hA.union hB) (hμ.mono fun _ hx ↦ Or.inl hx) (hν.mono fun _ hy ↦ Or.inr hy)
  have hπ : Vlasov.IsCoupling π μ ν := hopt.1
  have : IsProbabilityMeasure (π.map Prod.fst) := hπ.1.symm ▸ inferInstance
  let _instOriginalLegalDataPlanProbability : IsProbabilityMeasure π :=
    Measure.isProbabilityMeasure_of_map Prod.fst
  have hcalF : ∀ᵐ p ∂π, (F.lengthEDist p.1 p.2).toReal = u p.2 - u p.1 := by
    filter_upwards [hcal] with p hp
    simpa only [F.metricSpace_dist] using hp.symm
  refine ⟨u, hu, ?_⟩
  intro g hg G hgb t
  exact exists_complete_finsler_originalIID_legal_pressure_vanishing_error
    F hcomplete hdim μ ν π hπ hA hB hAB hμ hν hu hcalF hg G hgb t

end OTSelector.Reconstruction
