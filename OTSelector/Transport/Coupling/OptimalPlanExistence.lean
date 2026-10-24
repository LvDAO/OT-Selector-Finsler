import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import OTSelector.Transport.Coupling.CostEquivalence
import OTSelector.Transport.Coupling.Embedding
import OTSelector.Transport.Coupling.OptimalCalibration
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OptimalPlanExistence.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OptimalPlanExistence`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OptimalPlanExistence

**Conditions:** Original probability marginals are carried by a common compact subset of the metric space.

**Objects:** An actual original distance optimizer and, together with dual attainment, a calibrated optimizer and characterization of its entire face.

**Proof detail:** Feasible probability couplings are nonempty and closed in a compact probability space; continuous bounded distance attains its minimum, and exact compact-subtype lifting accounts for all ambient competitors.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=68), Section 437P and Theorem 437R(f), (g), (h), tightness, compact measure sets and metrizability; [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61), Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation; [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I](https://www.jirka.org/ra/html/sec_metcont.html), Section 7.5, Lemma 7.5.5 (compact continuous images), Theorem 7.5.6 (extreme values), and Exercise 7.5.6 (intermediate value theorem); [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=110), Section 6.1, Proposition 6.1 and equation (6.1), pp. 106–107 (PDF pages 110–111).

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Existence of original distance-optimal probability couplings

On a compact metric carrier, the feasible probability couplings form a nonempty closed
subset of a compact space. The integral of the original distance is continuous and
attains its minimum. Exact subtype lifting transfers this optimizer to the original
ambient metric space. Combining it with dual attainment gives an actual calibrated
minimizer and the calibration characterization of the whole optimal face.
-/

open Set MeasureTheory Filter
open scoped ENNReal BoundedContinuousFunction

namespace OTSelector.Reconstruction

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The original extended-distance cost admits a minimizing coupling on a compact
metric Borel space. The feasible set and its minimum are constructed. -/
theorem exists_isOptimalCoupling_edist_of_compactSpace [CompactSpace M]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∃ π : Measure (M × M), IsOptimalCoupling edist μ ν π := by
  let μP : ProbabilityMeasure M := ⟨μ, inferInstance⟩
  let νP : ProbabilityMeasure M := ⟨ν, inferInstance⟩
  let S : Set (ProbabilityMeasure (M × M)) :=
    {π | π.map measurable_fst.aemeasurable = μP ∧
      π.map measurable_snd.aemeasurable = νP}
  have hclosed : IsClosed S :=
    (isClosed_eq (ProbabilityMeasure.continuous_map continuous_fst)
      continuous_const).inter
      (isClosed_eq (ProbabilityMeasure.continuous_map continuous_snd) continuous_const)
  have hnonempty : S.Nonempty := ⟨μP.prod νP, by simp [S]⟩
  let d : (M × M) →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun z ↦ dist z.1 z.2, continuous_fst.dist continuous_snd⟩
  obtain ⟨π, hπ, hmin⟩ := hclosed.isCompact.exists_isMinOn hnonempty
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction d).continuousOn
  have hcoupling : Vlasov.IsCoupling (π : Measure (M × M)) μ ν :=
    ⟨congrArg ProbabilityMeasure.toMeasure hπ.1,
      congrArg ProbabilityMeasure.toMeasure hπ.2⟩
  have hcost (κ : ProbabilityMeasure (M × M)) :
      couplingCost edist (κ : Measure (M × M)) =
        ENNReal.ofReal (∫ z, d z ∂(κ : Measure (M × M))) := by
    unfold couplingCost
    simp_rw [edist_dist]
    exact (ofReal_integral_eq_lintegral_ofReal (d.integrable κ)
      (Eventually.of_forall fun _ ↦ dist_nonneg)).symm
  refine ⟨π, hcoupling, fun κ hκ ↦ ?_⟩
  have : IsProbabilityMeasure (κ.map Prod.fst) := hκ.1.symm ▸ inferInstance
  have : IsProbabilityMeasure κ := Measure.isProbabilityMeasure_of_map Prod.fst
  let κP : ProbabilityMeasure (M × M) := ⟨κ, inferInstance⟩
  have hκP : κP ∈ S := by
    constructor
    · exact ProbabilityMeasure.toMeasure_injective hκ.1
    · exact ProbabilityMeasure.toMeasure_injective hκ.2
  change couplingCost edist (π : Measure (M × M)) ≤
    couplingCost edist (κP : Measure (M × M))
  rw [hcost π, hcost κP]
  exact ENNReal.ofReal_le_ofReal (hmin hκP)

/-- Original probabilities carried by one compact set admit an original
extended-distance optimizer. Compactness or second countability of the ambient space
is not required. Every ambient competitor is accounted for by exact subtype lifting. -/
theorem exists_isOptimalCoupling_edist_of_compact_carrier
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K : Set M} (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K)
    (hν : ∀ᵐ x ∂ν, x ∈ K) :
    ∃ π : Measure (M × M), IsOptimalCoupling edist μ ν π := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let μK := μ.comap ((↑) : K → M)
  let νK := ν.comap ((↑) : K → M)
  have hμmap : μK.map ((↑) : K → M) = μ :=
    map_comap_subtype_of_ae_mem hK.measurableSet hμ
  have hνmap : νK.map ((↑) : K → M) = ν :=
    map_comap_subtype_of_ae_mem hK.measurableSet hν
  have : IsProbabilityMeasure (μK.map ((↑) : K → M)) := hμmap.symm ▸ inferInstance
  have : IsProbabilityMeasure (νK.map ((↑) : K → M)) := hνmap.symm ▸ inferInstance
  have : IsProbabilityMeasure μK := Measure.isProbabilityMeasure_of_map ((↑) : K → M)
  have : IsProbabilityMeasure νK := Measure.isProbabilityMeasure_of_map ((↑) : K → M)
  obtain ⟨πK, hπK⟩ := exists_isOptimalCoupling_edist_of_compactSpace μK νK
  refine ⟨πK.map (Prod.map ((↑) : K → M) ((↑) : K → M)), ?_⟩
  have h := (isOptimalCoupling_map_subtype_edist_iff hK.measurableSet).mpr hπK
  rwa [hμmap, hνmap] at h

/-- Compactly carried original probabilities have an actual calibrated optimal
coupling and a global one-Lipschitz potential that characterizes their entire optimal
face. Neither a primal optimizer nor a dual maximizer is supplied. -/
theorem exists_calibrated_optimalCoupling_of_compact_carrier
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K : Set M} (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K)
    (hν : ∀ᵐ x ∂ν, x ∈ K) :
    ∃ (f : M → ℝ) (π : Measure (M × M)), LipschitzWith 1 f ∧
      IsOptimalCoupling edist μ ν π ∧
      (∀ᵐ z ∂π, f z.2 - f z.1 = dist z.1 z.2) ∧
      ∀ κ : Measure (M × M), Vlasov.IsCoupling κ μ ν →
        (IsOptimalCoupling edist μ ν κ ↔
          ∀ᵐ z ∂κ, f z.2 - f z.1 = dist z.1 z.2) := by
  obtain ⟨x₀, hx₀⟩ := hμ.exists
  obtain ⟨f, hf, _, hface⟩ :=
    exists_optimal_calibration_of_compact_carrier μ ν hK hμ hν ⟨x₀, hx₀⟩
  obtain ⟨π, hπ⟩ := exists_isOptimalCoupling_edist_of_compact_carrier μ ν hK hμ hν
  exact ⟨f, π, hf, hπ, (hface π hπ.1).mp hπ, hface⟩

end OTSelector.Reconstruction

end
