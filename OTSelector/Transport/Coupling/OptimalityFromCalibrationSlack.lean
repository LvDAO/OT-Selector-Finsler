import OTSelector.Transport.Coupling.CostEquivalence
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.PopulationOptimality.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.PopulationOptimality`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.PopulationOptimality

**Conditions:** Compact metric Borel carriers, weak convergence of probability plans/marginals, bounded continuous cost/potentials, and feasible dual potentials with vanishing slack.

**Objects:** A feasible weak limit, equality of primal and dual cost, and optimality for the original nonnegative cost.

**Proof detail:** Push weak convergence through marginal maps, pass bounded continuous slack integrals to the limit, and compare every competitor to the attained dual value using the fixed marginal integrals.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61), Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31), Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20); [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf), Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini).

Source relation (generalization): The weak-integral and feasible-dual argument applies to the stated compact probability setting; finite duality is cited for its primal/dual comparison principle, while existence of the feasible potentials and the convergence hypotheses remain explicit inputs.
-/

/-!
# Population optimality from vanishing calibration slack

Weak convergence of plans and of their marginals preserves feasibility on compact metric Borel
spaces. If a bounded continuous cost has feasible bounded continuous endpoint potentials and the
integral of their calibration slack tends to zero, the limit attains the dual value and minimizes
the actual nonnegative cost over every feasible coupling. Feasibility and optimality of the limit
are conclusions. Optimality uses the existing extended-valued `IsOptimalCoupling` predicate.
-/

open Filter MeasureTheory Set
open scoped Topology BoundedContinuousFunction

namespace OTSelector.Reconstruction

variable {A B : Type*} [MetricSpace A] [MetricSpace B]
  [CompactSpace A] [CompactSpace B] [MeasurableSpace A] [MeasurableSpace B]
  [BorelSpace A] [BorelSpace B]

omit [CompactSpace A] in
/-- Continuous marginal projections and uniqueness of weak limits recover the prescribed
population marginals. Feasibility is required only eventually along the nontrivial filter. -/
theorem isCoupling_of_weak_limits
    {ι : Type*} {l : Filter ι} [NeBot l]
    (plans : ι → ProbabilityMeasure (A × B)) (sources : ι → ProbabilityMeasure A)
    (targets : ι → ProbabilityMeasure B) (π : ProbabilityMeasure (A × B))
    (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure B)
    (hplans : Tendsto plans l (𝓝 π)) (hsources : Tendsto sources l (𝓝 μ))
    (htargets : Tendsto targets l (𝓝 ν))
    (hcoupling : ∀ᶠ i in l, Vlasov.IsCoupling (plans i : Measure (A × B))
      (sources i : Measure A) (targets i : Measure B)) :
    Vlasov.IsCoupling (π : Measure (A × B)) (μ : Measure A) (ν : Measure B) := by
  have hfst := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    plans π hplans (continuous_fst : Continuous (Prod.fst : A × B → A))
  have hsnd := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    plans π hplans (continuous_snd : Continuous (Prod.snd : A × B → B))
  have hfstEq : (fun i ↦ (plans i).map measurable_fst.aemeasurable) =ᶠ[l] sources := by
    filter_upwards [hcoupling] with i hi
    exact ProbabilityMeasure.toMeasure_injective hi.1
  have hsndEq : (fun i ↦ (plans i).map measurable_snd.aemeasurable) =ᶠ[l] targets := by
    filter_upwards [hcoupling] with i hi
    exact ProbabilityMeasure.toMeasure_injective hi.2
  have hfstLimit := tendsto_nhds_unique hfst (hsources.congr' hfstEq.symm)
  have hsndLimit := tendsto_nhds_unique hsnd (htargets.congr' hsndEq.symm)
  exact ⟨congrArg ProbabilityMeasure.toMeasure hfstLimit,
    congrArg ProbabilityMeasure.toMeasure hsndLimit⟩

omit [MetricSpace B] [CompactSpace A] [CompactSpace B] [BorelSpace B] in
private theorem integral_fst_of_coupling
    (u : A →ᵇ ℝ) {κ : Measure (A × B)} {μ : Measure A} {ν : Measure B}
    (hκ : Vlasov.IsCoupling κ μ ν) :
    ∫ z, u z.1 ∂κ = ∫ x, u x ∂μ := by
  rw [← hκ.1]
  exact (integral_map measurable_fst.aemeasurable u.continuous.aestronglyMeasurable).symm

omit [MetricSpace A] [CompactSpace A] [CompactSpace B] [BorelSpace A] in
private theorem integral_snd_of_coupling
    (v : B →ᵇ ℝ) {κ : Measure (A × B)} {μ : Measure A} {ν : Measure B}
    (hκ : Vlasov.IsCoupling κ μ ν) :
    ∫ z, v z.2 ∂κ = ∫ y, v y ∂ν := by
  rw [← hκ.2]
  exact (integral_map measurable_snd.aemeasurable v.continuous.aestronglyMeasurable).symm

omit [CompactSpace A] in
/-- A feasible probability plan with zero integrated calibration slack has cost exactly equal
to the sum of the endpoint-potential integrals. -/
theorem integral_cost_eq_dual_of_zero_slack
    (cost : (A × B) →ᵇ ℝ) (u : A →ᵇ ℝ) (v : B →ᵇ ℝ)
    (π : ProbabilityMeasure (A × B)) (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure B)
    (hcoupling : Vlasov.IsCoupling (π : Measure (A × B)) (μ : Measure A) (ν : Measure B))
    (hslack : ∫ z, (cost z - u z.1 - v z.2) ∂(π : Measure (A × B)) = 0) :
    ∫ z, cost z ∂(π : Measure (A × B)) =
      (∫ x, u x ∂(μ : Measure A)) + ∫ y, v y ∂(ν : Measure B) := by
  have hu : Integrable (fun z : A × B ↦ u z.1) (π : Measure (A × B)) :=
    (u.compContinuous ⟨Prod.fst, continuous_fst⟩).integrable _
  have hv : Integrable (fun z : A × B ↦ v z.2) (π : Measure (A × B)) :=
    (v.compContinuous ⟨Prod.snd, continuous_snd⟩).integrable _
  rw [integral_sub (f := fun z ↦ cost z - u z.1) ((cost.integrable _).sub hu) hv,
    integral_sub (f := fun z ↦ cost z) (cost.integrable _) hu,
    integral_fst_of_coupling u hcoupling, integral_snd_of_coupling v hcoupling] at hslack
  linarith

omit [CompactSpace A] in
/-- A zero-slack calibration certificate proves extended-cost optimality against every feasible
joint measure. Any such competitor is itself a probability measure by its source marginal. -/
theorem isOptimalCoupling_of_zero_slack
    (cost : (A × B) →ᵇ ℝ) (u : A →ᵇ ℝ) (v : B →ᵇ ℝ)
    (hcost : ∀ z, 0 ≤ cost z) (hdual : ∀ x y, u x + v y ≤ cost (x, y))
    (π : ProbabilityMeasure (A × B)) (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure B)
    (hcoupling : Vlasov.IsCoupling (π : Measure (A × B)) (μ : Measure A) (ν : Measure B))
    (hslack : ∫ z, (cost z - u z.1 - v z.2) ∂(π : Measure (A × B)) = 0) :
    IsOptimalCoupling (fun x y ↦ ENNReal.ofReal (cost (x, y)))
      (μ : Measure A) (ν : Measure B) (π : Measure (A × B)) := by
  have hvalue := integral_cost_eq_dual_of_zero_slack cost u v π μ ν hcoupling hslack
  refine ⟨hcoupling, fun κ hκ ↦ ?_⟩
  have : IsProbabilityMeasure (κ.map Prod.fst) := by
    rw [hκ.1]
    infer_instance
  have : IsProbabilityMeasure κ := Measure.isProbabilityMeasure_of_map Prod.fst
  have hu : Integrable (fun z : A × B ↦ u z.1) κ :=
    (u.compContinuous ⟨Prod.fst, continuous_fst⟩).integrable _
  have hv : Integrable (fun z : A × B ↦ v z.2) κ :=
    (v.compContinuous ⟨Prod.snd, continuous_snd⟩).integrable _
  have hbound : (∫ x, u x ∂(μ : Measure A)) + (∫ y, v y ∂(ν : Measure B)) ≤
      ∫ z, cost z ∂κ := by
    rw [← integral_fst_of_coupling u hκ, ← integral_snd_of_coupling v hκ,
      ← integral_add hu hv]
    exact integral_mono (hu.add hv) (cost.integrable _) (fun z ↦ hdual z.1 z.2)
  unfold couplingCost
  rw [← ofReal_integral_eq_lintegral_ofReal (cost.integrable _)
    (Eventually.of_forall hcost)]
  rw [← ofReal_integral_eq_lintegral_ofReal (cost.integrable _)
    (Eventually.of_forall hcost)]
  exact ENNReal.ofReal_le_ofReal (hvalue.trans_le hbound)

omit [CompactSpace A] in
/-- Weak limits of feasible plans with vanishing calibration slack are feasible population
optimizers and attain the dual value. Neither feasibility nor optimality of the limit is a
premise, and the approximating plans need not themselves be optimal. -/
theorem population_optimality_of_weak_limits
    {ι : Type*} {l : Filter ι} [NeBot l]
    (cost : (A × B) →ᵇ ℝ) (u : A →ᵇ ℝ) (v : B →ᵇ ℝ)
    (hcost : ∀ z, 0 ≤ cost z) (hdual : ∀ x y, u x + v y ≤ cost (x, y))
    (plans : ι → ProbabilityMeasure (A × B)) (sources : ι → ProbabilityMeasure A)
    (targets : ι → ProbabilityMeasure B) (π : ProbabilityMeasure (A × B))
    (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure B)
    (hplans : Tendsto plans l (𝓝 π)) (hsources : Tendsto sources l (𝓝 μ))
    (htargets : Tendsto targets l (𝓝 ν))
    (hcoupling : ∀ᶠ i in l, Vlasov.IsCoupling (plans i : Measure (A × B))
      (sources i : Measure A) (targets i : Measure B))
    (hslack : Tendsto
      (fun i ↦ ∫ z, (cost z - u z.1 - v z.2) ∂(plans i : Measure (A × B))) l (𝓝 0)) :
    (∫ z, cost z ∂(π : Measure (A × B)) =
      (∫ x, u x ∂(μ : Measure A)) + ∫ y, v y ∂(ν : Measure B)) ∧
    IsOptimalCoupling (fun x y ↦ ENNReal.ofReal (cost (x, y)))
      (μ : Measure A) (ν : Measure B) (π : Measure (A × B)) := by
  have hπ := isCoupling_of_weak_limits plans sources targets π μ ν
    hplans hsources htargets hcoupling
  let slack : (A × B) →ᵇ ℝ := cost - u.compContinuous ⟨Prod.fst, continuous_fst⟩ -
    v.compContinuous ⟨Prod.snd, continuous_snd⟩
  have hlimit := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hplans) slack
  have hzero : ∫ z, (cost z - u z.1 - v z.2) ∂(π : Measure (A × B)) = 0 :=
    tendsto_nhds_unique hlimit hslack
  exact ⟨integral_cost_eq_dual_of_zero_slack cost u v π μ ν hπ hzero,
    isOptimalCoupling_of_zero_slack cost u v hcost hdual π μ ν hπ hzero⟩

end OTSelector.Reconstruction

end
