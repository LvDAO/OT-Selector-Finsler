import OTSelector.Analysis.Convex.UniformDerivativeReadout
import OTSelector.MeasureTheory.CompactReadout
import OTSelector.Probability.RandomSetWholeFace
import OTSelector.Probability.RowProbabilityFilter
import OTSelector.Probability.RowProbabilityNontrivial
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Limit.PressureSelector.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Limit.PressureSelector`; the selected original proof blocks follow. -/
section

/-!
# Limit.PressureSelector

**Conditions:** Probability optimizer faces are eventually nonempty on a compact metric support; every bounded continuous probe has the explicit pressure derivative, central convergence, neighboring lower bound and affine comparison.

**Objects:** One uniquely determined probability measure and weak convergence of the entire face to it.

**Proof detail:** First trap all scalar readouts by opposite pressure secants; compactness supplies a subsequential limit, continuous probes identify it uniquely, and finite neighborhood tests upgrade scalar control to whole-face weak convergence.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=68), Section 437P and Theorem 437R(f), (g), (h), tightness, compact measure sets and metrizability; [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61), Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation; [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=47), Sections 436J–436K, Riesz representation on locally compact Hausdorff spaces; [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=83), Sections 3.1.3–3.1.4, pp. 69–71, first-order support inequality (3.2) and positive-semidefinite Hessian criterion.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Deterministic whole-face limits from probe pressures on compact supports

Differentiable limiting pressures for all bounded continuous probes determine a unique probability
measure. The proof derives uniform scalar readouts, constructs the measure by compactness,
and finally obtains weak convergence of the entire face. The limit measure is not an input.

The compact space represents the support of plans, not a compactness assumption on the ambient
manifold. The pressure limits and affine comparisons remain explicit analytic premises. This module
does not establish them for the general Finsler empirical model or assert population optimality.
-/

open Filter MeasureTheory Set
open scoped Topology BoundedContinuousFunction

namespace OTSelector.Pressure

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
  [T2Space E] [BorelSpace E] [CompactSpace E] [HasOuterApproxClosed E]

/-- Probe-pressure derivatives construct the unique limiting measure and control every face member.
Nonemptiness and nontriviality are used for reconstruction, not to select an empirical optimizer. -/
theorem existsUnique_probabilityMeasure_of_pressure
    {ι : Type*} {l : Filter ι} [NeBot l]
    (face : ι → Set (ProbabilityMeasure E))
    (value : (E →ᵇ ℝ) → ι → ℝ → ℝ) (pressure : (E →ᵇ ℝ) → ℝ → ℝ)
    (radius derivative : (E →ᵇ ℝ) → ℝ)
    (hne : ∀ᶠ z in l, (face z).Nonempty)
    (hradius : ∀ f, 0 < radius f)
    (hderiv : ∀ f, HasDerivAt (pressure f) (derivative f) 0)
    (hzero : ∀ f, Tendsto (fun z ↦ value f z 0) l (𝓝 (pressure f 0)))
    (hlower : ∀ f t, |t| < radius f →
      Tendsto (fun z ↦ max (pressure f t - value f z t) 0) l (𝓝 0))
    (haffine : ∀ f t, |t| < radius f → ∀ᶠ z in l, ∀ μ ∈ face z,
      value f z t ≤ value f z 0 + t * ∫ x, f x ∂(μ : Measure E)) :
    ∃! ν : ProbabilityMeasure E,
      (∀ f : E →ᵇ ℝ, ∫ x, f x ∂(ν : Measure E) = derivative f) ∧
        Tendsto face l (𝓝 ν).smallSets := by
  have htest (f : E →ᵇ ℝ) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ z in l, ∀ μ ∈ face z, |(∫ x, f x ∂(μ : Measure E)) - derivative f| < ε :=
    eventually_forall_readout_of_pressure face (fun _ μ ↦ ∫ x, f x ∂(μ : Measure E))
      (value f) (pressure f) (hradius f) (hderiv f) (hzero f) (hlower f) (haffine f) hε
  obtain ⟨ν, hν, huniq⟩ := Reconstruction.existsUnique_probabilityMeasure_of_uniform_readout
    face derivative hne htest
  refine ⟨ν, ⟨hν, ?_⟩, fun μ hμ ↦ huniq μ hμ.1⟩
  apply WholeFace.tendsto_smallSets_of_forall_integral face ν
  intro f ε hε
  simpa only [hν f] using htest f ε hε

/-- Under the original probability row laws, probe pressures construct one deterministic measure
and the probability that any face member leaves a weak neighborhood tends to zero. Arbitrary
failure events are measured by outer measure; no measurable optimizer choice is required. -/
theorem existsUnique_probabilityMeasure_row_of_pressure
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (face : (Σ n, Ω n) → Set (ProbabilityMeasure E))
    (value : (E →ᵇ ℝ) → (Σ n, Ω n) → ℝ → ℝ)
    (pressure : (E →ᵇ ℝ) → ℝ → ℝ) (radius derivative : (E →ᵇ ℝ) → ℝ)
    (hne : Tendsto (fun n ↦ (P n).real {ω | ¬ (face ⟨n, ω⟩).Nonempty}) atTop (𝓝 0))
    (hradius : ∀ f, 0 < radius f)
    (hderiv : ∀ f, HasDerivAt (pressure f) (derivative f) 0)
    (hzero : ∀ f ε, 0 < ε → Tendsto
      (fun n ↦ (P n).real {ω | ε ≤ |value f ⟨n, ω⟩ 0 - pressure f 0|}) atTop (𝓝 0))
    (hlower : ∀ f t, |t| < radius f → ∀ ε, 0 < ε → Tendsto
      (fun n ↦ (P n).real {ω | ε ≤ max (pressure f t - value f ⟨n, ω⟩ t) 0})
      atTop (𝓝 0))
    (haffine : ∀ f t, |t| < radius f → Tendsto
      (fun n ↦ (P n).real {ω | ¬ ∀ μ ∈ face ⟨n, ω⟩,
        value f ⟨n, ω⟩ t ≤ value f ⟨n, ω⟩ 0 + t * ∫ x, f x ∂(μ : Measure E)})
      atTop (𝓝 0)) :
    ∃! ν : ProbabilityMeasure E,
      (∀ f : E →ᵇ ℝ, ∫ x, f x ∂(ν : Measure E) = derivative f) ∧
        ∀ U ∈ 𝓝 ν, Tendsto
          (fun n ↦ (P n).real {ω | ∃ μ ∈ face ⟨n, ω⟩, μ ∉ U}) atTop (𝓝 0) := by
  have htestP (f : E →ᵇ ℝ) (ε : ℝ) (hε : 0 < ε) :
      Tendsto (fun n ↦ (P n).real {ω | ∃ μ ∈ face ⟨n, ω⟩,
        ε ≤ |(∫ x, f x ∂(μ : Measure E)) - derivative f|}) atTop (𝓝 0) :=
    tendsto_measureReal_exists_readout_of_pressure P face
      (fun _ μ ↦ ∫ x, f x ∂(μ : Measure E)) (value f) (pressure f)
      (hradius f) (hderiv f) (hzero f) (hlower f) (haffine f) hε
  have htest (f : E →ᵇ ℝ) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ z in Probability.rowProbabilityFilter P, ∀ μ ∈ face z,
        |(∫ x, f x ∂(μ : Measure E)) - derivative f| < ε := by
    apply (Probability.eventually_rowProbabilityFilter_iff P _).mpr
    simpa only [not_forall, not_lt, exists_prop] using htestP f ε hε
  have hne' : ∀ᶠ z in Probability.rowProbabilityFilter P, (face z).Nonempty :=
    (Probability.eventually_rowProbabilityFilter_iff P _).mpr hne
  obtain ⟨ν, hν, huniq⟩ := Reconstruction.existsUnique_probabilityMeasure_of_uniform_readout
    face derivative hne' htest
  refine ⟨ν, ⟨hν, ?_⟩, fun μ hμ ↦ huniq μ hμ.1⟩
  intro U hU
  apply WholeFace.tendsto_measureReal_exists_notMem_of_forall_integral P face ν _ U hU
  intro f ε hε
  simpa only [hν f] using htestP f ε hε

end OTSelector.Pressure

end
