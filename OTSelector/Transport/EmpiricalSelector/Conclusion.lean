import OTSelector.Reconstruction.FinslerOriginalPaperIndependence

/-!
# The displayed empirical-selector conclusion

`PaperLineByLineConclusion` names the three clauses of the paper theorem:
population optimality, weak-neighborhood convergence of the full empirical
optimal face, and the metric supremum form. Its arguments contain only the
original populations, samples, and candidate plan. The two equivalences below
identify this structured presentation with `IsPaperSelectorPlan`.

The proved theorem from the original Finsler and iid hypotheses is
`existsUnique_original_general_finsler_selector_for_iid_samples`.
-/

open Filter MeasureTheory
open scoped Topology

noncomputable section
namespace OTSelector.Reconstruction

/-- **The paper's displayed conclusion, line by line.**

Arguments: the population marginals mu, nu, the sampling data P, X, Y and the
candidate plan pi.  No potential, coordinate, label or tie-breaking data occurs
(main.tex:107-109). -/
structure PaperLineByLineConclusion {M : Type*} [MetricSpace M] [MeasurableSpace M]
    [BorelSpace M] [ProperSpace M]
    (mu nu : ProbabilityMeasure M) {Omega : ℕ → Type*} [∀ n, MeasurableSpace (Omega n)]
    (P : ∀ n, Measure (Omega n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Omega n → M) (pi : ProbabilityMeasure (M × M)) : Prop where
  /-- main.tex:98-99 and main.tex:94-96: the plan pi is the deterministic population
  distance-optimal plan, i.e. an optimal coupling of mu and nu for the original
  length cost d_F.  (On the Finsler metric space F.metricSpace, edist is the
  path-length distance d_F; fractional optima are included, main.tex:107.) -/
  population_optimal_plan :
    IsOptimalCoupling edist (mu : Measure M) (nu : Measure M) (pi : Measure (M × M))
  /-- main.tex:94-96 and main.tex:99-104: Opt_n is the ENTIRE optimal coupling set
  for the original length cost d_F, and for every metric d_weak inducing weak
  convergence on probabilities on A x B, the whole empirical optimal face
  converges to pi in probability.  Written in weak-neighbourhood form. -/
  weak_convergence :
    ∀ U ∈ nhds pi, Tendsto (fun n => (P n).real
      {s | ∃ gamma ∈ Pressure.empiricalOptimalFace
        (fun i => X n i s) (fun i => Y n i s), gamma ∉ U}) atTop (nhds 0)
  /-- main.tex:101-106, equation (general-finsler-entire-selector): the displayed
  sup form.  For every metric d_weak inducing weak convergence on probabilities,
  sup over gamma in Opt_n of d_weak(gamma, pi) tends to zero in probability;
  written as the vanishing probability of the event that some empirical optimum
  is at d_weak-distance at least eps from pi. -/
  metric_sup_convergence :
    ∀ d : ProbabilityMeasure (M × M) → ProbabilityMeasure (M × M) → ℝ,
      d pi pi = 0 →
      (∀ eps : ℝ, 0 < eps → IsOpen {gamma : ProbabilityMeasure (M × M) |
        d gamma pi < eps}) →
      ∀ eps : ℝ, 0 < eps → Tendsto (fun n => (P n).real
        {s | ∃ gamma ∈ Pressure.empiricalOptimalFace
          (fun i => X n i s) (fun i => Y n i s), eps ≤ d gamma pi}) atTop (nhds 0)

/-- **The line-by-line predicate is exactly the repo paper-facing predicate.**

Both predicates unfold to the same three clauses: optimality of the population
plan, weak-neighbourhood convergence of the entire empirical optimal face, and
the displayed metric sup convergence (main.tex:98-106). -/
theorem paperLineByLineConclusion_iff_isPaperSelectorPlan
    {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [ProperSpace M]
    {Omega : ℕ → Type*} [∀ n, MeasurableSpace (Omega n)]
    (P : ∀ n, Measure (Omega n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Omega n → M)
    {mu nu : ProbabilityMeasure M} (pi : ProbabilityMeasure (M × M)) :
    PaperLineByLineConclusion mu nu P X Y pi ↔ IsPaperSelectorPlan mu nu P X Y pi := by
  constructor
  · intro h
    exact ⟨h.population_optimal_plan, h.weak_convergence, h.metric_sup_convergence⟩
  · intro h
    exact ⟨h.1, h.2.1, h.2.2⟩

/-- **The displayed form s are interchangeable under exists-unique.**  The
paper's displayed conclusion is the same either way: exists-unique a plan
satisfying PaperLineByLineConclusion iff exists-unique a plan satisfying
IsPaperSelectorPlan. -/
theorem existsUnique_paperLineByLineConclusion_iff_existsUnique_isPaperSelectorPlan
    {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [ProperSpace M]
    {Omega : ℕ → Type*} [∀ n, MeasurableSpace (Omega n)]
    (P : ∀ n, Measure (Omega n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Omega n → M)
    {mu nu : ProbabilityMeasure M} :
    ((∃! pi : ProbabilityMeasure (M × M), PaperLineByLineConclusion mu nu P X Y pi) ↔
      (∃! pi : ProbabilityMeasure (M × M), IsPaperSelectorPlan mu nu P X Y pi)) := by
  constructor
  · rintro ⟨w, hw, huniq⟩
    exact ⟨w, (paperLineByLineConclusion_iff_isPaperSelectorPlan P X Y w).mp hw,
      fun y hy => huniq y ((paperLineByLineConclusion_iff_isPaperSelectorPlan P X Y y).mpr hy)⟩
  · rintro ⟨w, hw, huniq⟩
    exact ⟨w, (paperLineByLineConclusion_iff_isPaperSelectorPlan P X Y w).mpr hw,
      fun y hy => huniq y ((paperLineByLineConclusion_iff_isPaperSelectorPlan P X Y y).mp hy)⟩

end OTSelector.Reconstruction
