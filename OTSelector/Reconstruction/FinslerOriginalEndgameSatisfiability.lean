import OTSelector.Reconstruction.FinslerOriginalConditionalEndgame

/-!
# Satisfiability and non-vacuity of the conditional endgame hypotheses

The conditional endgame of the general Finsler selector is packaged in the
structure |FinslerConditionalEndgameHypotheses| (FinslerOriginalConditionalEndgame):
the paper-side geometric hypotheses together with the reduced named analytic
fields |pressureLower|, |pressureUpper|, |radius|, |hradius|, |hvalue|, |hprob|,
|hupper|.  This file shows that the package is *consistent*: no field is
impossible and no field refutes another.

Main results:

* |trivialPalmSampleLaw| and |emptyRayClusterData|: the leaf records
  |PaperPalmSampleLaw| and |AeRayClusterData| are inhabited *unconditionally*.
  The ray-cluster record is satisfied by the empty ray domain (all ray
  conditions are vacuous), so it imposes no mathematical constraint on the rest
  of the bundle.
* |samplePressure|: an explicit pressure field of the singleton empirical kernel,
  |(f, t) ↦ t * f (p, q)| for two fixed carrier projections |p| and |q|.
* |finslerSupportedPressure_const|: the supported empirical pressure of a
  constant sample pair equals |t * f (p, q)| exactly (the distance slack is zero
  because both samples coincide, and the probe matrix is constant).
* |paperGeometricHypothesesOfTube|: the paper's calibrated tube plus the
  pointwise clock atomlessness give the whole geometric bundle.
* |nonempty_conditionalEndgameHypotheses_of_geometric|: for *every* geometric
  bundle (arbitrary paper-side ray data and Palm law) and every probability
  sample law with constant source and target samples, the conditional endgame
  structure is inhabited.  Hence the analytic fields can never be refuted by the
  geometric data, and conversely.
* |nonempty_conditionalEndgameHypotheses|: the concrete instance from the
  paper's tube hypothesis.

The remaining inputs of the witness are exactly the paper's data: a calibrated
tube (|CalibratedTube|), a 1-Lipschitz potential, pointwise clock atomlessness,
compact carriers with the population marginals supported on them, a probability
sample law and one base point |x0|.  These are precisely the geometric/Palm data
that the paper proves/assumes, not additional endgame hypotheses; in particular
no analytic field (pressure limit, value identification, probability bounds) is
assumed in the witness: all of them are constructed and proved here.

Circularity audit: the only logical interaction between fields is that
|hvalue| equates |pressureLower| and |pressureUpper|, and |hprob| / |hupper|
are one-sided limits for them; the witness satisfies |hvalue| and both limits
with the same explicitly constructed field, so there is no inconsistent
circularity.  |radius| / |hradius| are independent bookkeeping; |hvalue| is
independent of the geometric bundle; |interior_nonempty| cannot be derived from
the (possibly empty) ray clusters, and conversely the trivial ray clusters are
consistent with a nonempty calibrated interior; |hprob| / |hupper| are not
derivable from any other field but are supplied here by the singleton-kernel
computation.  No field was found to be refutable under the others.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module
open OTSelector.Geometry OTSelector.Probability TopologicalSpace
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

universe uE uM uZ

variable {E : Type uE} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]

/-! ## 1. The leaf records are inhabited -/

/-- The Palm sample law with all lane quantities identically zero. -/
def trivialPalmSampleLaw : PaperPalmSampleLaw where
  maskedMean := fun _ => 0
  normalization := fun _ => 0
  populationValue := fun _ => 0
  palmReadout := fun _ => 0
  maskedMean_eq := fun _ => rfl
  readout_tendsto := by
    simpa using tendsto_const_nhds

/-- The abstract Palm sample law is inhabited. -/
theorem nonempty_paperPalmSampleLaw : Nonempty PaperPalmSampleLaw :=
  ⟨trivialPalmSampleLaw⟩

/-- The a.e. ray-cluster data with empty ray domain and empty good set.  Every
ray clause quantifies over the empty set, so the record is satisfied with no
geometric input at all. -/
def emptyRayClusterData (F : ContinuousFinslerNorm E M) (u : M → ℝ) (ν : Measure M) :
    AeRayClusterData F u ν where
  domain := ∅
  domain_measurable := MeasurableSet.empty
  good := ∅
  good_measurable := MeasurableSet.empty
  good_subset := empty_subset _
  good_null := by simp
  curve := fun x _ => x
  curve_zero := by intro x hx; simp at hx
  el := by intro x hx; simp at hx
  radius := fun _ => 1
  radius_pos := by intro x hx; simp at hx
  speed_one := by intro x hx; simp at hx
  locally_minimizing := by intro x hx; simp at hx
  clock := by intro x hx; simp at hx

/-- The almost-everywhere ray-cluster package is inhabited for arbitrary data. -/
theorem nonempty_aeRayClusterData (F : ContinuousFinslerNorm E M) (u : M → ℝ) (ν : Measure M) :
    Nonempty (AeRayClusterData F u ν) :=
  ⟨emptyRayClusterData F u ν⟩

/-! ## 2. The explicit singleton-kernel pressure field -/

/-- The pressure field of a singleton empirical kernel: the probe evaluated at
the two fixed carrier projections, tilted by the time |t|. -/
def samplePressure {A B : Set M} (p q : ↥(A ∪ B)) : FinalPressureField A B :=
  fun f t => t * f (p, q)

/-- Evaluation of the singleton-kernel pressure field. -/
@[simp] theorem samplePressure_apply {A B : Set M} (p q : ↥(A ∪ B))
    (f : FinalProbeSpace A B) (t : ℝ) :
    samplePressure p q f t = t * f (p, q) := rfl

/-! ## 3. Exact pressure of a constant sample pair -/

variable {F : ContinuousFinslerNorm E M} {u : M → ℝ} {μ ν : ProbabilityMeasure M}

/-- The supported empirical pressure of a constant sample pair equals the tilted
probe at the two fixed carrier projections.  The distance slack is zero because
both coordinates coincide, and the probe matrix is constant, so the assignment
minimum is just the tilted probe. -/
theorem finslerSupportedPressure_const
    {K : Set M} {hK : MeasurableSet K}
    {hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K} {hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K}
    {n : ℕ} (hn : n ≠ 0) {X Y : Fin n → M} {φ : M → ℝ} {k : ℝ}
    {f : (K × K) →ᵇ ℝ} {t : ℝ} {x₀ : M}
    (hX : ∀ i, X i = x₀) (hY : ∀ j, Y j = x₀) :
    finslerSupportedPressure F μ ν K hK hμ hν X Y φ k f t =
      t * f (supportProjection μ K hK hμ x₀, supportProjection ν K hK hν x₀) := by
  letI : MetricSpace M := F.metricSpace
  unfold finslerSupportedPressure Pressure.supportedDistancePressure
  dsimp only
  have hXc : X = fun _ => x₀ := funext hX
  have hYc : Y = fun _ => x₀ := funext hY
  rw [hXc, hYc]
  have hcost :
      (fun i j : Fin n =>
        k * distanceSlackEdgeCost (fun _ : Fin n => x₀) (fun _ : Fin n => x₀) φ i j) =
        fun (_ : Fin n) (_ : Fin n) => (0 : ℝ) := by
    funext i j
    simp only [distanceSlackEdgeCost, dist_self]
    ring
  have hprobe :
      (fun (i j : Fin n) => f (supportProjection μ K hK hμ ((fun _ : Fin n => x₀) i),
          supportProjection ν K hK hν ((fun _ : Fin n => x₀) j))) =
        fun (_ : Fin n) (_ : Fin n) =>
          f (supportProjection μ K hK hμ x₀, supportProjection ν K hK hν x₀) := rfl
  rw [hcost, hprobe]
  unfold perturbedAssignmentValue perturbedEdgeCost
  simp only [zero_add]
  set c : ℝ := t * f (supportProjection μ K hK hμ x₀, supportProjection ν K hK hν x₀)
  change assignmentCost (fun (_ : Fin n) (_ : Fin n) => c)
    (optimalAssignment (fun (_ : Fin n) (_ : Fin n) => c)) / (n : ℝ) = c
  have hval :
      assignmentCost (fun (_ : Fin n) (_ : Fin n) => c)
        (optimalAssignment (fun (_ : Fin n) (_ : Fin n) => c)) = (n : ℝ) * c := by
    simp [assignmentCost, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hval]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn)

/-! ## 4. The geometric bundle from the paper's tube data -/

/-- The paper's calibrated tube, the 1-Lipschitz potential and the pointwise
clock atomlessness supply the whole paper-side geometric bundle: the a.e. ray
clusters are the trivial (empty) ones and the Palm sample law is the zero one. -/
def paperGeometricHypothesesOfTube {Z : Type uZ}
    (T : CalibratedTube F u Z)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hμclock : PointwiseClockAtomless (μ : Measure M) u)
    (hνclock : PointwiseClockAtomless (ν : Measure M) u) :
    FinslerPaperGeometricHypotheses F u μ ν where
  interior_nonempty := interiorNonempty_of_calibratedTube T hu
  source_rayCluster := emptyRayClusterData F u (μ : Measure M)
  target_rayCluster := emptyRayClusterData F u (ν : Measure M)
  source_clock_atomless := hμclock
  target_clock_atomless := hνclock
  palm_sample_law := trivialPalmSampleLaw

/-- The paper-side geometric bundle is inhabited from the tube hypothesis. -/
theorem nonempty_geometric_of_tube {Z : Type uZ} (T : CalibratedTube F u Z)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hμclock : PointwiseClockAtomless (μ : Measure M) u)
    (hνclock : PointwiseClockAtomless (ν : Measure M) u) :
    Nonempty (FinslerPaperGeometricHypotheses F u μ ν) :=
  ⟨paperGeometricHypothesesOfTube T hu hμclock hνclock⟩

/-! ## 5. The conditional endgame bundle is inhabited -/

/-- **Non-vacuity of the conditional endgame.**  For every paper-side geometric
bundle |G|, every pair of compact carriers containing the population marginals
a.e., every probability sample law |P| and every constant source/target sample
pair |(x0, x0)|, the conditional endgame structure is inhabited.

The analytic fields are explicit: |pressureLower = pressureUpper = samplePressure
p q|, |radius = 1|, and the two probability limits hold with equality because the
supported empirical pressure of the constant pair is exactly |t * f (p, q)|.
Consequently no endgame field is impossible, and no field refutes another. -/
theorem nonempty_conditionalEndgameHypotheses_of_geometric
    (G : FinslerPaperGeometricHypotheses F u μ ν)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (hP : ∀ n, IsProbabilityMeasure (P n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (x₀ : M)
    (hX : ∀ n i s, X n i s = x₀) (hY : ∀ n j s, Y n j s = x₀) :
    Nonempty (FinslerConditionalEndgameHypotheses F u μ ν hA hB hμA hνB P X Y) := by
  classical
  let p : ↥(A ∪ B) :=
    supportProjection μ (A ∪ B) (hA.union hB).measurableSet
      (hμA.mono fun x hx => Or.inl hx) x₀
  let q : ↥(A ∪ B) :=
    supportProjection ν (A ∪ B) (hA.union hB).measurableSet
      (hνB.mono fun y hy => Or.inr hy) x₀
  refine ⟨G, samplePressure p q, samplePressure p q, (fun _ => (1 : ℝ)),
    (fun _ => one_pos), ?_, ?_, ?_⟩
  · unfold FinalValueIdentification
    intro f t
    rfl
  · unfold FinalProbLowerData
    intro f t ε ht hε
    have hpoint : ∀ (n : ℕ) (s : Ω n),
        finslerSupportedPressure F μ ν (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun x hx => Or.inl hx) (hνB.mono fun y hy => Or.inr hy)
          (fun i => X n i s) (fun i => Y n i s) u
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t =
            t * f (p, q) := by
      intro n s
      exact finslerSupportedPressure_const (μ := μ) (ν := ν) (K := A ∪ B)
        (hK := (hA.union hB).measurableSet)
        (hμ := hμA.mono fun x hx => Or.inl hx)
        (hν := hνB.mono fun y hy => Or.inr hy) (F := F) (n := n + 1)
        (Nat.succ_ne_zero n) (X := fun i => X n i s) (Y := fun j => Y n j s)
        (φ := u) (x₀ := x₀) (fun i => hX n i s) (fun j => hY n j s)
    have hset : ∀ n : ℕ,
        {s : Ω n | finslerSupportedPressure F μ ν (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun x hx => Or.inl hx) (hνB.mono fun y hy => Or.inr hy)
          (fun i => X n i s) (fun i => Y n i s) u
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
            samplePressure p q f t - ε} = ∅ := by
      intro n
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, samplePressure_apply]
      rw [hpoint n s]
      intro h
      linarith
    have hzero : ∀ n : ℕ,
        (P n).real {s : Ω n | finslerSupportedPressure F μ ν (A ∪ B)
          (hA.union hB).measurableSet (hμA.mono fun x hx => Or.inl hx)
          (hνB.mono fun y hy => Or.inr hy) (fun i => X n i s) (fun i => Y n i s) u
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
            samplePressure p q f t - ε} = 0 := by
      intro n
      rw [hset n]
      simp
    simp only [hzero]
    exact tendsto_const_nhds
  · unfold FinalProbUpperData
    intro f t ε ht hε
    have hpoint : ∀ (n : ℕ) (s : Ω n),
        finslerSupportedPressure F μ ν (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun x hx => Or.inl hx) (hνB.mono fun y hy => Or.inr hy)
          (fun i => X n i s) (fun i => Y n i s) u
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t =
            t * f (p, q) := by
      intro n s
      exact finslerSupportedPressure_const (μ := μ) (ν := ν) (K := A ∪ B)
        (hK := (hA.union hB).measurableSet)
        (hμ := hμA.mono fun x hx => Or.inl hx)
        (hν := hνB.mono fun y hy => Or.inr hy) (F := F) (n := n + 1)
        (Nat.succ_ne_zero n) (X := fun i => X n i s) (Y := fun j => Y n j s)
        (φ := u) (x₀ := x₀) (fun i => hX n i s) (fun j => hY n j s)
    have hInt : ∀ n : ℕ,
        ∫ s, finslerSupportedPressure F μ ν (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun x hx => Or.inl hx) (hνB.mono fun y hy => Or.inr hy)
          (fun i => X n i s) (fun i => Y n i s) u
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n =
            t * f (p, q) := by
      intro n
      rw [show (fun s => finslerSupportedPressure F μ ν (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun x hx => Or.inl hx) (hνB.mono fun y hy => Or.inr hy)
          (fun i => X n i s) (fun i => Y n i s) u
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t) =
            fun _ => t * f (p, q) from funext (hpoint n)]
      haveI : IsProbabilityMeasure (P n) := hP n
      change ∫ _ : Ω n, t * f (p, q) ∂P n = t * f (p, q)
      rw [integral_const, measureReal_def, measure_univ]
      simp
    filter_upwards with n
    rw [hInt n, samplePressure_apply]
    linarith

/-- **The concrete witness from the paper's tube hypothesis.** -/
theorem nonempty_conditionalEndgameHypotheses {Z : Type uZ}
    (T : CalibratedTube F u Z)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hμclock : PointwiseClockAtomless (μ : Measure M) u)
    (hνclock : PointwiseClockAtomless (ν : Measure M) u)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (hP : ∀ n, IsProbabilityMeasure (P n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (x₀ : M)
    (hX : ∀ n i s, X n i s = x₀) (hY : ∀ n j s, Y n j s = x₀) :
    Nonempty (FinslerConditionalEndgameHypotheses F u μ ν hA hB hμA hνB P X Y) :=
  nonempty_conditionalEndgameHypotheses_of_geometric
    (paperGeometricHypothesesOfTube T hu hμclock hνclock)
    hA hB hμA hνB P hP X Y x₀ hX hY

end OTSelector.Reconstruction

