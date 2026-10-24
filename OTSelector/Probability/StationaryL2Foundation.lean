import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.Probability.IdentDistrib
import Mathlib.Topology.Sequences
import OTSelector.Probability.InvariantEventSigma

/-!
# Probability.StationaryL2Foundation

## Lemma skeleton

* **Conditions:** Measure-preserving indexed transformations and Hilbert L2; the group formulas have an additive action. Strong continuity follows from almost-everywhere continuous representatives with identical distributions under a finite law.
* **Objects:** Invariant-event sigma-field characterizations, conditional orthogonal projection and stationary covariance positivity/continuity bounds.
* **Proof detail:** Identify invariant measurable representatives, identify the L2 subspace with fixed vectors, use conditional expectation as orthogonal projection, establish L2 continuity from identical-distribution uniform integrability, and recognize covariance matrices as Gram matrices.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap24.pdf#page=36): Theorem 244M and Section 244N(a)–(b), pp. 36–37.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=61): Section 1.4, Exercises 1.4.12–1.4.13, pp. 52–53.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=233): Section 8A, Theorem 8.11, p. 218; Example 8.14, p. 219 (L2 Cauchy–Schwarz).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=107): Section 3B, Theorem 3.31, p. 92 (Dominated Convergence).

Source relation (composition): Hilbert/conditional-expectation foundation and positive-definite covariance, before any spectral measure representation.
-/

/-! The Hilbert-space foundation for stationary-current spectral analysis.
The fixed subspace of the actual measure-preserving transformations is exactly
L² of the almost surely invariant event sigma algebra. Its orthogonal projection
is the actual conditional expectation, so conditional centering removes the
whole invariant Hilbert component before a spectral measure is constructed. -/

open Set Function Filter MeasureTheory
open scoped ENNReal InnerProductSpace Topology ComplexOrder
noncomputable section

namespace OTSelector.Probability

variable {Ω I V : Type*} [MeasurableSpace Ω]

/-- A countably separated observable is measurable for the actual invariant
sigma algebra exactly when every transformation preserves it almost surely.
The null set may depend on the transformation. -/
theorem measurable_aeInvariantEventSigma_iff
    [MeasurableSpace V] [MeasurableSpace.CountablySeparated V]
    (P : Measure Ω) (T : I → Ω → Ω) {f : Ω → V} :
    Measurable[aeInvariantEventSigma P T] f ↔
      Measurable f ∧ ∀ i, f ∘ T i =ᵐ[P] f := by
  constructor
  · intro hf
    refine ⟨hf.mono (aeInvariantEventSigma_le P T) le_rfl, fun i ↦ ?_⟩
    apply Filter.EventuallyEq.of_forall_separating_preimage MeasurableSet
    intro A hA
    exact (hf hA).2 i
  · rintro ⟨hf, hinv⟩ A hA
    refine ⟨hf hA, fun i ↦ ?_⟩
    filter_upwards [hinv i] with ω hω
    exact congrArg (fun v ↦ v ∈ A) hω

variable [NormedAddCommGroup V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- Almost strongly measurable invariant observables are precisely the
observables measurable for the actual invariant event sigma algebra. -/
theorem aestronglyMeasurable_aeInvariantEventSigma_iff
    (P : Measure Ω) (T : I → Ω → Ω)
    (hT : ∀ i, MeasurePreserving (T i) P P) {f : Ω → V} :
    AEStronglyMeasurable[aeInvariantEventSigma P T] f P ↔
      AEStronglyMeasurable f P ∧ ∀ i, f ∘ T i =ᵐ[P] f := by
  constructor
  · intro hf
    obtain ⟨g, hg, hfg⟩ := hf
    have hgm := (measurable_aeInvariantEventSigma_iff P T).1 hg.measurable
    refine ⟨hg.mono (aeInvariantEventSigma_le P T) |>.aestronglyMeasurable.congr hfg.symm,
      fun i ↦ ?_⟩
    exact ((hT i).quasiMeasurePreserving.ae_eq_comp hfg).trans ((hgm.2 i).trans hfg.symm)
  · rintro ⟨hf, hinv⟩
    obtain ⟨g, hg, hfg⟩ := hf
    have hginv (i : I) : g ∘ T i =ᵐ[P] g :=
      ((hT i).quasiMeasurePreserving.ae_eq_comp hfg.symm).trans ((hinv i).trans hfg)
    exact ⟨g, ((measurable_aeInvariantEventSigma_iff P T).2
      ⟨hg.measurable, hginv⟩).stronglyMeasurable, hfg⟩

variable [InnerProductSpace ℝ V]

/-- The invariant L² subspace is exactly the joint fixed subspace of all
Koopman pullbacks. This uses the full transformation family, including
uncountably many spatial translations. -/
theorem mem_lpMeas_aeInvariantEventSigma_iff
    (P : Measure Ω) (T : I → Ω → Ω)
    (hT : ∀ i, MeasurePreserving (T i) P P) (f : Lp V 2 P) :
    f ∈ lpMeas V ℝ (aeInvariantEventSigma P T) 2 P ↔
      ∀ i, Lp.compMeasurePreserving (T i) (hT i) f = f := by
  rw [mem_lpMeas_iff_aestronglyMeasurable,
    aestronglyMeasurable_aeInvariantEventSigma_iff P T hT]
  constructor
  · rintro ⟨_, hf⟩ i
    apply Lp.ext
    exact (Lp.coeFn_compMeasurePreserving f (hT i)).trans (hf i)
  · intro hf
    refine ⟨Lp.aestronglyMeasurable f, fun i ↦ ?_⟩
    exact (Lp.coeFn_compMeasurePreserving f (hT i)).symm.trans
      (Filter.Eventually.of_forall fun ω ↦ congrArg (fun g : Lp V 2 P ↦ g ω) (hf i))

variable [CompleteSpace V]

/-- The actual invariant conditional L² expectation is fixed by every
measure-preserving transformation, rather than only by one chosen shift. -/
theorem compMeasurePreserving_condExpL2_aeInvariantEventSigma
    (P : Measure Ω) (T : I → Ω → Ω)
    (hT : ∀ i, MeasurePreserving (T i) P P) (f : Lp V 2 P) (i : I) :
    Lp.compMeasurePreserving (T i) (hT i)
      (condExpL2 V ℝ (aeInvariantEventSigma_le P T) f : Lp V 2 P) =
        (condExpL2 V ℝ (aeInvariantEventSigma_le P T) f : Lp V 2 P) := by
  exact (mem_lpMeas_aeInvariantEventSigma_iff P T hT _).1
    (condExpL2 V ℝ (aeInvariantEventSigma_le P T) f).property i

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
/-- The original Banach conditional expectation and the Hilbert orthogonal
projection have exactly the same zero component. -/
theorem condExpL2_aeInvariantEventSigma_eq_zero_of_condExp_eq_zero
    (P : Measure Ω) [IsFiniteMeasure P] (T : I → Ω → Ω) (f : Lp V 2 P)
    (hf : P[f | aeInvariantEventSigma P T] =ᵐ[P] fun _ ↦ 0) :
    (condExpL2 V ℝ (aeInvariantEventSigma_le P T) f : Lp V 2 P) = 0 := by
  apply Lp.ext
  have he := (Lp.memLp f).condExpL2_ae_eq_condExp
    (𝕜 := ℝ) (aeInvariantEventSigma_le P T)
  have hto : (Lp.memLp f).toLp (fun ω ↦ f ω) = f := by
    apply Lp.ext
    exact (Lp.memLp f).coeFn_toLp
  rw [hto] at he
  exact (he.trans hf).trans (Lp.coeFn_zero _ _ _).symm

/-- An invariant-conditionally centered L² observable is orthogonal to
EVERY invariant L² observable. This removes its entire invariant component. -/
theorem inner_eq_zero_of_condExp_aeInvariantEventSigma_eq_zero
    (P : Measure Ω) [IsFiniteMeasure P] (T : I → Ω → Ω)
    (hT : ∀ i, MeasurePreserving (T i) P P) (f g : Lp V 2 P)
    (hf : P[f | aeInvariantEventSigma P T] =ᵐ[P] fun _ ↦ 0)
    (hg : ∀ i, Lp.compMeasurePreserving (T i) (hT i) g = g) :
    ⟪f, g⟫_ℝ = 0 := by
  have hproj := condExpL2_aeInvariantEventSigma_eq_zero_of_condExp_eq_zero P T f hf
  rw [← inner_condExpL2_eq_inner_fun (aeInvariantEventSigma_le P T) f g
    (mem_lpMeas_iff_aestronglyMeasurable.1
      ((mem_lpMeas_aeInvariantEventSigma_iff P T hT g).2 hg)), hproj]
  exact inner_zero_left _

section MeanSquareContinuity

variable {X : Type*} [TopologicalSpace X] [SequentialSpace X]

omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V] in
/-- Sample-continuous identically distributed L² observations are continuous
as L²-valued observations. Their identical laws supply uniform integrability
internally, so no bounded random envelope or mixing hypothesis is required. -/
theorem continuous_toLp_of_ae_continuous_identDistrib
    (P : Measure Ω) [IsFiniteMeasure P] (J : X → Ω → V)
    (hJ : ∀ x, MemLp (J x) 2 P)
    (hd : ∀ x y, ProbabilityTheory.IdentDistrib (J x) (J y) P P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun x ↦ J x ω)) :
    Continuous (fun x ↦ (hJ x).toLp (J x)) := by
  apply continuous_iff_seqContinuous.2
  intro x x₀ hx
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n ↦ J (x n))
    (fun n ↦ hJ (x n)) (J x₀) (hJ x₀)).2
  have hui := ProbabilityTheory.MemLp.uniformIntegrable_of_identDistrib
    (p := 2) (j := 0) (by norm_num) (by norm_num) (hJ (x 0))
    (fun n ↦ hd (x n) (x 0))
  apply tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun n ↦ (hJ (x n)).aestronglyMeasurable) (hJ x₀) hui.2.1
  filter_upwards [hc] with ω hω
  exact (hω.tendsto x₀).comp hx

omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V] in
/-- Sample continuity of the genuine translated observable promotes its
Koopman orbit to strong L² continuity. Every translated L² norm and tail law
comes from the original measure-preserving scene transformations. -/
theorem continuous_compMeasurePreserving_of_ae_continuous
    (P : Measure Ω) [IsFiniteMeasure P] (T : X → Ω → Ω)
    (hT : ∀ x, MeasurePreserving (T x) P P) (f : Lp V 2 P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun x ↦ f (T x ω))) :
    Continuous (fun x ↦ Lp.compMeasurePreserving (T x) (hT x) f) := by
  have hJ (x : X) : MemLp (fun ω ↦ f (T x ω)) 2 P :=
    (Lp.memLp f).comp_measurePreserving (hT x)
  have hlaw (x : X) : P.map (f ∘ T x) = P.map f := by
    rw [← Measure.map_map (Lp.stronglyMeasurable f).measurable (hT x).measurable,
      (hT x).map_eq]
  have hd (x y : X) : ProbabilityTheory.IdentDistrib
      (fun ω ↦ f (T x ω)) (fun ω ↦ f (T y ω)) P P := by
    refine ⟨(hJ x).aestronglyMeasurable.aemeasurable,
      (hJ y).aestronglyMeasurable.aemeasurable, ?_⟩
    exact (hlaw x).trans (hlaw y).symm
  have hEq (x : X) : (hJ x).toLp (fun ω ↦ f (T x ω)) =
      Lp.compMeasurePreserving (T x) (hT x) f := by
    apply Lp.ext
    exact (hJ x).coeFn_toLp.trans (Lp.coeFn_compMeasurePreserving f (hT x)).symm
  simpa only [hEq] using continuous_toLp_of_ae_continuous_identDistrib P _ hJ hd hc

end MeanSquareContinuity

section Covariance

variable {G W 𝕜 : Type*} [AddCommGroup G] [RCLike 𝕜]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
  (P : Measure Ω) (T : G → Ω → Ω) (hT : ∀ v, MeasurePreserving (T v) P P)
  (hadd : ∀ v w ω, T v (T w ω) = T (v + w) ω)

include hadd

/-- Koopman pullback follows the exact additive cocycle of the original
transformations; no spectral representation is an input. -/
theorem compMeasurePreserving_add (f : Lp W 2 P) (v w : G) :
    Lp.compMeasurePreserving (T v) (hT v)
      (Lp.compMeasurePreserving (T w) (hT w) f) =
        Lp.compMeasurePreserving (T (v + w)) (hT (v + w)) f := by
  have hc : T w ∘ T v = T (v + w) := by
    funext ω
    simp only [Function.comp_apply, hadd, add_comm w v]
  simpa only [hc] using
    (Lp.compMeasurePreserving_comp_apply f (hT w) (hT v)).symm

/-- Two translated L² observations have covariance depending only on their
translation difference. The original law and observable are unchanged. -/
theorem inner_compMeasurePreserving_eq_difference
    (f g : Lp W 2 P) (v w : G) :
    ⟪Lp.compMeasurePreserving (T v) (hT v) f,
      Lp.compMeasurePreserving (T w) (hT w) g⟫_𝕜 =
        ⟪f, Lp.compMeasurePreserving (T (w - v)) (hT (w - v)) g⟫_𝕜 := by
  have hc := compMeasurePreserving_add P T hT hadd g v (w - v)
  have hv : v + (w - v) = w := by abel
  rw [hv] at hc
  rw [← hc]
  exact (Lp.compMeasurePreservingₗᵢ 𝕜 (T v) (hT v)).inner_map_map f _

/-- Every finite covariance matrix of a stationary L² observation is positive
semidefinite. This is the actual Gram positivity required before Bochner's
spectral-measure construction, with arbitrary complex coefficients when 𝕜=ℂ. -/
theorem posSemidef_stationaryL2Covariance
    {n : Type*} [Fintype n] (f : Lp W 2 P) (x : n → G) :
    Matrix.PosSemidef (fun i j ↦ ⟪f, Lp.compMeasurePreserving (T (x j - x i))
      (hT (x j - x i)) f⟫_𝕜 : Matrix n n 𝕜) := by
  have he : (fun i j ↦ ⟪f, Lp.compMeasurePreserving (T (x j - x i))
      (hT (x j - x i)) f⟫_𝕜 : Matrix n n 𝕜) =
      Matrix.gram 𝕜 (fun i ↦ Lp.compMeasurePreserving (T (x i)) (hT (x i)) f) := by
    ext i j
    exact (inner_compMeasurePreserving_eq_difference P T hT hadd f f (x i) (x j)).symm
  rw [he]
  exact Matrix.posSemidef_gram 𝕜 _

/-- Finite systems of different current components and different spatial
points have one positive-semidefinite block covariance matrix. -/
theorem posSemidef_stationaryL2CrossCovariance
    {n : Type*} [Fintype n] (f : n → Lp W 2 P) (x : n → G) :
    Matrix.PosSemidef (fun i j ↦ ⟪f i, Lp.compMeasurePreserving (T (x j - x i))
      (hT (x j - x i)) (f j)⟫_𝕜 : Matrix n n 𝕜) := by
  have he : (fun i j ↦ ⟪f i, Lp.compMeasurePreserving (T (x j - x i))
      (hT (x j - x i)) (f j)⟫_𝕜 : Matrix n n 𝕜) =
      Matrix.gram 𝕜 (fun i ↦ Lp.compMeasurePreserving (T (x i)) (hT (x i)) (f i)) := by
    ext i j
    exact (inner_compMeasurePreserving_eq_difference P T hT hadd (f i) (f j) (x i) (x j)).symm
  rw [he]
  exact Matrix.posSemidef_gram 𝕜 _

omit hadd [AddCommGroup G] in
/-- Stationary scalar covariance is uniformly bounded by the original two
L² norms, so its value at zero controls every translate. -/
theorem norm_stationaryL2Covariance_le (f g : Lp W 2 P) (v : G) :
    ‖⟪f, Lp.compMeasurePreserving (T v) (hT v) g⟫_𝕜‖ ≤ ‖f‖ * ‖g‖ := by
  simpa only [Lp.norm_compMeasurePreserving] using
    norm_inner_le_norm f (Lp.compMeasurePreserving (T v) (hT v) g)

end Covariance

end OTSelector.Probability

