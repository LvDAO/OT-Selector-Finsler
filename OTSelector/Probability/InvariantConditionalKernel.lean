import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Disintegration.Unique

/-!
# Invariant Conditional Kernel

Conditions: Finite joint law on root×nonempty standard Borel X; measurable actions preserving that joint law while fixing the root. A countable dense parameter encoding, pointwise parameter continuity, first-countable parameter space, and the stated probability-law separation hypotheses support the all-parameter result.

Objects: Actual conditional kernels invariant under each action, then simultaneously under every parameter on one full root set.

Proof detail: Map each conditional kernel by one action and use uniqueness of disintegration. Intersect only a countable family of full root sets. Bounded continuous probes and dominated convergence give continuity of pushed-forward probabilities; closedness extends invariance from dense parameters to all parameters.

Relation to primary sources: This is a local combination of conditional-law uniqueness, countable intersections, weak continuity, and density. It is not an uncountable intersection of exceptional sets, and no group-action or compactness assumption is silently added.

References:
* D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009), 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary. https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=25
* Rick Durrett, Probability: Theory and Examples, fifth edition (2019 author PDF), Section 4.1, conditional-expectation definition and Uniqueness argument, pp. 205–206; Section 4.1.3, Theorems 4.1.16–4.1.18, pp. 214–215. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=213
* D. H. Fremlin, Measure Theory, Volume 4, Chapter 43, 437J(d), (f), pp. 61–62; 437K–437L, pp. 62–63: narrow topology and bounded continuous integral tests. https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61
* Rick Durrett, Probability: Theory and Examples, fifth edition (2019 author PDF), Section 1.6.2, Theorem 1.6.7, p. 30: dominated convergence. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=38
-/
/-!
# Conditional stationarity over the original macroscopic root

A spatial action fixes the retained macroscopic root. Uniqueness of the actual
conditional kernel transfers invariance of the joint law to its conditional
scene laws. Separability and continuity in the spatial parameter give one common
full-measure root set carrying every spatial translation.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Joint stationarity that fixes the original tag disintegrates into actual
conditional stationarity for each fixed physical translation. -/
theorem ae_measurePreserving_condKernel_of_joint
    {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    [StandardBorelSpace X] [Nonempty X]
    (ρ : Measure (T × X)) [IsFiniteMeasure ρ]
    {shift : X → X} (hshift : Measurable shift)
    (hjoint : MeasurePreserving (Prod.map id shift) ρ ρ) :
    ∀ᵐ w ∂ρ.fst, MeasurePreserving shift (ρ.condKernel w) (ρ.condKernel w) := by
  have hdis : ρ = ρ.fst ⊗ₘ (ρ.condKernel.map shift) := by
    rw [Measure.compProd_map hshift, ρ.disintegrate ρ.condKernel]
    exact hjoint.map_eq.symm
  have hae := eq_condKernel_of_measure_eq_compProd (ρ.condKernel.map shift) hdis
  filter_upwards [hae] with w hw
  exact ⟨hshift, by simpa only [Kernel.map_apply _ hshift] using hw⟩

/-- Countably many physical translations hold on one original full-measure
macroscopic root set. -/
theorem ae_forall_measurePreserving_condKernel_of_joint
    {T X D : Type*} [MeasurableSpace T] [MeasurableSpace X]
    [StandardBorelSpace X] [Nonempty X] [Countable D]
    (ρ : Measure (T × X)) [IsFiniteMeasure ρ]
    (shift : D → X → X) (hshift : ∀ d, Measurable (shift d))
    (hjoint : ∀ d, MeasurePreserving (Prod.map id (shift d)) ρ ρ) :
    ∀ᵐ w ∂ρ.fst, ∀ d, MeasurePreserving (shift d) (ρ.condKernel w) (ρ.condKernel w) :=
  ae_all_iff.mpr (fun d ↦ ae_measurePreserving_condKernel_of_joint ρ (hshift d) (hjoint d))

/-- Pointwise continuity of physical reroots gives continuity of their
pushforward probability laws, with no uniform continuity or compactness premise
on the full scene space. -/
theorem continuous_probability_map_of_pointwise_parameter
    {V X : Type*} [TopologicalSpace V] [FirstCountableTopology V] [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : ProbabilityMeasure X) (action : V → X → X)
    (hm : ∀ v, Measurable (action v)) (hc : ∀ x, Continuous (fun v ↦ action v x)) :
    Continuous (fun v ↦ ν.map (hm v).aemeasurable) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have h : Tendsto (fun v' ↦ ∫ x, f (action v' x) ∂(ν : Measure X)) (𝓝 v)
      (𝓝 (∫ x, f (action v x) ∂(ν : Measure X))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ ‖f‖)
    · exact .of_forall (fun v' ↦ (f.continuous.measurable.comp (hm v')).aestronglyMeasurable)
    · exact .of_forall (fun _ ↦ .of_forall (fun x ↦ f.norm_coe_le_norm (action _ x)))
    · exact integrable_const _
    · exact .of_forall (fun x ↦ (f.continuous.tendsto _).comp ((hc x).tendsto v))
  have heq (v' : V) : (∫ x, f x ∂(ν.map (hm v').aemeasurable : Measure X)) =
      ∫ x, f (action v' x) ∂(ν : Measure X) :=
    integral_map (hm v').aemeasurable f.continuous.measurable.aestronglyMeasurable
  simpa only [heq] using h

/-- Invariance on a dense parameter family extends to every physical
translation through the actual probability law's continuous pushforward. -/
theorem measurePreserving_of_dense_parameters
    {V X D : Type*} [TopologicalSpace V] [FirstCountableTopology V] [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [HasOuterApproxClosed X]
    (ν : ProbabilityMeasure X) (action : V → X → X)
    (hm : ∀ v, Measurable (action v)) (hc : ∀ x, Continuous (fun v ↦ action v x))
    (encode : D → V) (hdense : DenseRange encode)
    (hinv : ∀ d, MeasurePreserving (action (encode d)) (ν : Measure X) (ν : Measure X)) :
    ∀ v, MeasurePreserving (action v) (ν : Measure X) (ν : Measure X) := by
  have hclosed : IsClosed {v | ν.map (hm v).aemeasurable = ν} :=
    isClosed_eq (continuous_probability_map_of_pointwise_parameter ν action hm hc) continuous_const
  have hsub : range encode ⊆ {v | ν.map (hm v).aemeasurable = ν} := by
    rintro _ ⟨d, rfl⟩
    apply Subtype.ext
    exact (hinv d).map_eq
  intro v
  have hv := (closure_minimal hsub hclosed) (hdense v)
  exact ⟨hm v, congrArg (fun p : ProbabilityMeasure X ↦ (p : Measure X)) hv⟩

/-- The joint original-root law supplies one full-measure set of conditional
scene laws invariant under every physical translation. Countable dense spatial
parameters and pointwise reroot continuity are the only countability inputs. -/
theorem ae_forall_measurePreserving_condKernel_of_joint_dense
    {T V X D : Type*} [MeasurableSpace T] [TopologicalSpace V] [FirstCountableTopology V] [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [HasOuterApproxClosed X]
    [StandardBorelSpace X] [Nonempty X] [Countable D]
    (ρ : Measure (T × X)) [IsFiniteMeasure ρ]
    (action : V → X → X) (hm : ∀ v, Measurable (action v))
    (hc : ∀ x, Continuous (fun v ↦ action v x))
    (encode : D → V) (hdense : DenseRange encode)
    (hjoint : ∀ d, MeasurePreserving (Prod.map id (action (encode d))) ρ ρ) :
    ∀ᵐ w ∂ρ.fst, ∀ v, MeasurePreserving (action v) (ρ.condKernel w) (ρ.condKernel w) := by
  filter_upwards [ae_forall_measurePreserving_condKernel_of_joint ρ
    (fun d ↦ action (encode d)) (fun d ↦ hm (encode d)) hjoint] with w hw
  exact measurePreserving_of_dense_parameters
    ⟨ρ.condKernel w, inferInstance⟩ action hm hc encode hdense hw

end OTSelector.Reconstruction
