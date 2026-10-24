import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Probability.Kernel.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Semicontinuity.Basic
import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasureTightness

/-!
## Lemma skeleton

* **Conditions:** A locally finite-measure carrier with measurable open evaluations and a countable precompact exhaustion.
* **Objects:** A measurable S-finite kernel equal to each original measure.
* **Proof detail:** Restrict to precompact windows, stratify their finite masses measurably and sum finite kernels.

## Mathematical sources

* Olav Kallenberg, *Random Measures, Theory and Applications (Springer 2017)*, Section 1.3 “Kernels and operators”, pp. 29–36; Section 1.4 “Disintegration”, pp. 37–42.
  https://link.springer.com/chapter/10.1007/978-3-319-41598-7_1
* D. H. Fremlin, *Measure Theory, Volume 4*, Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).
  https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18
* D. H. Fremlin, *Measure Theory, Volume 4*, Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61

**Relationship to the sources:** Neither stationarity nor a Palm theorem enters. The explicit S-finite decomposition is a local measurable-kernel implementation, with no same-form textbook theorem claimed.
-/

/-!
# The actual locally finite diffuse plan as a measurable S-finite kernel

Precompact open restrictions are finite and their open-set evaluations are
already proved measurable for the vague carrier. Exhaustion recovers the full
original measure. Explicit measurable finite-mass strata give a countable
finite-kernel decomposition rather than an assumed kernel interface.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

section PointwiseFinite
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

private def palmFiniteMassStripe (κ : Kernel A B) (k : ℕ) : Kernel A B :=
  Kernel.piecewise (s := {a | Nat.ceil ((κ a univ).toReal) = k})
    (measurableSet_eq_fun ((Kernel.measurable_coe κ MeasurableSet.univ).ennreal_toReal.nat_ceil)
      measurable_const) κ 0

private theorem palmFiniteMassStripe_apply (κ : Kernel A B) (k : ℕ) (a : A) (s : Set B) :
    palmFiniteMassStripe κ k a s =
      if Nat.ceil ((κ a univ).toReal) = k then κ a s else 0 := by
  simp [palmFiniteMassStripe, Kernel.piecewise_apply']

private instance palmFiniteMassStripeIsFinite (κ : Kernel A B)
    [∀ a, IsFiniteMeasure (κ a)] (k : ℕ) : IsFiniteKernel (palmFiniteMassStripe κ k) where
  exists_univ_le := by
    refine ⟨k, ENNReal.natCast_lt_top k, fun a ↦ ?_⟩
    rw [palmFiniteMassStripe_apply]
    split_ifs with hk
    · apply (ENNReal.toReal_le_toReal (measure_ne_top (κ a) univ) (ENNReal.natCast_ne_top k)).mp
      simpa only [ENNReal.toReal_natCast, ← hk] using Nat.le_ceil ((κ a univ).toReal)
    · exact bot_le

/-- A kernel with actual finite measures at every environment is S-finite;
its measurable finite-mass strata supply the finite decomposition. -/
theorem isSFiniteKernel_of_pointwise_finite (κ : Kernel A B)
    [∀ a, IsFiniteMeasure (κ a)] : IsSFiniteKernel κ := by
  have heq : κ = Kernel.sum (palmFiniteMassStripe κ) := by
    ext a s hs
    rw [Kernel.sum_apply' _ _ hs]
    simp [palmFiniteMassStripe_apply, eq_comm]
  rw [heq]
  infer_instance
end PointwiseFinite

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [PseudoMetrizableSpace X] [SigmaCompactSpace X]

omit [T2Space X] in
/-- A finite restriction of the actual diffuse vague carrier is Giry-measurable.
Open-set evaluations and the original compact bound discharge the interface. -/
theorem measurable_localFiniteMeasure_restrict_open {U K : Set X} (hU : IsOpen U)
    (hK : IsCompact K) (hUK : U ⊆ K) :
    Measurable (fun μ : LocalFiniteMeasure X ↦ (μ : Measure X).restrict U) := by
  let (μ : LocalFiniteMeasure X) : IsFiniteMeasure ((μ : Measure X).restrict U) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_mono hUK).trans_lt (hK.measure_lt_top (μ := (μ : Measure X)))⟩
  apply Measurable.measure_of_isPiSystem (by exact BorelSpace.measurable_eq) isPiSystem_isOpen
  · intro s hs
    simp only [Measure.restrict_apply hs.measurableSet]
    exact LocalFiniteMeasure.measurable_measure_open (hs.inter hU)
  · simpa only [Measure.restrict_apply_univ] using LocalFiniteMeasure.measurable_measure_open hU

omit [T2Space X] in
/-- The complete original locally finite diffuse plan is measurable as an
actual measure, not only through compact test coordinates. -/
theorem measurable_localFiniteMeasure_coe :
    Measurable (fun μ : LocalFiniteMeasure X ↦ (μ : Measure X)) := by
  let K := CompactExhaustion.choice X
  let U : ℕ → Set X := fun n ↦ interior (K n)
  have hcover : ⋃ n, U n = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨n, hn⟩ := K.exists_mem x
    exact ⟨n + 1, K.subset_interior_succ n hn⟩
  have hmono : Monotone U := fun _ _ h ↦ interior_mono (K.subset h)
  have hwindow (n : ℕ) : Measurable (fun μ : LocalFiniteMeasure X ↦ (μ : Measure X).restrict (U n)) :=
    measurable_localFiniteMeasure_restrict_open isOpen_interior (K.isCompact n) interior_subset
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have heq : (fun μ : LocalFiniteMeasure X ↦ (μ : Measure X) s) =
      (fun μ : LocalFiniteMeasure X ↦ ⨆ n, ((μ : Measure X).restrict (U n)) s) := by
    funext μ
    have hi : (⋃ n, s ∩ U n) = s := by rw [← inter_iUnion, hcover, inter_univ]
    calc
      (μ : Measure X) s = (μ : Measure X) (⋃ n, s ∩ U n) := congrArg _ hi.symm
      _ = ⨆ n, (μ : Measure X) (s ∩ U n) :=
        (Monotone.directed_le (fun a b h ↦ inter_subset_inter_right s (hmono h))).measure_iUnion
      _ = _ := by simp only [Measure.restrict_apply hs]
  rw [heq]
  exact Measurable.iSup (fun n ↦ (Measure.measurable_coe hs).comp (hwindow n))

/-- The actual diffuse vague scene plan is a measurable random measure kernel. -/
def localFiniteMeasureKernel : Kernel (LocalFiniteMeasure X) X :=
  ⟨fun μ ↦ (μ : Measure X), measurable_localFiniteMeasure_coe⟩

omit [T2Space X] in
@[simp]
theorem localFiniteMeasureKernel_apply (μ : LocalFiniteMeasure X) :
    localFiniteMeasureKernel μ = (μ : Measure X) := rfl

/-- The actual kernel admits a countable finite decomposition, built from
bounded shells of the original compact exhaustion and measurable mass strata. -/
instance localFiniteMeasureKernelIsSFinite :
    IsSFiniteKernel (localFiniteMeasureKernel (X := X)) := by
  let K := CompactExhaustion.choice X
  let U : ℕ → Set X := fun n ↦ interior (K n)
  have hcover : ⋃ n, U n = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨n, hn⟩ := K.exists_mem x
    exact ⟨n + 1, K.subset_interior_succ n hn⟩
  have hs (n : ℕ) : MeasurableSet (disjointed U n) :=
    MeasurableSet.disjointed (fun _ ↦ isOpen_interior.measurableSet) n
  let κ (n : ℕ) : Kernel (LocalFiniteMeasure X) X := localFiniteMeasureKernel.restrict (hs n)
  have hfinite (n : ℕ) (μ : LocalFiniteMeasure X) : IsFiniteMeasure (κ n μ) := by
    constructor
    change ((μ : Measure X).restrict (disjointed U n)) univ < ∞
    rw [Measure.restrict_apply_univ]
    exact (measure_mono ((disjointed_subset U n).trans interior_subset)).trans_lt
      ((K.isCompact n).measure_lt_top (μ := (μ : Measure X)))
  have hsf (n : ℕ) : IsSFiniteKernel (κ n) := by
    let (μ : LocalFiniteMeasure X) : IsFiniteMeasure (κ n μ) := hfinite n μ
    exact isSFiniteKernel_of_pointwise_finite (κ n)
  have heq : localFiniteMeasureKernel (X := X) = Kernel.sum κ := by
    ext μ s hsm
    rw [Kernel.sum_apply' _ _ hsm]
    have hμ := congrArg (fun ν : Measure X ↦ ν s)
      ((μ : Measure X).restrict_iUnion (disjoint_disjointed U) hs)
    rw [iUnion_disjointed, hcover, Measure.restrict_univ] at hμ
    simpa only [Measure.sum_apply _ hsm, κ, Kernel.restrict_apply,
      localFiniteMeasureKernel_apply] using hμ
  rw [heq]
  let (n : ℕ) : IsSFiniteKernel (κ n) := hsf n
  infer_instance

end OTSelector.Reconstruction
