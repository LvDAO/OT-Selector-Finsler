import OTSelector.Reconstruction.FinslerOriginalKernelMarkedPoisson
import OTSelector.Reconstruction.FinslerOriginalCubePartitionGeometry
import OTSelector.Geometry.Finsler.Calibration.PopulationConditionalLaw
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# The normalized clock Markov kernel

The kernel-marked pressure lane is parametric in a Markov kernel K on the
position space whose fiber is the conditional clock law.  This module builds that
kernel from the population conditional window law:

* clockFiberNormalizer is the fiber integral of a jointly measurable conditional
  clock density f;
* clockBase is Lebesgue measure together with an atom at zero, the carrier on
  which the normalized-with-fallback fiber density lives;
* clockFiberDensity is the normalized fiber density: on normalized fibers it is
  the conditional density f (z, .), and on non-normalized fibers it gives the
  Dirac mass at zero, so every fiber is a probability measure;
* clockKernel f hf is the resulting Markov kernel, and
  clockKernel_apply_of_normalized is its defining formula: on a normalized fiber
  the mass of a measurable clock set C is the integral of f (z, .) over C;
* clockKernel_ae_eq_withDensity and clockKernel_ae_eq_condDistrib identify it
  with the plain withDensity fiber and with the regular conditional distribution
  of the clock given the label;
* compProd_clockKernel_eq_jointLaw proves that the label law composed with the
  clock kernel is exactly the joint law of (label, clock);
* cubeClockKernel, clockMarkedSeqLaw, clockMarkedPressure and
  clockMarkedScalePressure instantiate the kernel-marked Poisson/de-Poissonization
  lane of FinslerOriginalKernelMarkedPoisson at the clock kernel, read through a
  seed-label linear coordinate e.

The remaining atlas-level gap is documented at the end of the file: the present
construction works window by window, and the label law is identified with the
uniform cube law only under the uniform-intensity hypothesis of the cube
partition lane.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Manifold
open scoped NNReal ENNReal BigOperators Topology ContDiff
open Metric
open OTSelector.Probability OTSelector.Geometry

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {Z : Type*} [MeasurableSpace Z]

/-! ## The normalized conditional clock kernel -/

/-- The fiber normalizer of a jointly measurable conditional clock density. -/
noncomputable def clockFiberNormalizer (f : Z → ℝ → ℝ≥0∞) (z : Z) : ℝ≥0∞ :=
  ∫⁻ s, f z s ∂volume

/-- The fiber normalizer of a conditional clock density is measurable. -/
theorem measurable_clockFiberNormalizer {f : Z → ℝ → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) :
    Measurable (clockFiberNormalizer f) := by
  unfold clockFiberNormalizer
  exact hf.lintegral_prod_right

/-- The clock carrier measure: Lebesgue measure together with an atom at zero.
The atom carries the probability fallback on fibers where the conditional density
is not normalized. -/
noncomputable def clockBase : Measure ℝ := (volume : Measure ℝ) + Measure.dirac (0 : ℝ)

instance : SFinite clockBase := by
  unfold clockBase
  infer_instance

/-- The normalized conditional clock density with the probability fallback at
zero on non-normalized fibers. -/
noncomputable def clockFiberDensity (f : Z → ℝ → ℝ≥0∞) (z : Z) (s : ℝ) : ℝ≥0∞ :=
  if clockFiberNormalizer f z = 1 then (if s = 0 then 0 else f z s)
  else (if s = 0 then 1 else 0)

/-- Joint measurability of the normalized clock density with fallback. -/
theorem measurable_clockFiberDensity {f : Z → ℝ → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) :
    Measurable (Function.uncurry (clockFiberDensity f)) := by
  have hgood : MeasurableSet {p : Z × ℝ | clockFiberNormalizer f p.1 = 1} :=
    (measurable_clockFiberNormalizer hf).comp measurable_fst (measurableSet_singleton 1)
  have hzero : MeasurableSet {p : Z × ℝ | p.2 = (0 : ℝ)} :=
    (measurableSet_singleton 0).preimage measurable_snd
  have h1 : Measurable fun p : Z × ℝ => if p.2 = 0 then (0 : ℝ≥0∞) else f p.1 p.2 :=
    Measurable.ite hzero measurable_const hf
  have h2 : Measurable fun p : Z × ℝ => if p.2 = 0 then (1 : ℝ≥0∞) else 0 :=
    Measurable.ite hzero measurable_const measurable_const
  exact Measurable.ite hgood h1 h2

/-- **The normalized clock Markov kernel.**  Its fiber at a seed label is the
normalized conditional clock density; on fibers where the density is not
normalized it is the Dirac mass at zero. -/
noncomputable def clockKernel (f : Z → ℝ → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f)) : Kernel Z ℝ :=
  Kernel.withDensity (Kernel.const Z clockBase) (clockFiberDensity f)

/-- The clock kernel is a Markov kernel. -/
instance isMarkovKernel_clockKernel (f : Z → ℝ → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f)) : IsMarkovKernel (clockKernel f hf) := by
  refine ⟨fun z => ⟨?_⟩⟩
  have hd := measurable_clockFiberDensity hf
  rw [clockKernel, Kernel.withDensity_apply' (Kernel.const Z clockBase) hd z Set.univ,
    Kernel.const_apply, setLIntegral_univ]
  by_cases hz : clockFiberNormalizer f z = 1
  · have hsimp : (fun s : ℝ => clockFiberDensity f z s) = fun s => if s = 0 then 0 else f z s := by
      funext s
      unfold clockFiberDensity
      rw [if_pos hz]
    rw [hsimp, clockBase, lintegral_add_measure, lintegral_dirac]
    have hdirac : (if (0 : ℝ) = 0 then (0 : ℝ≥0∞) else f z 0) = 0 := if_pos rfl
    rw [hdirac, add_zero]
    have hcongr : (fun s : ℝ => if s = 0 then (0 : ℝ≥0∞) else f z s)
        =ᵐ[volume] (fun s => f z s) := by
      filter_upwards [show ∀ᵐ s : ℝ ∂volume, s ≠ 0 from by rw [ae_iff]; simp [measure_singleton]] with s hs
      rw [if_neg hs]
    rw [lintegral_congr_ae hcongr]
    exact hz
  · have hsimp : (fun s : ℝ => clockFiberDensity f z s) = fun s => if s = 0 then 1 else 0 := by
      funext s
      unfold clockFiberDensity
      rw [if_neg hz]
    rw [hsimp, clockBase, lintegral_add_measure, lintegral_dirac]
    have hvol : ∫⁻ s, (if s = (0 : ℝ) then (1 : ℝ≥0∞) else 0) ∂volume = 0 := by
      have hind : (fun s : ℝ => if s = 0 then (1 : ℝ≥0∞) else 0) =
          Set.indicator {0} (fun _ => (1 : ℝ≥0∞)) := by
        funext s
        by_cases hs : s = 0 <;> simp [hs]
      rw [hind, lintegral_indicator (measurableSet_singleton (0 : ℝ)),
        setLIntegral_one, measure_singleton]
    rw [hvol, zero_add]
    norm_num

/-- **The defining formula of the clock kernel on a normalized fiber.**  On a
fiber whose conditional density is normalized, the clock kernel is exactly the
conditional distribution with density f (z, .): the mass of a measurable clock
set C is the integral of the density over C. -/
theorem clockKernel_apply_of_normalized (f : Z → ℝ → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f)) {z : Z} (hz : clockFiberNormalizer f z = 1)
    {C : Set ℝ} (hC : MeasurableSet C) :
    clockKernel f hf z C = ∫⁻ s in C, f z s ∂volume := by
  have hd := measurable_clockFiberDensity hf
  have hsimp : (fun s : ℝ => clockFiberDensity f z s) = fun s => if s = 0 then 0 else f z s := by
    funext s
    unfold clockFiberDensity
    rw [if_pos hz]
  rw [clockKernel, Kernel.withDensity_apply' (Kernel.const Z clockBase) hd z C,
    Kernel.const_apply, hsimp, clockBase, Measure.restrict_add, lintegral_add_measure]
  have hzero : ∀ᵐ s : ℝ ∂volume, s ≠ 0 := by
    rw [ae_iff]
    simp [measure_singleton]
  have hvol : ∫⁻ s in C, (if s = 0 then (0 : ℝ≥0∞) else f z s) ∂volume
      = ∫⁻ s in C, f z s ∂volume := by
    rw [← lintegral_indicator hC, ← lintegral_indicator hC]
    refine lintegral_congr_ae ?_
    filter_upwards [hzero] with s hs
    by_cases hmem : s ∈ C
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, if_neg hs]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
  have hdirac : ∫⁻ s in C, (if s = 0 then (0 : ℝ≥0∞) else f z s) ∂(Measure.dirac (0 : ℝ)) = 0 := by
    rw [← lintegral_indicator hC, lintegral_dirac]
    by_cases h0 : (0 : ℝ) ∈ C
    · rw [Set.indicator_of_mem h0]
      simp
    · rw [Set.indicator_of_notMem h0]
  rw [hvol, hdirac, add_zero]

/-- **Almost everywhere normalized fibers give the plain conditional density.**
If the conditional clock density is normalized almost everywhere, then almost
everywhere the clock kernel is the plain density fiber. -/
theorem clockKernel_ae_eq_withDensity (f : Z → ℝ → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f)) (lambda : Measure Z)
    (hn : ∀ᵐ z ∂lambda, clockFiberNormalizer f z = 1) :
    ∀ᵐ z ∂lambda, clockKernel f hf z = (volume : Measure ℝ).withDensity (f z) := by
  filter_upwards [hn] with z hz
  ext C hC
  rw [clockKernel_apply_of_normalized f hf hz hC, withDensity_apply _ hC]

/-- **Almost everywhere positivity of the clock normalizer.** -/
theorem clockFiberNormalizer_pos_ae (f : Z → ℝ → ℝ≥0∞) (lambda : Measure Z)
    (hn : ∀ᵐ z ∂lambda, clockFiberNormalizer f z = 1) :
    ∀ᵐ z ∂lambda, 0 < clockFiberNormalizer f z := by
  filter_upwards [hn] with z hz
  rw [hz]
  norm_num

/-- **Almost everywhere finiteness of the clock normalizer.** -/
theorem clockFiberNormalizer_ne_top_ae (f : Z → ℝ → ℝ≥0∞) (lambda : Measure Z)
    (hn : ∀ᵐ z ∂lambda, clockFiberNormalizer f z = 1) :
    ∀ᵐ z ∂lambda, clockFiberNormalizer f z ≠ ⊤ := by
  filter_upwards [hn] with z hz
  rw [hz]
  norm_num

/-- **Almost everywhere nonvanishing of the clock normalizer.** -/
theorem clockFiberNormalizer_ne_zero_ae (f : Z → ℝ → ℝ≥0∞) (lambda : Measure Z)
    (hn : ∀ᵐ z ∂lambda, clockFiberNormalizer f z = 1) :
    ∀ᵐ z ∂lambda, clockFiberNormalizer f z ≠ 0 := by
  filter_upwards [hn] with z hz
  rw [hz]
  norm_num

/-! ## The clock kernel is the conditional clock law of the population window law -/

section Population

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- **The clock kernel is the regular conditional distribution of the clock
given the label.**  Under the population conditional window law, the clock kernel
built from the conditional density agrees almost everywhere with the conditional
distribution of the clock given the label.  This is the conditional probability
description used by the kernel-marked pressure lane. -/
theorem clockKernel_ae_eq_condDistrib
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {kappa : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {eta : Measure M} [IsFiniteMeasure eta] {rho : M → ℝ} {v : ℕ → E → ℝ}
    (hW : PopulationConditionalWindowLaw P a kappa lambda eta rho v) :
    ∀ᵐ z ∂lambda,
      clockKernel (fun z s => populationConditionalDensity P a kappa lambda rho v (z, s))
        hW.density_measurable z = condDistrib u a eta z := by
  filter_upwards [clockKernel_ae_eq_withDensity
      (fun z s => populationConditionalDensity P a kappa lambda rho v (z, s))
      hW.density_measurable lambda hW.normalized, hW.conditional_law] with z hz hcond
  rw [hz]
  exact hcond

/-- **The joint law of (label, clock) is the label law composed with the clock
kernel.**  Under the population conditional window law the joint law of the
label and the clock is exactly the composition product of the label law with the
normalized clock kernel, which is the interface expected by the kernel-marked
pressure lane. -/
theorem compProd_clockKernel_eq_jointLaw
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {kappa : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {eta : Measure M} [IsFiniteMeasure eta] {rho : M → ℝ} {v : ℕ → E → ℝ}
    (hu : AEMeasurable u eta)
    (hW : PopulationConditionalWindowLaw P a kappa lambda eta rho v) :
    lambda ⊗ₘ clockKernel (fun z s => populationConditionalDensity P a kappa lambda rho v (z, s))
        hW.density_measurable =
      eta.map (fun x => (a x, u x)) := by
  haveI hlambda_fin : IsFiniteMeasure lambda := by
    rw [← hW.label_law]
    infer_instance
  haveI hlambda_sf : SFinite lambda := inferInstance
  calc lambda ⊗ₘ clockKernel
        (fun z s => populationConditionalDensity P a kappa lambda rho v (z, s))
        hW.density_measurable
      = lambda ⊗ₘ condDistrib u a eta :=
        Measure.compProd_congr (clockKernel_ae_eq_condDistrib hW)
    _ = eta.map (fun x => (a x, u x)) := by
        rw [← hW.label_law]
        exact compProd_map_condDistrib (μ := eta) (X := a) (Y := u) hu

end Population

/-! ## Instantiation of the kernel-marked pressure lane at the clock kernel -/

section Instantiation

variable {q : ℕ} {Z' : Type*} [NormedAddCommGroup Z'] [NormedSpace ℝ Z'] [MeasurableSpace Z'] [BorelSpace Z']

/-- **The clock kernel in cube coordinates.**  Reading the seed label through a
linear coordinate equivalence to `Fin q → ℝ` gives the Markov kernel on the
cube-coordinate space whose fiber is the conditional clock law; this is the kernel
`K` of the kernel-marked pressure lane. -/
noncomputable def cubeClockKernel (f : Z' → ℝ → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f)) (e : Z' ≃L[ℝ] (Fin q → ℝ)) :
    Kernel (Fin q → ℝ) ℝ :=
  Kernel.withDensity (Kernel.const (Fin q → ℝ) clockBase)
    (fun x s => clockFiberDensity f (e.symm x) s)

/-- Joint measurability of the cube-coordinate clock density. -/
theorem measurable_cubeClockDensity {q : ℕ} (f : Z' → ℝ → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f)) (e : Z' ≃L[ℝ] (Fin q → ℝ)) :
    Measurable (Function.uncurry (fun x : Fin q → ℝ => fun s => clockFiberDensity f (e.symm x) s)) := by
  have hd := measurable_clockFiberDensity hf
  have hmap : Measurable fun p : (Fin q → ℝ) × ℝ => (e.symm p.1, p.2) :=
    (e.symm.continuous.measurable.comp measurable_fst).prodMk measurable_snd
  exact hd.comp hmap

/-- The cube-coordinate clock kernel is a Markov kernel. -/
instance isMarkovKernel_cubeClockKernel {q : ℕ} (f : Z' → ℝ → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f)) (e : Z' ≃L[ℝ] (Fin q → ℝ)) :
    IsMarkovKernel (cubeClockKernel (q := q) f hf e) := by
  refine ⟨fun x => ⟨?_⟩⟩
  have h := (isMarkovKernel_clockKernel f hf).isProbabilityMeasure (e.symm x)
  rw [cubeClockKernel, Kernel.withDensity_apply'
      (Kernel.const (Fin q → ℝ) clockBase) (measurable_cubeClockDensity f hf e) x Set.univ,
    Kernel.const_apply, setLIntegral_univ]
  rw [clockKernel, Kernel.withDensity_apply (Kernel.const Z' clockBase)
    (measurable_clockFiberDensity hf), Kernel.const_apply] at h
  have h2 := h.measure_univ
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h2
  exact h2

/-- **The kernel-marked Poisson sequence law at the clock kernel.** -/
noncomputable def clockMarkedSeqLaw (f : Z' → ℝ → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f)) {q : ℕ} (e : Z' ≃L[ℝ] (Fin q → ℝ)) :
    Measure (ℕ → (Fin q → ℝ) × ℝ) :=
  kernelMarkedSeqLaw q ℝ (cubeClockKernel (q := q) f hf e)

/-- **The kernel-marked Poissonized pressure at the clock kernel.** -/
noncomputable def clockMarkedPressure (f : Z' → ℝ → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f)) {q : ℕ} (e : Z' ≃L[ℝ] (Fin q → ℝ))
    (r : ℝ≥0) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  kernelMarkedPressure q ℝ ℝ (cubeClockKernel (q := q) f hf e)
    (cubeClockKernel (q := q) f hf e) r kin g t

/-- **The scale-normalized kernel-marked pressure at the clock kernel.** -/
noncomputable def clockMarkedScalePressure (f : Z' → ℝ → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f)) {q : ℕ} (e : Z' ≃L[ℝ] (Fin q → ℝ))
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (R t : ℝ) : ℝ :=
  kernelMarkedScalePressure q ℝ ℝ (cubeClockKernel (q := q) f hf e)
    (cubeClockKernel (q := q) f hf e) kin g R t

end Instantiation

/-! ## Remaining gap: the atlas-level global refinement

The construction above is exact at the level of the population conditional window
law and produces a genuine Markov clock kernel with the conditional probability
description and the composition-product joint law.  Two producer-level steps are
deliberately left to the atlas lane:

* **Refined atlas cover equality.**  The clock kernel is attached to the
  population windows \(P j\) of the original countable atlas.  Passing to a
  refined atlas whose cores are the certified chart balls of
  `exists_ball_core_C11_data` and whose retained pieces cover the original
  retained pieces requires the refinement-cover/partition lemma (the refined
  atlas of `FinslerOriginalGlobalRefinedAtlas` provides the family and the uniform
  cube coverage, but not the exact cover equality with the original atlas).
* **Label law versus the uniform cube law.**  The joint law identity above is in
  label coordinates: `lambda ⊗ₘ clockKernel = eta.map (a, u)`.  Its cube-coordinate
  form `cubeMeasure ⊗ₘ cubeClockKernel` additionally requires the label law to be the
  uniform cube law, which holds under the uniform-intensity hypothesis of the cube
  partition lane (`labelRestrict_eq_smul_reference_iff` of
  `FinslerOriginalCubePartitionGeometry`); without that hypothesis the label law is
  the normalized intensity-weighted Haar law instead.
-/

end OTSelector.Reconstruction
