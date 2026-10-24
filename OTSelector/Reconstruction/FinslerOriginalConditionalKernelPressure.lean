import OTSelector.Reconstruction.FinslerOriginalCubeCoverageConditionalMarks
import OTSelector.Probability.MarkedCountExpectation
import OTSelector.Probability.MarkedBlockLaw
import OTSelector.Limit.FinslerTileBlockMeasurability
import OTSelector.Reconstruction.FinslerTileBlockFrozenComparison
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Coordinate-dependent conditional mark kernels in the marked pressure lane

The marked pressure `markedScalePressure` of the frozen-comparison lane is stated
for *independent* mark laws `α` and `β`.  The actual population atlas, however,
produces the mark (clock) conditionally on the seed label: the exact clock
density given seed label `w` is `t ↦ J(t,w) ρ(t,w)`, proved in the cube-partition
lane.  This module implements the corresponding modelling change at the level of
the fixed marked block value:

* `condMarkedPointLaw` is the marked one-point law of a coordinate law together
  with a coordinate-dependent mark kernel, `μ ⊗ₘ K`; it is exactly the joint law
  of a cell whose coordinate and mark satisfy `ConditionalMarkLaw`.
* `condMarkedBlockValue` is the fixed marked block value at sizes `m`, `k` built
  from the marked cube positions and the marked kernels.
* `condMarkedBlockExpectation` is its expectation under `m` and `k` iid marked
  points with cube-uniform positions and coordinate-dependent marks; this is the
  coordinate-dependent-kernel marked pressure at a fixed sample size.
* `iidMarkedBlockExpectation` is the same fixed block expectation for
  *independent* marks `α`, `β`, which is the classical marked pressure integrand.

The main results show that the extension is conservative and well-behaved:

* `measurable_condMarkedBlockValue` and `integrable_condMarkedBlockValue`: the
  block value is measurable and integrable on the cube carrier, so the
  conditional-kernel pressure is well defined;
* `condMarkedBlockExpectation_const`: when the kernels are the constant kernels,
  the conditional-kernel pressure reduces exactly to the independent-mark
  pressure — the existing independent-mark results are the constant-kernel
  special case;
* `abs_condMarkedBlockExpectation_tilt_sub_le`: the conditional-kernel pressure
  is uniformly Lipschitz in the tilt with the marked cardinality as constant,
  which is the continuity input of the pressure lane;
* `conditionalMarkLaw_markedPointLaw`: the upper localization's mark hypotheses
  are precisely a description of the marked one-point law as a conditional-kernel
  composition product.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold
open MeasureTheory.Measure
open OTSelector.Probability
open Metric
open scoped Topology ENNReal NNReal BigOperators

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-! ## The coordinate-dependent marked block value -/

/-- The marked edge cost of a source cube point with mark a and a target cube
point with mark b: the marked kinetic kernel evaluated at the displacement,
tilted by the marked probe. -/
noncomputable def condMarkedEdgeCost (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ)
    (t : ℝ) (u v : Fin q → ℝ) (a : A) (b : B) : ℝ :=
  kin a b (v - u) + t * g a b

/-- The fixed marked block value at sizes m, k for the coordinate-dependent mark
model, read on the marked cube positions and marks. -/
noncomputable def condMarkedBlockValue (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ)
    (t : ℝ) {m k : ℕ} (S : Fin m → (Fin q → ℝ) × A) (T : Fin k → (Fin q → ℝ) × B) : ℝ :=
  OTSelector.PartialMatching.maxCardValue fun i j =>
    condMarkedEdgeCost kin g t (S i).1 (T j).1 (S i).2 (T j).2

/-- The marked one-point law of a coordinate law with a coordinate-dependent mark
kernel: the composition product of the coordinate law with the mark kernel. -/
noncomputable def condMarkedPointLaw (μ : Measure (Fin q → ℝ)) (K : Kernel (Fin q → ℝ) A) :
    Measure ((Fin q → ℝ) × A) :=
  μ ⊗ₘ K

/-- The law of m iid marked points with cube-uniform positions and marks drawn
from the coordinate-dependent kernel. -/
noncomputable def condMarkedArrayLaw (m : ℕ) (K : Kernel (Fin q → ℝ) A)
    [IsMarkovKernel K] : Measure (Fin m → (Fin q → ℝ) × A) :=
  Measure.pi fun _ : Fin m =>
    condMarkedPointLaw (OTSelector.Probability.cubeMeasure (Fin q) 1) K

/-- **The coordinate-dependent-kernel marked pressure at a fixed sample size.**
The expectation of the fixed marked block value under m and k iid marked points
whose positions are cube-uniform and whose marks are drawn from the conditional
kernels Ks, Kt given the position. -/
noncomputable def condMarkedBlockExpectation (kin : A → B → (Fin q → ℝ) → ℝ)
    (g : A → B → ℝ) (t : ℝ)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (m k : ℕ) : ℝ :=
  ∫ p : (Fin m → (Fin q → ℝ) × A) × (Fin k → (Fin q → ℝ) × B),
    condMarkedBlockValue kin g t p.1 p.2
    ∂((condMarkedArrayLaw m Ks).prod (condMarkedArrayLaw k Kt))

/-- **The independent-mark marked pressure at a fixed sample size.**  The
classical marked block integrand: m and k iid marked points with cube-uniform
positions and iid marks α, β, independent of the positions. -/
noncomputable def iidMarkedBlockExpectation (kin : A → B → (Fin q → ℝ) → ℝ)
    (g : A → B → ℝ) (t : ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (m k : ℕ) : ℝ :=
  ∫ p : (Fin m → (Fin q → ℝ) × A) × (Fin k → (Fin q → ℝ) × B),
    condMarkedBlockValue kin g t p.1 p.2
    ∂((Measure.pi fun _ : Fin m =>
          (OTSelector.Probability.cubeMeasure (Fin q) 1).prod α).prod
      (Measure.pi fun _ : Fin k =>
          (OTSelector.Probability.cubeMeasure (Fin q) 1).prod β))

/-! ## Measurability, uniform bounds and integrability -/

/-- Measurability of the conditional-kernel marked block value. -/
theorem measurable_condMarkedBlockValue (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ)
    (t : ℝ)
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g)) (m k : ℕ) :
    Measurable fun p : (Fin m → (Fin q → ℝ) × A) × (Fin k → (Fin q → ℝ) × B) =>
      condMarkedBlockValue kin g t p.1 p.2 := by
  classical
  apply OTSelector.PartialMatching.measurable_maxCardValue
  intro i j
  change Measurable fun p :
      (Fin m → (Fin q → ℝ) × A) × (Fin k → (Fin q → ℝ) × B) =>
      kin ((p.1 i).2) ((p.2 j).2) ((p.2 j).1 - (p.1 i).1) +
        t * g ((p.1 i).2) ((p.2 j).2)
  have hSa : Measurable fun p :
      (Fin m → (Fin q → ℝ) × A) × (Fin k → (Fin q → ℝ) × B) => (p.1 i).2 :=
    measurable_snd.comp ((measurable_pi_apply i).comp measurable_fst)
  have hTa : Measurable fun p :
      (Fin m → (Fin q → ℝ) × A) × (Fin k → (Fin q → ℝ) × B) => (p.2 j).2 :=
    measurable_snd.comp ((measurable_pi_apply j).comp measurable_snd)
  have hSu : Measurable fun p :
      (Fin m → (Fin q → ℝ) × A) × (Fin k → (Fin q → ℝ) × B) => (p.1 i).1 :=
    measurable_fst.comp ((measurable_pi_apply i).comp measurable_fst)
  have hTv : Measurable fun p :
      (Fin m → (Fin q → ℝ) × A) × (Fin k → (Fin q → ℝ) × B) => (p.2 j).1 :=
    measurable_fst.comp ((measurable_pi_apply j).comp measurable_snd)
  have hkin_meas : Measurable fun p :
      (Fin m → (Fin q → ℝ) × A) × (Fin k → (Fin q → ℝ) × B) =>
      kin ((p.1 i).2) ((p.2 j).2) ((p.2 j).1 - (p.1 i).1) :=
    hkin.comp (Measurable.prodMk (Measurable.prodMk hSa hTa) (hTv.sub hSu))
  have hg_meas : Measurable fun p :
      (Fin m → (Fin q → ℝ) × A) × (Fin k → (Fin q → ℝ) × B) =>
      g ((p.1 i).2) ((p.2 j).2) :=
    hg.comp (Measurable.prodMk hSa hTa)
  exact hkin_meas.add (hg_meas.const_mul t)

/-! ## Uniform bounds on the cube carrier -/

variable (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ)

/-- **The marked edge cost is uniformly bounded on the cube carrier.** -/
theorem abs_condMarkedEdgeCost_le (t : ℝ) {C G : ℝ} (hC0 : 0 ≤ C)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hgb : ∀ a b, |g a b| ≤ G)
    {u v : Fin q → ℝ} (hu : u ∈ OTSelector.Probability.unitCubeSet q)
    (hv : v ∈ OTSelector.Probability.unitCubeSet q) (a : A) (b : B) :
    |condMarkedEdgeCost kin g t u v a b| ≤ C * (q : ℝ) + |t| * G := by
  have hcoord : ∀ l : Fin q, (v l - u l) ^ 2 < 1 := by
    intro l
    have hu' := (Set.mem_pi.mp hu) l (mem_univ l)
    have hv' := (Set.mem_pi.mp hv) l (mem_univ l)
    rw [Set.mem_Ioo] at hu' hv'
    nlinarith
  have hsum : ∑ l, (v l - u l) ^ 2 ≤ (q : ℝ) := by
    calc ∑ l, (v l - u l) ^ 2 ≤ ∑ _l : Fin q, (1 : ℝ) := by
          exact Finset.sum_le_sum fun l _ => le_of_lt (hcoord l)
      _ = (q : ℝ) := by simp
  have hkin_le : |kin a b (v - u)| ≤ C * (q : ℝ) :=
    (hkin_bound a b (v - u)).trans (by
      refine mul_le_mul_of_nonneg_left hsum hC0)
  calc |condMarkedEdgeCost kin g t u v a b|
      = |kin a b (v - u) + t * g a b| := rfl
    _ ≤ |kin a b (v - u)| + |t * g a b| := abs_add_le _ _
    _ ≤ C * (q : ℝ) + |t| * G := by
        refine add_le_add hkin_le ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hgb a b) (abs_nonneg t)

/-- **The marked block value is uniformly bounded on the cube carrier.** -/
theorem abs_condMarkedBlockValue_le (t : ℝ) {C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hgb : ∀ a b, |g a b| ≤ G) {m k : ℕ}
    (S : Fin m → (Fin q → ℝ) × A) (T : Fin k → (Fin q → ℝ) × B)
    (hS : ∀ i, (S i).1 ∈ OTSelector.Probability.unitCubeSet q)
    (hT : ∀ j, (T j).1 ∈ OTSelector.Probability.unitCubeSet q) :
    |condMarkedBlockValue kin g t S T| ≤
      (min m k : ℝ) * (C * (q : ℝ) + |t| * G) := by
  have hB0 : 0 ≤ C * (q : ℝ) + |t| * G := by positivity
  exact OTSelector.PartialMatching.abs_maxCardValue_le_of_abs_le hB0
    (fun i j => abs_condMarkedEdgeCost_le kin g t hC0 hkin_bound hgb (hS i) (hT j) _ _)

/-! ## The pathwise positions on the cube -/

/-- Almost every marked source array has all its cube positions in the unit cube. -/
theorem ae_condMarkedArrayLaw_positions (m : ℕ) (K : Kernel (Fin q → ℝ) A)
    [IsMarkovKernel K] :
    ∀ᵐ S ∂(condMarkedArrayLaw m K),
      ∀ i, (S i).1 ∈ OTSelector.Probability.unitCubeSet q := by
  haveI hInt : IsProbabilityMeasure (OTSelector.Probability.uniformInterval (1 : ℝ)) :=
    OTSelector.Probability.isProbabilityMeasure_uniformInterval (by norm_num)
  haveI hc : IsProbabilityMeasure (OTSelector.Probability.cubeMeasure (Fin q) 1) := by
    rw [OTSelector.Probability.cubeMeasure]
    infer_instance
  haveI hpoint : IsProbabilityMeasure
      (condMarkedPointLaw (OTSelector.Probability.cubeMeasure (Fin q) 1) K) := by
    rw [condMarkedPointLaw]
    infer_instance
  haveI hall : ∀ _ : Fin m, IsProbabilityMeasure
      (condMarkedPointLaw (OTSelector.Probability.cubeMeasure (Fin q) 1) K) := fun _ => hpoint
  haveI hsf : SFinite (OTSelector.Probability.cubeMeasure (Fin q) 1) := inferInstance
  rw [condMarkedArrayLaw]
  apply ae_all_iff.mpr
  intro i
  have hmp := measurePreserving_eval (μ := fun _ : Fin m =>
    condMarkedPointLaw (OTSelector.Probability.cubeMeasure (Fin q) 1) K) i
  have hmap : (Measure.pi fun _ : Fin m =>
      condMarkedPointLaw (OTSelector.Probability.cubeMeasure (Fin q) 1) K).map
        (fun S => (S i).1) = OTSelector.Probability.cubeMeasure (Fin q) 1 := by
    rw [show (fun S : Fin m → (Fin q → ℝ) × A => (S i).1) =
        Prod.fst ∘ (Function.eval i) from rfl,
      ← Measure.map_map measurable_fst (measurable_pi_apply i), hmp.map_eq]
    exact Measure.fst_compProd (OTSelector.Probability.cubeMeasure (Fin q) 1) K
  refine ae_of_ae_map (f := fun S : Fin m → (Fin q → ℝ) × A => (S i).1)
    (measurable_fst.comp (measurable_pi_apply i)).aemeasurable ?_
  rw [hmap]
  exact OTSelector.Probability.ae_mem_unitCubeSet_cubeMeasure q

/-! ## Integrability and the reduction to independent marks -/

/-- The marked array law is a probability measure. -/
theorem isProbabilityMeasure_condMarkedArrayLaw (m : ℕ) (K : Kernel (Fin q → ℝ) A)
    [IsMarkovKernel K] : IsProbabilityMeasure (condMarkedArrayLaw m K) := by
  haveI hInt : IsProbabilityMeasure (OTSelector.Probability.uniformInterval (1 : ℝ)) :=
    OTSelector.Probability.isProbabilityMeasure_uniformInterval (by norm_num)
  haveI hc : IsProbabilityMeasure (OTSelector.Probability.cubeMeasure (Fin q) 1) := by
    rw [OTSelector.Probability.cubeMeasure]
    infer_instance
  haveI hpoint : IsProbabilityMeasure
      (condMarkedPointLaw (OTSelector.Probability.cubeMeasure (Fin q) 1) K) := by
    rw [condMarkedPointLaw]
    infer_instance
  haveI hall : ∀ _ : Fin m, IsProbabilityMeasure
      (condMarkedPointLaw (OTSelector.Probability.cubeMeasure (Fin q) 1) K) := fun _ => hpoint
  rw [condMarkedArrayLaw]
  infer_instance

/-- **Integrability of the conditional-kernel marked block value.**  On the cube
carrier the marked block value is bounded by the marked cardinality times the
kinetic and probe bounds, hence integrable under the marked array laws. -/
theorem integrable_condMarkedBlockValue (kin : A → B → (Fin q → ℝ) → ℝ)
    (g : A → B → ℝ) (t : ℝ) {C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (m k : ℕ) :
    Integrable (fun p : (Fin m → (Fin q → ℝ) × A) × (Fin k → (Fin q → ℝ) × B) =>
      condMarkedBlockValue kin g t p.1 p.2)
      ((condMarkedArrayLaw m Ks).prod (condMarkedArrayLaw k Kt)) := by
  haveI hmS := isProbabilityMeasure_condMarkedArrayLaw (q := q) m Ks
  haveI hmT := isProbabilityMeasure_condMarkedArrayLaw (q := q) k Kt
  have hmeas := measurable_condMarkedBlockValue kin g t hkin hg m k
  have hmapfst : ((condMarkedArrayLaw m Ks).prod (condMarkedArrayLaw k Kt)).map Prod.fst
      = condMarkedArrayLaw m Ks := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hmapsnd : ((condMarkedArrayLaw m Ks).prod (condMarkedArrayLaw k Kt)).map Prod.snd
      = condMarkedArrayLaw k Kt := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hsrc : ∀ᵐ p ∂((condMarkedArrayLaw m Ks).prod (condMarkedArrayLaw k Kt)),
      ∀ i, (p.1 i).1 ∈ OTSelector.Probability.unitCubeSet q :=
    (MeasurePreserving.quasiMeasurePreserving
      (show MeasurePreserving Prod.fst _ _ from ⟨measurable_fst, hmapfst⟩)).ae
      (ae_condMarkedArrayLaw_positions m Ks)
  have htgt : ∀ᵐ p ∂((condMarkedArrayLaw m Ks).prod (condMarkedArrayLaw k Kt)),
      ∀ j, (p.2 j).1 ∈ OTSelector.Probability.unitCubeSet q :=
    (MeasurePreserving.quasiMeasurePreserving
      (show MeasurePreserving Prod.snd _ _ from ⟨measurable_snd, hmapsnd⟩)).ae
      (ae_condMarkedArrayLaw_positions k Kt)
  refine Integrable.mono' (integrable_const ((min m k : ℝ) * (C * (q : ℝ) + |t| * G)))
    hmeas.aestronglyMeasurable ?_
  filter_upwards [hsrc, htgt] with p hp hq
  rw [Real.norm_eq_abs]
  exact abs_condMarkedBlockValue_le kin g t hC0 hG0 hkin_bound hgb p.1 p.2 hp hq

/-- **Reduction to the independent-mark marked pressure.**  For constant mark
kernels the coordinate-dependent-kernel marked pressure is exactly the classical
independent-mark marked pressure: the existing independent-mark results are the
constant-kernel special case of the conditional-kernel model. -/
theorem condMarkedBlockExpectation_const (kin : A → B → (Fin q → ℝ) → ℝ)
    (g : A → B → ℝ) (t : ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (m k : ℕ) :
    condMarkedBlockExpectation kin g t (Kernel.const (Fin q → ℝ) α)
        (Kernel.const (Fin q → ℝ) β) m k =
      iidMarkedBlockExpectation kin g t α β m k := by
  unfold condMarkedBlockExpectation iidMarkedBlockExpectation condMarkedArrayLaw
    condMarkedPointLaw
  simp only [Measure.compProd_const]

/-- **The marked one-point law of a conditional mark law.**  The joint law of a
cell whose coordinate and mark satisfy the conditional mark law is exactly the
composition product of the coordinate law with the mark kernel. -/
theorem conditionalMarkLaw_markedPointLaw {X : Type*} [MeasurableSpace X]
    {ρ : Measure X} {coord : X → Fin q → ℝ} {mark : X → A}
    {K : Kernel (Fin q → ℝ) A} (hK : ConditionalMarkLaw ρ coord mark K) :
    ρ.map (fun x => (coord x, mark x)) = condMarkedPointLaw (ρ.map coord) K :=
  hK

/-- **Almost-everywhere-constant kernels give the product mark law.**  If the
mark kernel is almost everywhere the constant kernel, the marked one-point law is
the product of the coordinate law and the mark law, which is precisely the
independent-mark hypothesis of the upper localization. -/
theorem condMarkedPointLaw_eq_prod_of_ae_const {μ : Measure (Fin q → ℝ)} [SFinite μ]
    {K : Kernel (Fin q → ℝ) A} [IsSFiniteKernel K] {α : Measure A} [SFinite α]
    (hconst : K =ᵐ[μ] Kernel.const (Fin q → ℝ) α) :
    condMarkedPointLaw μ K = μ.prod α := by
  rw [condMarkedPointLaw, Measure.compProd_congr hconst, Measure.compProd_const]

/-! ## Continuity in the tilt -/

/-- **Uniform Lipschitz continuity of the conditional-kernel pressure in the
tilt.**  The conditional-kernel marked pressure is Lipschitz in the tilt with
constant the marked cardinality times the probe bound; this is the continuity
input of the marked pressure lane, now available for coordinate-dependent marks. -/
theorem abs_condMarkedBlockExpectation_tilt_sub_le (kin : A → B → (Fin q → ℝ) → ℝ)
    (g : A → B → ℝ) {C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (m k : ℕ) (t t' : ℝ) :
    |condMarkedBlockExpectation kin g t Ks Kt m k -
        condMarkedBlockExpectation kin g t' Ks Kt m k| ≤
      (min m k : ℝ) * (|t - t'| * G) := by
  set mu := (condMarkedArrayLaw m Ks).prod (condMarkedArrayLaw k Kt) with hmu
  haveI hmS := isProbabilityMeasure_condMarkedArrayLaw (q := q) m Ks
  haveI hmT := isProbabilityMeasure_condMarkedArrayLaw (q := q) k Kt
  haveI hmuprob : IsProbabilityMeasure mu := by
    rw [hmu]
    infer_instance
  have hf : Integrable (fun p : (Fin m → (Fin q → ℝ) × A) × (Fin k → (Fin q → ℝ) × B) =>
      condMarkedBlockValue kin g t p.1 p.2) mu :=
    integrable_condMarkedBlockValue kin g t hC0 hG0 hkin hkin_bound hg hgb Ks Kt m k
  have hf' : Integrable (fun p : (Fin m → (Fin q → ℝ) × A) × (Fin k → (Fin q → ℝ) × B) =>
      condMarkedBlockValue kin g t' p.1 p.2) mu :=
    integrable_condMarkedBlockValue kin g t' hC0 hG0 hkin hkin_bound hg hgb Ks Kt m k
  have hpoint : ∀ p : (Fin m → (Fin q → ℝ) × A) × (Fin k → (Fin q → ℝ) × B),
      |condMarkedBlockValue kin g t p.1 p.2 - condMarkedBlockValue kin g t' p.1 p.2| ≤
        (min m k : ℝ) * (|t - t'| * G) := by
    intro p
    have hB : ∀ i j,
        |(fun i j => condMarkedEdgeCost kin g t (p.1 i).1 (p.2 j).1 (p.1 i).2 (p.2 j).2) i j -
          (fun i j => condMarkedEdgeCost kin g t' (p.1 i).1 (p.2 j).1
            (p.1 i).2 (p.2 j).2) i j| ≤ |t - t'| * G := by
      intro i j
      have hdiff : condMarkedEdgeCost kin g t (p.1 i).1 (p.2 j).1 (p.1 i).2 (p.2 j).2 -
          condMarkedEdgeCost kin g t' (p.1 i).1 (p.2 j).1 (p.1 i).2 (p.2 j).2 =
          (t - t') * g (p.1 i).2 (p.2 j).2 := by
        unfold condMarkedEdgeCost
        ring
      rw [hdiff, abs_mul]
      exact mul_le_mul_of_nonneg_left (hgb _ _) (abs_nonneg _)
    have := OTSelector.PartialMatching.abs_maxCardValue_sub_le_of_abs_sub_le hB
    simpa only [condMarkedBlockValue] using this
  have h : |∫ p, (condMarkedBlockValue kin g t p.1 p.2 -
        condMarkedBlockValue kin g t' p.1 p.2) ∂mu| ≤
      ∫ p, |condMarkedBlockValue kin g t p.1 p.2 -
        condMarkedBlockValue kin g t' p.1 p.2| ∂mu := by
    rw [show |∫ p, (condMarkedBlockValue kin g t p.1 p.2 -
          condMarkedBlockValue kin g t' p.1 p.2) ∂mu| =
        ‖∫ p, (condMarkedBlockValue kin g t p.1 p.2 -
          condMarkedBlockValue kin g t' p.1 p.2) ∂mu‖ from by rw [Real.norm_eq_abs]]
    calc ‖∫ p, (condMarkedBlockValue kin g t p.1 p.2 -
          condMarkedBlockValue kin g t' p.1 p.2) ∂mu‖
        ≤ ∫ p, ‖condMarkedBlockValue kin g t p.1 p.2 -
            condMarkedBlockValue kin g t' p.1 p.2‖ ∂mu :=
          norm_integral_le_integral_norm (f := fun p :
            (Fin m → (Fin q → ℝ) × A) × (Fin k → (Fin q → ℝ) × B) =>
            condMarkedBlockValue kin g t p.1 p.2 - condMarkedBlockValue kin g t' p.1 p.2)
      _ = ∫ p, |condMarkedBlockValue kin g t p.1 p.2 -
            condMarkedBlockValue kin g t' p.1 p.2| ∂mu := by
          simp only [Real.norm_eq_abs]
  calc |condMarkedBlockExpectation kin g t Ks Kt m k -
        condMarkedBlockExpectation kin g t' Ks Kt m k|
      = |∫ p, (condMarkedBlockValue kin g t p.1 p.2 -
          condMarkedBlockValue kin g t' p.1 p.2) ∂mu| := by
        rw [condMarkedBlockExpectation, condMarkedBlockExpectation, hmu, integral_sub hf hf']
    _ ≤ ∫ p, |condMarkedBlockValue kin g t p.1 p.2 -
          condMarkedBlockValue kin g t' p.1 p.2| ∂mu := h
    _ ≤ ∫ _p, (min m k : ℝ) * (|t - t'| * G) ∂mu :=
        integral_mono (hf.sub hf').abs (integrable_const _) hpoint
    _ = (min m k : ℝ) * (|t - t'| * G) := by
        rw [integral_const]
        simp [Measure.real, smul_eq_mul]

end OTSelector.Reconstruction
