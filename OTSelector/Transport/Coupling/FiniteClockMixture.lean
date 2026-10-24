import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Tactic

/-!
# Transport.Coupling.FiniteClockMixture

## Lemma skeleton

* **Conditions:** Finite class indices, nonnegative real matrix weights and measurable families of finite/s-finite or Markov kernels as explicitly specified in each declaration.

* **Objects:** Weighted finite product couplings, their kernel versions, exact marginals/mass, same-label gluing and legal-support/residual bounds.

* **Proof detail:** Sum P_ij times the product of the two component laws. Normalize only by the Markov factors already supplied, compute projections termwise, then integrate over the common label and duplicate that label into both endpoints. Nonnegative additivity and positive matrix entries give residual domination and legal carrying.

## Mathematical sources

- [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf): Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=144): Section 5B, Theorem 5.28 (Tonelli), printed p. 129, PDF page 144.
- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean): Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (composition): An explicit finite-mixture/kernel assembly. Measurability is used where supplied; the weighted-kernel definition uses the library’s measurable fallback, and the actual evaluation formula requires the stated measurable weights.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- A finite class flow couples the actual within-class laws. -/
def finiteClassPopulationCoupling
    {I J X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] [MeasurableSpace Y]
    (P : I → J → ℝ) (α : I → Measure X) (β : J → Measure Y) : Measure (X × Y) :=
  ∑ i, ∑ j, ENNReal.ofReal (P i j) • (α i).prod (β j)

/-- The source marginal of the population coupling is its actual class mixture. -/
theorem finiteClassPopulationCoupling_fst
    {I J X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] [MeasurableSpace Y]
    (P : I → J → ℝ) (α : I → Measure X) (β : J → Measure Y)
    [∀ i, IsProbabilityMeasure (α i)] [∀ j, IsProbabilityMeasure (β j)]
    (hP : ∀ i j, 0 ≤ P i j) :
    (finiteClassPopulationCoupling P α β).map Prod.fst =
      ∑ i, ENNReal.ofReal (∑ j, P i j) • α i := by
  classical
  simp only [finiteClassPopulationCoupling,
    Measure.map_finset_sum' measurable_fst.aemeasurable, Measure.map_smul,
    Measure.map_fst_prod, measure_univ, one_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hP i j), Finset.sum_smul]

/-- The target marginal of the population coupling is its actual class mixture. -/
theorem finiteClassPopulationCoupling_snd
    {I J X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] [MeasurableSpace Y]
    (P : I → J → ℝ) (α : I → Measure X) (β : J → Measure Y)
    [∀ i, IsProbabilityMeasure (α i)] [∀ j, IsProbabilityMeasure (β j)]
    (hP : ∀ i j, 0 ≤ P i j) :
    (finiteClassPopulationCoupling P α β).map Prod.snd =
      ∑ j, ENNReal.ofReal (∑ i, P i j) • β j := by
  classical
  simp only [finiteClassPopulationCoupling,
    Measure.map_finset_sum' measurable_snd.aemeasurable, Measure.map_smul,
    Measure.map_snd_prod, measure_univ, one_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hP i j), Finset.sum_smul]

/-- A measurable class-weighted kernel, with finite values but no uniform
pointwise density bound. -/
def classWeightedKernel
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    (w : Z → ℝ) (κ : Kernel Z X) [IsSFiniteKernel κ] : Kernel Z X :=
  Kernel.withDensity κ (fun z _ ↦ ENNReal.ofReal (w z))

theorem classWeightedKernel_apply
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    (w : Z → ℝ) (hw : Measurable w) (κ : Kernel Z X) [IsSFiniteKernel κ] (z : Z) :
    classWeightedKernel w κ z = ENNReal.ofReal (w z) • κ z := by
  rw [classWeightedKernel, Kernel.withDensity_apply _ (hw.comp measurable_fst).ennreal_ofReal]
  exact withDensity_const _

instance classWeightedKernel_isSFinite
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    (w : Z → ℝ) (κ : Kernel Z X) [IsSFiniteKernel κ] :
    IsSFiniteKernel (classWeightedKernel w κ) := by
  unfold classWeightedKernel
  exact Kernel.IsSFiniteKernel.withDensity _ (fun _ _ ↦ ENNReal.ofReal_ne_top)

/-- The class-flow coupling is an actual measurable kernel. -/
def finiteClassPopulationKernel
    {I J Z X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (P : Z → I → J → ℝ) (α : I → Kernel Z X) (β : J → Kernel Z Y)
    [∀ i, IsSFiniteKernel (α i)] [∀ j, IsSFiniteKernel (β j)] : Kernel Z (X × Y) :=
  ∑ i, ∑ j, classWeightedKernel (fun z ↦ P z i j) ((α i) ×ₖ (β j))

theorem finiteClassPopulationKernel_apply
    {I J Z X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (P : Z → I → J → ℝ) (hP : ∀ i j, Measurable (fun z ↦ P z i j))
    (α : I → Kernel Z X) (β : J → Kernel Z Y)
    [∀ i, IsSFiniteKernel (α i)] [∀ j, IsSFiniteKernel (β j)] (z : Z) :
    finiteClassPopulationKernel P α β z =
      finiteClassPopulationCoupling (P z) (fun i ↦ α i z) (fun j ↦ β j z) := by
  simp only [finiteClassPopulationKernel, finiteClassPopulationCoupling, sum_apply,
    classWeightedKernel_apply _ (hP _ _) _, Kernel.prod_apply]

instance finiteClassPopulationKernel_isSFinite
    {I J Z X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (P : Z → I → J → ℝ) (α : I → Kernel Z X) (β : J → Kernel Z Y)
    [∀ i, IsSFiniteKernel (α i)] [∀ j, IsSFiniteKernel (β j)] :
    IsSFiniteKernel (finiteClassPopulationKernel P α β) := by
  unfold finiteClassPopulationKernel
  apply Kernel.IsSFiniteKernel.finsetSum
  intro i hi
  apply Kernel.IsSFiniteKernel.finsetSum
  intro j hj
  infer_instance

/-- Adding retained and residual nonnegative flows adds their actual population
couplings, so the deterministic residual is a submeasure of the new whole plan. -/
theorem finiteClassPopulationCoupling_add
    {I J X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] [MeasurableSpace Y]
    (P Q : I → J → ℝ) (α : I → Measure X) (β : J → Measure Y)
    (hP : ∀ i j, 0 ≤ P i j) (hQ : ∀ i j, 0 ≤ Q i j) :
    finiteClassPopulationCoupling (fun i j ↦ P i j + Q i j) α β =
      finiteClassPopulationCoupling P α β + finiteClassPopulationCoupling Q α β := by
  classical
  simp only [finiteClassPopulationCoupling,
    ENNReal.ofReal_add (hP _ _) (hQ _ _), add_smul, Finset.sum_add_distrib]

/-- Legal class edges and the actual within-bin laws give a legal population
coupling. No independently sampled orphan law is introduced. -/
theorem finiteClassPopulationCoupling_ae
    {I J X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] [MeasurableSpace Y]
    (P : I → J → ℝ) (α : I → Measure X) (β : J → Measure Y)
    (allowed : I → J → Prop) (legal : X × Y → Prop)
    (hzero : ∀ i j, ¬ allowed i j → P i j = 0)
    (hlegal : ∀ i j, allowed i j → ∀ᵐ p ∂(α i).prod (β j), legal p) :
    ∀ᵐ p ∂finiteClassPopulationCoupling P α β, legal p := by
  classical
  rw [ae_iff]
  simp only [finiteClassPopulationCoupling, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hij : allowed i j
  · rw [(ae_iff.mp (hlegal i j hij)), mul_zero]
  · rw [hzero i j hij, ENNReal.ofReal_zero, zero_mul]

/-- Kernel addition retains the same actual conditional laws in every class. -/
theorem finiteClassPopulationKernel_add
    {I J Z X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (P Q : Z → I → J → ℝ)
    (hmP : ∀ i j, Measurable (fun z ↦ P z i j))
    (hmQ : ∀ i j, Measurable (fun z ↦ Q z i j))
    (α : I → Kernel Z X) (β : J → Kernel Z Y)
    [∀ i, IsSFiniteKernel (α i)] [∀ j, IsSFiniteKernel (β j)]
    (hP : ∀ z i j, 0 ≤ P z i j) (hQ : ∀ z i j, 0 ≤ Q z i j) :
    finiteClassPopulationKernel (fun z i j ↦ P z i j + Q z i j) α β =
      finiteClassPopulationKernel P α β + finiteClassPopulationKernel Q α β := by
  ext z : 1
  change finiteClassPopulationKernel (fun z i j ↦ P z i j + Q z i j) α β z =
    finiteClassPopulationKernel P α β z + finiteClassPopulationKernel Q α β z
  have hmSum : ∀ i j, Measurable (fun z ↦ P z i j + Q z i j) := by
    intro i j
    exact measurable_add.comp ((hmP i j).prodMk (hmQ i j))
  rw [finiteClassPopulationKernel_apply (fun z i j ↦ P z i j + Q z i j) hmSum α β z,
    finiteClassPopulationKernel_apply _ hmP α β z,
    finiteClassPopulationKernel_apply _ hmQ α β z]
  exact finiteClassPopulationCoupling_add (P z) (Q z) _ _ (hP z) (hQ z)

/-- The actual deterministic residual measure is below the rebuilt whole
population coupling on the same original label space. -/
theorem finiteClassPopulationKernel_compProd_residual_le
    {I J Z X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Z) (P Q : Z → I → J → ℝ)
    (hmP : ∀ i j, Measurable (fun z ↦ P z i j))
    (hmQ : ∀ i j, Measurable (fun z ↦ Q z i j))
    (α : I → Kernel Z X) (β : J → Kernel Z Y)
    [∀ i, IsSFiniteKernel (α i)] [∀ j, IsSFiniteKernel (β j)]
    (hP : ∀ z i j, 0 ≤ P z i j) (hQ : ∀ z i j, 0 ≤ Q z i j) :
    μ ⊗ₘ finiteClassPopulationKernel Q α β ≤
      μ ⊗ₘ finiteClassPopulationKernel (fun z i j ↦ P z i j + Q z i j) α β := by
  rw [finiteClassPopulationKernel_add _ _ hmP hmQ α β hP hQ,
    Measure.compProd_add_right]
  exact Measure.le_add_left le_rfl

/-- The original source class mixture, with its actual root-dependent masses. -/
def finiteClassMarginalKernel
    {I Z X : Type*} [Fintype I] [MeasurableSpace Z] [MeasurableSpace X]
    (a : Z → I → ℝ) (α : I → Kernel Z X) [∀ i, IsSFiniteKernel (α i)] : Kernel Z X :=
  ∑ i, classWeightedKernel (fun z ↦ a z i) (α i)

instance finiteClassMarginalKernel_isSFinite
    {I Z X : Type*} [Fintype I] [MeasurableSpace Z] [MeasurableSpace X]
    (a : Z → I → ℝ) (α : I → Kernel Z X) [∀ i, IsSFiniteKernel (α i)] :
    IsSFiniteKernel (finiteClassMarginalKernel a α) := by
  unfold finiteClassMarginalKernel
  exact Kernel.IsSFiniteKernel.finsetSum _ (fun i hi ↦ inferInstance)

theorem finiteClassMarginalKernel_apply
    {I Z X : Type*} [Fintype I] [MeasurableSpace Z] [MeasurableSpace X]
    (a : Z → I → ℝ) (ha : ∀ i, Measurable (fun z ↦ a z i))
    (α : I → Kernel Z X) [∀ i, IsSFiniteKernel (α i)] (z : Z) :
    finiteClassMarginalKernel a α z = ∑ i, ENNReal.ofReal (a z i) • α i z := by
  simp only [finiteClassMarginalKernel, sum_apply, classWeightedKernel_apply _ (ha _) _]

/-- The actual source marginal is recovered for almost every original label;
profiles outside the chosen good label set need no artificial feasibility. -/
theorem finiteClassPopulationKernel_fst_ae
    {I J Z X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Z) (P : Z → I → J → ℝ) (a : Z → I → ℝ)
    (hmP : ∀ i j, Measurable (fun z ↦ P z i j))
    (hma : ∀ i, Measurable (fun z ↦ a z i))
    (α : I → Kernel Z X) (β : J → Kernel Z Y)
    [∀ i, IsMarkovKernel (α i)] [∀ j, IsMarkovKernel (β j)]
    (hP : ∀ᵐ z ∂μ, ∀ i j, 0 ≤ P z i j)
    (hrow : ∀ᵐ z ∂μ, ∀ i, ∑ j, P z i j = a z i) :
    (finiteClassPopulationKernel P α β).map Prod.fst =ᵐ[μ]
      finiteClassMarginalKernel a α := by
  filter_upwards [hP, hrow] with z hz hrowz
  rw [Kernel.map_apply _ measurable_fst,
    finiteClassPopulationKernel_apply _ hmP α β z,
    finiteClassPopulationCoupling_fst _ _ _ hz,
    finiteClassMarginalKernel_apply _ hma α z]
  simp_rw [hrowz]

/-- The actual target marginal is recovered for almost every original label. -/
theorem finiteClassPopulationKernel_snd_ae
    {I J Z X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Z) (P : Z → I → J → ℝ) (b : Z → J → ℝ)
    (hmP : ∀ i j, Measurable (fun z ↦ P z i j))
    (hmb : ∀ j, Measurable (fun z ↦ b z j))
    (α : I → Kernel Z X) (β : J → Kernel Z Y)
    [∀ i, IsMarkovKernel (α i)] [∀ j, IsMarkovKernel (β j)]
    (hP : ∀ᵐ z ∂μ, ∀ i j, 0 ≤ P z i j)
    (hcol : ∀ᵐ z ∂μ, ∀ j, ∑ i, P z i j = b z j) :
    (finiteClassPopulationKernel P α β).map Prod.snd =ᵐ[μ]
      finiteClassMarginalKernel b β := by
  filter_upwards [hP, hcol] with z hz hcolz
  rw [Kernel.map_apply _ measurable_snd,
    finiteClassPopulationKernel_apply _ hmP α β z,
    finiteClassPopulationCoupling_snd _ _ _ hz,
    finiteClassMarginalKernel_apply _ hmb β z]
  simp_rw [hcolz]

/-- Both physical endpoints retain exactly the same original label. -/
def sameLabelPopulationPair {Z X Y : Type*} (p : Z × (X × Y)) : (Z × X) × (Z × Y) :=
  ((p.1, p.2.1), (p.1, p.2.2))

theorem measurable_sameLabelPopulationPair
    {Z X Y : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y] :
    Measurable (sameLabelPopulationPair (Z := Z) (X := X) (Y := Y)) :=
  (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))

/-- A whole original coupling is rebuilt on common labels from the continuous
within-class laws and the measurable finite class flow. -/
def sameLabelPopulationCoupling
    {I J Z X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Z) (P : Z → I → J → ℝ)
    (α : I → Kernel Z X) (β : J → Kernel Z Y)
    [∀ i, IsSFiniteKernel (α i)] [∀ j, IsSFiniteKernel (β j)] :
    Measure ((Z × X) × (Z × Y)) :=
  (μ ⊗ₘ finiteClassPopulationKernel P α β).map sameLabelPopulationPair

theorem sameLabelPopulationCoupling_fst
    {I J Z X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Z) [SFinite μ] (P : Z → I → J → ℝ) (a : Z → I → ℝ)
    (hmP : ∀ i j, Measurable (fun z ↦ P z i j))
    (hma : ∀ i, Measurable (fun z ↦ a z i))
    (α : I → Kernel Z X) (β : J → Kernel Z Y)
    [∀ i, IsMarkovKernel (α i)] [∀ j, IsMarkovKernel (β j)]
    (hP : ∀ᵐ z ∂μ, ∀ i j, 0 ≤ P z i j)
    (hrow : ∀ᵐ z ∂μ, ∀ i, ∑ j, P z i j = a z i) :
    (sameLabelPopulationCoupling μ P α β).map Prod.fst =
      μ ⊗ₘ finiteClassMarginalKernel a α := by
  rw [sameLabelPopulationCoupling,
    Measure.map_map measurable_fst measurable_sameLabelPopulationPair]
  change (μ ⊗ₘ finiteClassPopulationKernel P α β).map (Prod.map id Prod.fst) = _
  rw [← Measure.compProd_map measurable_fst]
  exact Measure.compProd_congr (finiteClassPopulationKernel_fst_ae μ P a hmP hma α β hP hrow)

theorem sameLabelPopulationCoupling_snd
    {I J Z X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Z) [SFinite μ] (P : Z → I → J → ℝ) (b : Z → J → ℝ)
    (hmP : ∀ i j, Measurable (fun z ↦ P z i j))
    (hmb : ∀ j, Measurable (fun z ↦ b z j))
    (α : I → Kernel Z X) (β : J → Kernel Z Y)
    [∀ i, IsMarkovKernel (α i)] [∀ j, IsMarkovKernel (β j)]
    (hP : ∀ᵐ z ∂μ, ∀ i j, 0 ≤ P z i j)
    (hcol : ∀ᵐ z ∂μ, ∀ j, ∑ i, P z i j = b z j) :
    (sameLabelPopulationCoupling μ P α β).map Prod.snd =
      μ ⊗ₘ finiteClassMarginalKernel b β := by
  rw [sameLabelPopulationCoupling,
    Measure.map_map measurable_snd measurable_sameLabelPopulationPair]
  change (μ ⊗ₘ finiteClassPopulationKernel P α β).map (Prod.map id Prod.snd) = _
  rw [← Measure.compProd_map measurable_snd]
  exact Measure.compProd_congr (finiteClassPopulationKernel_snd_ae μ P b hmP hmb α β hP hcol)

/-- The raw mass is the total class-flow mass; normalization is never imposed. -/
theorem finiteClassPopulationCoupling_mass
    {I J X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] [MeasurableSpace Y]
    (P : I → J → ℝ) (α : I → Measure X) (β : J → Measure Y)
    [∀ i, IsProbabilityMeasure (α i)] [∀ j, IsProbabilityMeasure (β j)]
    (hP : ∀ i j, 0 ≤ P i j) :
    finiteClassPopulationCoupling P α β Set.univ = ENNReal.ofReal (∑ i, ∑ j, P i j) := by
  classical
  simp only [finiteClassPopulationCoupling, Measure.finsetSum_apply,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i hi ↦ Finset.sum_nonneg (fun j hj ↦ hP i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ENNReal.ofReal_sum_of_nonneg (fun j hj ↦ hP i j)]

/-- Exact original-label mass of the rebuilt population coupling. -/
theorem sameLabelPopulationCoupling_mass
    {I J Z X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Z) [SFinite μ] (P : Z → I → J → ℝ)
    (hmP : ∀ i j, Measurable (fun z ↦ P z i j))
    (α : I → Kernel Z X) (β : J → Kernel Z Y)
    [∀ i, IsMarkovKernel (α i)] [∀ j, IsMarkovKernel (β j)]
    (hP : ∀ᵐ z ∂μ, ∀ i j, 0 ≤ P z i j) :
    sameLabelPopulationCoupling μ P α β Set.univ =
      ∫⁻ z, ENNReal.ofReal (∑ i, ∑ j, P z i j) ∂μ := by
  rw [sameLabelPopulationCoupling, Measure.map_apply measurable_sameLabelPopulationPair
    MeasurableSet.univ, Set.preimage_univ, Measure.compProd_apply MeasurableSet.univ]
  apply lintegral_congr_ae
  filter_upwards [hP] with z hz
  rw [finiteClassPopulationKernel_apply _ hmP α β z]
  exact finiteClassPopulationCoupling_mass _ _ _ hz

/-- The rebuilt coupling retains the original common label identically. -/
theorem sameLabelPopulationCoupling_ae_commonLabel
    {I J Z X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace Z] [MeasurableEq Z] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Z) (P : Z → I → J → ℝ)
    (α : I → Kernel Z X) (β : J → Kernel Z Y)
    [∀ i, IsSFiniteKernel (α i)] [∀ j, IsSFiniteKernel (β j)] :
    ∀ᵐ p ∂sameLabelPopulationCoupling μ P α β, p.1.1 = p.2.1 := by
  rw [sameLabelPopulationCoupling]
  apply (ae_map_iff measurable_sameLabelPopulationPair.aemeasurable
    (measurableSet_eq_fun (measurable_fst.comp measurable_fst)
      (measurable_fst.comp measurable_snd))).mpr
  exact Filter.Eventually.of_forall fun p ↦ rfl

/-- Legal finite clock-class edges remain legal under their actual continuous
within-bin conditional laws and the original common-label measure. -/
theorem sameLabelPopulationCoupling_ae_legal
    {I J Z X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Z) (P : Z → I → J → ℝ)
    (hmP : ∀ i j, Measurable (fun z ↦ P z i j))
    (α : I → Kernel Z X) (β : J → Kernel Z Y)
    [∀ i, IsSFiniteKernel (α i)] [∀ j, IsSFiniteKernel (β j)]
    (allowed : I → J → Prop) (legal : Z → X × Y → Prop)
    (hmlegal : MeasurableSet {p : Z × (X × Y) | legal p.1 p.2})
    (hzero : ∀ᵐ z ∂μ, ∀ i j, ¬ allowed i j → P z i j = 0)
    (hlegal : ∀ᵐ z ∂μ, ∀ i j, allowed i j →
      ∀ᵐ p ∂(α i z).prod (β j z), legal z p) :
    ∀ᵐ p ∂sameLabelPopulationCoupling μ P α β, legal p.1.1 (p.1.2, p.2.2) := by
  have hmread : Measurable (fun p : (Z × X) × (Z × Y) ↦ (p.1.1, (p.1.2, p.2.2))) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
  rw [sameLabelPopulationCoupling]
  apply (ae_map_iff measurable_sameLabelPopulationPair.aemeasurable (hmread hmlegal)).mpr
  apply Measure.ae_compProd_of_ae_ae hmlegal
  filter_upwards [hzero, hlegal] with z hz hl
  rw [finiteClassPopulationKernel_apply _ hmP α β z]
  exact finiteClassPopulationCoupling_ae _ _ _ allowed (legal z) hz hl

/-- Retained and residual kernels add almost everywhere on the original label
law. Bad labels outside the selected population require no feasibility premise. -/
theorem sameLabelPopulationCoupling_add_ae
    {I J Z X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Z) (P Q : Z → I → J → ℝ)
    (hmP : ∀ i j, Measurable (fun z ↦ P z i j))
    (hmQ : ∀ i j, Measurable (fun z ↦ Q z i j))
    (α : I → Kernel Z X) (β : J → Kernel Z Y)
    [∀ i, IsSFiniteKernel (α i)] [∀ j, IsSFiniteKernel (β j)]
    (hP : ∀ᵐ z ∂μ, ∀ i j, 0 ≤ P z i j)
    (hQ : ∀ᵐ z ∂μ, ∀ i j, 0 ≤ Q z i j) :
    sameLabelPopulationCoupling μ (fun z i j ↦ P z i j + Q z i j) α β =
      sameLabelPopulationCoupling μ P α β + sameLabelPopulationCoupling μ Q α β := by
  have hmSum : ∀ i j, Measurable (fun z ↦ P z i j + Q z i j) :=
    fun i j ↦ measurable_add.comp ((hmP i j).prodMk (hmQ i j))
  have hkernel : finiteClassPopulationKernel (fun z i j ↦ P z i j + Q z i j) α β =ᵐ[μ]
      finiteClassPopulationKernel P α β + finiteClassPopulationKernel Q α β := by
    filter_upwards [hP, hQ] with z hz hq
    change finiteClassPopulationKernel (fun z i j ↦ P z i j + Q z i j) α β z =
      finiteClassPopulationKernel P α β z + finiteClassPopulationKernel Q α β z
    rw [finiteClassPopulationKernel_apply _ hmSum α β z,
      finiteClassPopulationKernel_apply _ hmP α β z,
      finiteClassPopulationKernel_apply _ hmQ α β z]
    exact finiteClassPopulationCoupling_add _ _ _ _ hz hq
  simp only [sameLabelPopulationCoupling]
  rw [Measure.compProd_congr (η := finiteClassPopulationKernel P α β + finiteClassPopulationKernel Q α β) hkernel, Measure.compProd_add_right,
    Measure.map_add _ _ measurable_sameLabelPopulationPair]

/-- A pointwise class-mass bound gives an actual bound on the deterministic
residual population measure, in original unnormalized units. -/
theorem sameLabelPopulationCoupling_mass_le
    {I J Z X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Z) [SFinite μ] (P : Z → I → J → ℝ)
    (hmP : ∀ i j, Measurable (fun z ↦ P z i j))
    (α : I → Kernel Z X) (β : J → Kernel Z Y)
    [∀ i, IsMarkovKernel (α i)] [∀ j, IsMarkovKernel (β j)]
    (hP : ∀ᵐ z ∂μ, ∀ i j, 0 ≤ P z i j)
    (B : ℝ) (hB : ∀ᵐ z ∂μ, (∑ i, ∑ j, P z i j) ≤ B) :
    sameLabelPopulationCoupling μ P α β Set.univ ≤ ENNReal.ofReal B * μ Set.univ := by
  rw [sameLabelPopulationCoupling_mass μ P hmP α β hP]
  calc
    _ ≤ ∫⁻ _z, ENNReal.ofReal B ∂μ := lintegral_mono_ae (hB.mono fun z hz ↦ ENNReal.ofReal_le_ofReal hz)
    _ = _ := lintegral_const _

/-- The actual deterministic residual built from its measurable flow is a
submeasure of the reconstructed retained-plus-residual whole population. -/
theorem sameLabelPopulationCoupling_residual_le_ae
    {I J Z X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Z) (P Q : Z → I → J → ℝ)
    (hmP : ∀ i j, Measurable (fun z ↦ P z i j))
    (hmQ : ∀ i j, Measurable (fun z ↦ Q z i j))
    (α : I → Kernel Z X) (β : J → Kernel Z Y)
    [∀ i, IsSFiniteKernel (α i)] [∀ j, IsSFiniteKernel (β j)]
    (hP : ∀ᵐ z ∂μ, ∀ i j, 0 ≤ P z i j)
    (hQ : ∀ᵐ z ∂μ, ∀ i j, 0 ≤ Q z i j) :
    sameLabelPopulationCoupling μ Q α β ≤
      sameLabelPopulationCoupling μ (fun z i j ↦ P z i j + Q z i j) α β := by
  rw [sameLabelPopulationCoupling_add_ae μ P Q hmP hmQ α β hP hQ]
  exact Measure.le_add_left le_rfl

/-- Zero class-flow entries need no support information about a chosen
zero-bin fallback probability law. -/
theorem finiteClassPopulationCoupling_ae_of_pos
    {I J X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] [MeasurableSpace Y]
    (P : I → J → ℝ) (α : I → Measure X) (β : J → Measure Y)
    (legal : X × Y → Prop)
    (hlegal : ∀ i j, 0 < P i j → ∀ᵐ p ∂(α i).prod (β j), legal p) :
    ∀ᵐ p ∂finiteClassPopulationCoupling P α β, legal p := by
  classical
  rw [ae_iff]
  simp only [finiteClassPopulationCoupling, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hij : 0 < P i j
  · rw [(ae_iff.mp (hlegal i j hij)), mul_zero]
  · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hij), zero_mul]

/-- Positive-flow support is sufficient for legal original-label population
couplings, allowing arbitrary Markov fallbacks on zero-mass bins. -/
theorem sameLabelPopulationCoupling_ae_legal_of_pos
    {I J Z X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Z) (P : Z → I → J → ℝ)
    (hmP : ∀ i j, Measurable (fun z ↦ P z i j))
    (α : I → Kernel Z X) (β : J → Kernel Z Y)
    [∀ i, IsSFiniteKernel (α i)] [∀ j, IsSFiniteKernel (β j)]
    (legal : Z → X × Y → Prop)
    (hmlegal : MeasurableSet {p : Z × (X × Y) | legal p.1 p.2})
    (hlegal : ∀ᵐ z ∂μ, ∀ i j, 0 < P z i j →
      ∀ᵐ p ∂(α i z).prod (β j z), legal z p) :
    ∀ᵐ p ∂sameLabelPopulationCoupling μ P α β, legal p.1.1 (p.1.2, p.2.2) := by
  have hmread : Measurable (fun p : (Z × X) × (Z × Y) ↦ (p.1.1, (p.1.2, p.2.2))) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
  rw [sameLabelPopulationCoupling]
  apply (ae_map_iff measurable_sameLabelPopulationPair.aemeasurable (hmread hmlegal)).mpr
  apply Measure.ae_compProd_of_ae_ae hmlegal
  filter_upwards [hlegal] with z hz
  rw [finiteClassPopulationKernel_apply _ hmP α β z]
  exact finiteClassPopulationCoupling_ae_of_pos _ _ _ (legal z) hz

/-- Positive finite flow implies both original class marginals are positive. -/
theorem positive_classFlow_marginals
    {I J : Type*} [Fintype I] [Fintype J]
    (P : I → J → ℝ) (a : I → ℝ) (b : J → ℝ)
    (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = a i) (hcol : ∀ j, ∑ i, P i j = b j)
    (i : I) (j : J) (hij : 0 < P i j) : 0 < a i ∧ 0 < b j := by
  classical
  constructor
  · rw [← hrow i]
    exact hij.trans_le (Finset.single_le_sum (fun k hk ↦ hP i k) (Finset.mem_univ j))
  · rw [← hcol j]
    exact hij.trans_le (Finset.single_le_sum (fun k hk ↦ hP k j) (Finset.mem_univ i))

/-- Actual normalized within-bin laws only need bin support when their original
class mass is positive. Thus zero-bin Markov fallbacks never affect legality. -/
theorem positive_classFlow_bin_legal
    {I J : Type*} [Fintype I] [Fintype J]
    (P : I → J → ℝ) (a : I → ℝ) (b : J → ℝ)
    (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = a i) (hcol : ∀ j, ∑ i, P i j = b j)
    (α : I → Measure ℝ) (β : J → Measure ℝ)
    [∀ i, IsProbabilityMeasure (α i)] [∀ j, IsProbabilityMeasure (β j)]
    (sourceBin : I → Set ℝ) (targetBin : J → Set ℝ)
    (hsource : ∀ i, 0 < a i → ∀ᵐ x ∂α i, x ∈ sourceBin i)
    (htarget : ∀ j, 0 < b j → ∀ᵐ y ∂β j, y ∈ targetBin j)
    (allowed : I → J → Prop)
    (hzero : ∀ i j, ¬ allowed i j → P i j = 0)
    (hlegal : ∀ i j, allowed i j → ∀ x ∈ sourceBin i, ∀ y ∈ targetBin j, x ≤ y)
    (i : I) (j : J) (hij : 0 < P i j) :
    ∀ᵐ p ∂(α i).prod (β j), p.1 ≤ p.2 := by
  have hm := positive_classFlow_marginals P a b hP hrow hcol i j hij
  have ha : allowed i j := by
    by_contra hnot
    exact (ne_of_gt hij) (hzero i j hnot)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (hsource i hm.1),
    Measure.quasiMeasurePreserving_snd.ae (htarget j hm.2)] with p hx hy
  exact hlegal i j ha p.1 hx p.2 hy

end OTSelector.Reconstruction
