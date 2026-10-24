import LeanLevy.RandomMeasure.PoissonRandomMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.Variance
import OTSelector.Probability.PoissonCountDiscrepancy

/-!
Conditions: One actual Poisson point family on the disjoint union of two copies of a measurable carrier, with pairwise disjoint measurable finite-intensity cell sets.

Objects: True source/target copy intensities and expected total cell-count discrepancy bounded by the sum of sqrt(2 cell intensity).

Proof detail: Put the two color copies into one pairwise disjoint family, apply the actual joint product Poisson count law and integrate the computed independent-pair discrepancy.

References: Günter Last; Mathew Penrose: Section 3.1, Definition 3.1(i)–(ii), p. 19; Günter Last and Mathew Penrose: Section 2.3, Proposition 2.10, pp. 14–15; Section 3.1, Proposition 3.2, p. 20.
Relation: A law-level bridge from one actual doubled point family to independent color counts. It preserves multiplicities and does not depend on enumerating the realized points.
-/


/-!
# Cell-count discrepancies for a spatial Poisson random measure

Two independent colours of a Poisson point process on `E` are realized as one
Poisson point family on `E ⊕ E`.  On pairwise disjoint measurable sets `A i`,
the `ℝ`-valued source counts `N i` and target counts `M i` are independent
pushforwards of Poisson variables with the common mean `m (A i)`.  The expected
total histogram discrepancy obeys

`E ∑ i |N i - M i| ≤ ∑ i sqrt (2 * m (A i))`.

Only the level-wise count laws enter the hierarchical matching bound, so this
bridge is independent of any enumeration of the realized points.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Probability

variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E ⊕ E}
  {m : Measure E} [SigmaFinite m] [Nonempty E] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- The disjoint union of two copies of the intensity. -/
def doubleIntensity (m : Measure E) : Measure (E ⊕ E) :=
  m.map Sum.inl + m.map Sum.inr

instance : SigmaFinite (doubleIntensity m) := by
  unfold doubleIntensity
  have hemb_inl : MeasurableEmbedding (Sum.inl : E → E ⊕ E) :=
    ⟨Sum.inl_injective, measurable_inl, fun s hs => MeasurableSet.inl_image hs⟩
  have hemb_inr : MeasurableEmbedding (Sum.inr : E → E ⊕ E) :=
    ⟨Sum.inr_injective, measurable_inr, fun s hs => MeasurableSet.inr_image hs⟩
  haveI : SigmaFinite (m.map (Sum.inl : E → E ⊕ E)) := hemb_inl.sigmaFinite_map
  haveI : SigmaFinite (m.map (Sum.inr : E → E ⊕ E)) := hemb_inr.sigmaFinite_map
  infer_instance

/-- The source copy of a set. -/
def sourceCopy (A : Set E) : Set (E ⊕ E) := Sum.inl '' A

/-- The target copy of a set. -/
def targetCopy (A : Set E) : Set (E ⊕ E) := Sum.inr '' A

theorem measurableSet_sourceCopy {A : Set E} (hA : MeasurableSet A) :
    MeasurableSet (sourceCopy A) :=
  MeasurableSet.inl_image hA

theorem measurableSet_targetCopy {A : Set E} (hA : MeasurableSet A) :
    MeasurableSet (targetCopy A) :=
  MeasurableSet.inr_image hA

theorem doubleIntensity_sourceCopy (A : Set E) (hA : MeasurableSet A) :
    doubleIntensity m (sourceCopy A) = m A := by
  unfold doubleIntensity sourceCopy
  rw [Measure.add_apply, Measure.map_apply measurable_inl (MeasurableSet.inl_image hA),
    Measure.map_apply measurable_inr (MeasurableSet.inl_image (s := A) hA)]
  have hpre1 : Sum.inl ⁻¹' (Sum.inl '' A : Set (E ⊕ E)) = A := by
    ext x; simp
  have hpre2 : Sum.inr ⁻¹' (Sum.inl '' A : Set (E ⊕ E)) = (∅ : Set E) := by
    ext x; simp
  rw [hpre1, hpre2]; simp

theorem doubleIntensity_targetCopy (A : Set E) (hA : MeasurableSet A) :
    doubleIntensity m (targetCopy A) = m A := by
  unfold doubleIntensity targetCopy
  rw [Measure.add_apply, Measure.map_apply measurable_inr (MeasurableSet.inr_image hA),
    Measure.map_apply measurable_inl (MeasurableSet.inr_image (s := A) hA)]
  have hpre1 : Sum.inr ⁻¹' (Sum.inr '' A : Set (E ⊕ E)) = A := by
    ext x; simp
  have hpre2 : Sum.inl ⁻¹' (Sum.inr '' A : Set (E ⊕ E)) = (∅ : Set E) := by
    ext x; simp
  rw [hpre1, hpre2]; simp

/-- The expected histogram discrepancy between the two colours of a Poisson point
process on pairwise disjoint cells. -/
theorem integral_sum_abs_sub_poissonRandomMeasure_le
    (hd : IsPoissonPointFamily K X (doubleIntensity m) μ)
    {ι : Type*} [Fintype ι] (A : ι → Set E)
    (hA : ∀ i, MeasurableSet (A i)) (hfin : ∀ i, m (A i) < ⊤)
    (hdisj : Pairwise (Function.onFun Disjoint A)) :
    ∫ ω, (∑ i, |((poissonRandomMeasure K X ω) (sourceCopy (A i))).toReal -
        ((poissonRandomMeasure K X ω) (targetCopy (A i))).toReal|) ∂μ ≤
      ∑ i, Real.sqrt (2 * (m (A i)).toReal) := by
  classical
  let N : ι → Ω → ℝ := fun i ω =>
    ((poissonRandomMeasure K X ω) (sourceCopy (A i))).toReal
  let M : ι → Ω → ℝ := fun i ω =>
    ((poissonRandomMeasure K X ω) (targetCopy (A i))).toReal
  have hNraw (i : ι) : Measurable (fun ω =>
      (poissonRandomMeasure K X ω) (sourceCopy (A i))) :=
    measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point
      (measurableSet_sourceCopy (hA i))
  have hMraw (i : ι) : Measurable (fun ω =>
      (poissonRandomMeasure K X ω) (targetCopy (A i))) :=
    measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point
      (measurableSet_targetCopy (hA i))
  have hNmeas (i : ι) : Measurable (N i) := hNraw i |>.ennreal_toReal
  have hMmeas (i : ι) : Measurable (M i) := hMraw i |>.ennreal_toReal
  have hNlaw (i : ι) : μ.map (N i) =
      (poissonMeasure ((m (A i)).toNNReal)).map (Nat.cast : ℕ → ℝ) := by
    have h := map_poissonRandomMeasure_apply hd (measurableSet_sourceCopy (hA i))
      (by rw [doubleIntensity_sourceCopy (A i) (hA i)]; exact hfin i)
    rw [doubleIntensity_sourceCopy (A i) (hA i)] at h
    have hm : Measurable (fun z : ℝ≥0∞ => z.toReal) := ENNReal.measurable_toReal
    have hcast : ((fun z : ℝ≥0∞ => z.toReal) ∘ (fun n : ℕ => (n : ℝ≥0∞))) =
        (Nat.cast : ℕ → ℝ) := by
      funext n
      simp
    calc μ.map (N i)
        = μ.map ((fun z : ℝ≥0∞ => z.toReal) ∘
            (fun ω => (poissonRandomMeasure K X ω) (sourceCopy (A i)))) := rfl
      _ = (μ.map (fun ω => (poissonRandomMeasure K X ω) (sourceCopy (A i)))).map
            (fun z : ℝ≥0∞ => z.toReal) := (Measure.map_map hm (hNraw i)).symm
      _ = ((poissonMeasure ((m (A i)).toNNReal)).map (fun n : ℕ => (n : ℝ≥0∞))).map
            (fun z : ℝ≥0∞ => z.toReal) := by rw [h]
      _ = (poissonMeasure ((m (A i)).toNNReal)).map
            ((fun z : ℝ≥0∞ => z.toReal) ∘ (fun n : ℕ => (n : ℝ≥0∞))) :=
          Measure.map_map hm measurable_from_nat
      _ = (poissonMeasure ((m (A i)).toNNReal)).map (Nat.cast : ℕ → ℝ) := by rw [hcast]
  have hMlaw (i : ι) : μ.map (M i) =
      (poissonMeasure ((m (A i)).toNNReal)).map (Nat.cast : ℕ → ℝ) := by
    have h := map_poissonRandomMeasure_apply hd (measurableSet_targetCopy (hA i))
      (by rw [doubleIntensity_targetCopy (A i) (hA i)]; exact hfin i)
    rw [doubleIntensity_targetCopy (A i) (hA i)] at h
    have hm : Measurable (fun z : ℝ≥0∞ => z.toReal) := ENNReal.measurable_toReal
    have hcast : ((fun z : ℝ≥0∞ => z.toReal) ∘ (fun n : ℕ => (n : ℝ≥0∞))) =
        (Nat.cast : ℕ → ℝ) := by
      funext n
      simp
    calc μ.map (M i)
        = μ.map ((fun z : ℝ≥0∞ => z.toReal) ∘
            (fun ω => (poissonRandomMeasure K X ω) (targetCopy (A i)))) := rfl
      _ = (μ.map (fun ω => (poissonRandomMeasure K X ω) (targetCopy (A i)))).map
            (fun z : ℝ≥0∞ => z.toReal) := (Measure.map_map hm (hMraw i)).symm
      _ = ((poissonMeasure ((m (A i)).toNNReal)).map (fun n : ℕ => (n : ℝ≥0∞))).map
            (fun z : ℝ≥0∞ => z.toReal) := by rw [h]
      _ = (poissonMeasure ((m (A i)).toNNReal)).map
            ((fun z : ℝ≥0∞ => z.toReal) ∘ (fun n : ℕ => (n : ℝ≥0∞))) :=
          Measure.map_map hm measurable_from_nat
      _ = (poissonMeasure ((m (A i)).toNNReal)).map (Nat.cast : ℕ → ℝ) := by rw [hcast]
  have hdisjPair (i : ι) : Disjoint (sourceCopy (A i)) (targetCopy (A i)) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hzy⟩
    exact Sum.inl_ne_inr hzy.symm
  have hraw (i : ι) : IndepFun
      (fun ω => (poissonRandomMeasure K X ω) (sourceCopy (A i)))
      (fun ω => (poissonRandomMeasure K X ω) (targetCopy (A i))) μ :=
    indepFun_poissonRandomMeasure_apply hd (measurableSet_sourceCopy (hA i))
      (measurableSet_targetCopy (hA i)) (by rw [doubleIntensity_sourceCopy (A i) (hA i)]; exact hfin i)
      (by rw [doubleIntensity_targetCopy (A i) (hA i)]; exact hfin i) (hdisjPair i)
  have hindep (i : ι) : IndepFun (N i) (M i) μ :=
    hraw i |>.comp ENNReal.measurable_toReal ENNReal.measurable_toReal
  have hNint (i : ι) : Integrable (N i) μ := by
    simpa only [N] using integrable_toReal_poissonRandomMeasure_apply hd
      (measurableSet_sourceCopy (hA i)) (by rw [doubleIntensity_sourceCopy (A i) (hA i)]; exact hfin i)
  have hMint (i : ι) : Integrable (M i) μ := by
    simpa only [M] using integrable_toReal_poissonRandomMeasure_apply hd
      (measurableSet_targetCopy (hA i)) (by rw [doubleIntensity_targetCopy (A i) (hA i)]; exact hfin i)
  have hterm (i : ι) : Integrable (fun ω => |N i ω - M i ω|) μ :=
    ((hNint i).sub (hMint i)).abs
  have hpair (i : ι) : μ.map (fun ω => (N i ω, M i ω)) =
      ((poissonMeasure ((m (A i)).toNNReal)).map (Nat.cast : ℕ → ℝ)).prod
        ((poissonMeasure ((m (A i)).toNNReal)).map (Nat.cast : ℕ → ℝ)) := by
    have h := (indepFun_iff_map_prod_eq_prod_map_map (hNmeas i).aemeasurable
      (hMmeas i).aemeasurable).mp (hindep i)
    rwa [hNlaw i, hMlaw i] at h
  have hpiece (i : ι) :
      ∫ ω, |N i ω - M i ω| ∂μ =
        ∫ z : ℝ × ℝ, |z.1 - z.2|
          ∂(((poissonMeasure ((m (A i)).toNNReal)).map (Nat.cast : ℕ → ℝ)).prod
            ((poissonMeasure ((m (A i)).toNNReal)).map (Nat.cast : ℕ → ℝ))) := by
    have hcont : Continuous (fun z : ℝ × ℝ => |z.1 - z.2|) := by
      continuity
    rw [← hpair i]
    exact (integral_map ((hNmeas i).prodMk (hMmeas i)).aemeasurable
      hcont.aestronglyMeasurable).symm
  calc
    ∫ ω, (∑ i, |N i ω - M i ω|) ∂μ
        = ∑ i, ∫ ω, |N i ω - M i ω| ∂μ :=
      integral_finsetSum _ (fun i _ => hterm i)
    _ = ∑ i, ∫ z : ℝ × ℝ, |z.1 - z.2|
          ∂(((poissonMeasure ((m (A i)).toNNReal)).map (Nat.cast : ℕ → ℝ)).prod
            ((poissonMeasure ((m (A i)).toNNReal)).map (Nat.cast : ℕ → ℝ))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hpiece i
    _ ≤ ∑ i, Real.sqrt (2 * (m (A i)).toReal) :=
      Finset.sum_le_sum fun i _ => integral_abs_sub_poissonPair_cast_le _

end OTSelector.Probability
