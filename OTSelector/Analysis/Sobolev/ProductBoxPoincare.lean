import OTSelector.Analysis.Sobolev.SmoothBoxPoincare
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalProductBoxPoincare.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalProductBoxPoincare`; the selected original proof blocks follow. -/
section

/-!
Conditions: A C1 function on an ordered face-times-normal product box with explicit side-length bounds.

Objects: Measure-preserving coordinate split and the actual product-box Poincaré energy estimate.

Proof detail: Regroup finite product Lebesgue coordinates, apply the smooth-box inequality and separate tangential and normal derivatives.

Sources: D. H. Fremlin, Section 251W(g)–(h), pp. 14–15: finite product measures, sigma-finiteness and regrouping by a partition of the coordinate set (https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=14); Jiří Lebl, Section 5.3.1, Theorem 5.3.1, pp. 200–201 (https://www.jirka.org/ra/realanal.pdf#page=200); Rick Durrett, Section 1.6.3, variance identities (1.6.2)–(1.6.4), p. 33; Section 2.1.2, Theorems 2.1.11–2.1.13, pp. 48–49 (https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=41).
Relation: Product-coordinate adapter with the exact dimension factor; the split is the actual coordinate map.
-/

/-! The actual rectangle Poincare estimate in face-times-normal coordinates. -/
open Set Function Filter MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

/-- Separate the first scalar coordinate as the physical normal coordinate. -/
def cubeProductSplit (q : ℕ) : (Fin (q + 1) → ℝ) →L[ℝ] (Fin q → ℝ) × ℝ :=
  (ContinuousLinearMap.pi fun i : Fin q ↦ ContinuousLinearMap.proj i.succ).prod
    (ContinuousLinearMap.proj 0)

private def cubeProductSplitEquiv (q : ℕ) : (Fin (q + 1) → ℝ) ≃ᵐ (Fin q → ℝ) × ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (q + 1) ↦ ℝ) 0).trans
    MeasurableEquiv.prodComm

private theorem cubeProductSplit_eq (q : ℕ) :
    (cubeProductSplit q : (Fin (q + 1) → ℝ) → (Fin q → ℝ) × ℝ) = cubeProductSplitEquiv q := by
  funext x
  rfl

/-- This concrete continuous linear coordinate split preserves actual volume. -/
theorem measurePreserving_cubeProductSplit (q : ℕ) :
    MeasurePreserving (cubeProductSplit q) volume volume := by
  rw [cubeProductSplit_eq]
  exact Measure.measurePreserving_swap.comp (volume_preserving_piFinSuccAbove
    (fun _ : Fin (q + 1) ↦ ℝ) 0)

/-- Exact change of variables between a literal scalar-coordinate box and its face collar. -/
theorem integral_cubeProductSplit_box {q : ℕ} (a b : Fin q → ℝ) (c d : ℝ)
    (g : (Fin q → ℝ) × ℝ → ℝ) :
    (∫ x in Icc (Fin.cons c a : Fin (q + 1) → ℝ) (Fin.cons d b : Fin (q + 1) → ℝ), g (cubeProductSplit q x)) =
      ∫ p in Icc a b ×ˢ Icc c d, g p := by
  let e := cubeProductSplitEquiv q
  have hm : MeasurePreserving e volume volume := by
    rw [← cubeProductSplit_eq]
    exact measurePreserving_cubeProductSplit q
  have hpre : e ⁻¹' (Icc a b ×ˢ Icc c d) = Icc (Fin.cons c a : Fin (q + 1) → ℝ) (Fin.cons d b : Fin (q + 1) → ℝ) := by
    ext x
    change ((fun i : Fin q ↦ x i.succ) ∈ Icc a b ∧ x 0 ∈ Icc c d) ↔ _
    simp only [mem_Icc, Pi.le_def]
    constructor
    · rintro ⟨⟨hxa,hxb⟩,hxc,hxd⟩
      constructor <;> intro i <;> refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact hxc
      · exact hxa j
      · exact hxd
      · exact hxb j
    · rintro ⟨hxa,hxb⟩
      exact ⟨⟨fun i ↦ hxa i.succ, fun i ↦ hxb i.succ⟩, hxa 0, hxb 0⟩
  have hmr : MeasurePreserving e (volume.restrict (Icc (Fin.cons c a : Fin (q + 1) → ℝ) (Fin.cons d b : Fin (q + 1) → ℝ)))
      (volume.restrict (Icc a b ×ˢ Icc c d)) := by
    refine ⟨e.measurable, ?_⟩
    rw [← hpre, ← Measure.restrict_map e.measurable (measurableSet_Icc.prod measurableSet_Icc), hm.map_eq]
  rw [cubeProductSplit_eq]
  exact hmr.integral_comp' g

/-- Actual finite-cell approximation on a face-times-normal collar, in the
original physical coordinate directions used by the smooth trace estimate. -/
theorem smooth_product_box_poincare_sq_of_side_le
    {q : ℕ} {a b : Fin q → ℝ} (hab : ∀ i, a i < b i)
    {c d : ℝ} (hcd : c < d)
    {f : (Fin q → ℝ) × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {h : ℝ} (hh : 0 ≤ h) (hside : ∀ i, b i - a i ≤ h) (hnormal : d - c ≤ h) :
    2 * (∫ p in Icc a b ×ˢ Icc c d,
      (f p - (volume.real (Icc a b ×ˢ Icc c d))⁻¹ *
        (∫ z in Icc a b ×ˢ Icc c d, f z))^2) ≤
      ((q + 1 : ℕ) : ℝ) * h^2 *
        ((∑ i : Fin q, ∫ p in Icc a b ×ˢ Icc c d,
          (fderiv ℝ f p (Pi.single i 1, 0))^2) +
          (∫ p in Icc a b ×ˢ Icc c d, (fderiv ℝ f p (0, 1))^2)) := by
  classical
  let L := cubeProductSplit q
  have hfc : ContDiff ℝ 1 (fun x : Fin (q + 1) → ℝ ↦ f (L x)) := hf.comp L.contDiff
  have hbox : ∀ i : Fin (q + 1), (Fin.cons c a : Fin (q + 1) → ℝ) i < (Fin.cons d b : Fin (q + 1) → ℝ) i := by
    intro i
    exact Fin.cases hcd (fun j ↦ hab j) i
  have hsides : ∀ i : Fin (q + 1), (Fin.cons d b : Fin (q + 1) → ℝ) i - (Fin.cons c a : Fin (q + 1) → ℝ) i ≤ h := by
    intro i
    exact Fin.cases hnormal (fun j ↦ hside j) i
  have hp := smooth_box_poincare_sq_of_side_le hbox hfc hh hsides
  have hd (x : Fin (q + 1) → ℝ) :
      fderiv ℝ (fun y : Fin (q + 1) → ℝ ↦ f (L y)) x =
        (fderiv ℝ f (L x)).comp L :=
    ((hf.differentiable (by norm_num) (L x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv
  have hL0 : L (Pi.single (0 : Fin (q + 1)) 1) = (0, 1) := by
    ext i <;> simp [L, cubeProductSplit]
  have hLi (i : Fin q) : L (Pi.single i.succ 1) = (Pi.single i 1, 0) := by
    ext j <;> simp [L, cubeProductSplit, Pi.single_apply]
  have hvol : volume.real (Icc (Fin.cons c a : Fin (q + 1) → ℝ) (Fin.cons d b : Fin (q + 1) → ℝ)) =
      volume.real (Icc a b ×ˢ Icc c d) := by
    have he := integral_cubeProductSplit_box a b c d (fun _ ↦ (1 : ℝ))
    simpa only [setIntegral_const, smul_eq_mul, mul_one] using he
  simp only [hd, ContinuousLinearMap.comp_apply] at hp
  rw [Fin.sum_univ_succ] at hp
  simp only [hL0, hLi] at hp
  rw [show (∫ x in Icc (Fin.cons c a : Fin (q + 1) → ℝ) (Fin.cons d b : Fin (q + 1) → ℝ), f (L x)) =
      ∫ p in Icc a b ×ˢ Icc c d, f p from integral_cubeProductSplit_box a b c d f,
    hvol] at hp
  rw [show (∫ x in Icc (Fin.cons c a : Fin (q + 1) → ℝ) (Fin.cons d b : Fin (q + 1) → ℝ),
      (f (L x) - (volume.real (Icc a b ×ˢ Icc c d))⁻¹ *
        (∫ p in Icc a b ×ˢ Icc c d, f p))^2) =
      ∫ p in Icc a b ×ˢ Icc c d,
        (f p - (volume.real (Icc a b ×ˢ Icc c d))⁻¹ *
          (∫ z in Icc a b ×ˢ Icc c d, f z))^2 from
      integral_cubeProductSplit_box a b c d (fun p ↦
        (f p - (volume.real (Icc a b ×ˢ Icc c d))⁻¹ *
          (∫ z in Icc a b ×ˢ Icc c d, f z))^2)] at hp
  have hnormalInt : (∫ x in Icc (Fin.cons c a : Fin (q + 1) → ℝ) (Fin.cons d b : Fin (q + 1) → ℝ),
      (fderiv ℝ f (L x) (0, 1))^2) =
      ∫ p in Icc a b ×ˢ Icc c d, (fderiv ℝ f p (0, 1))^2 :=
    integral_cubeProductSplit_box a b c d (fun p ↦ (fderiv ℝ f p (0, 1))^2)
  have htangentInt (i : Fin q) : (∫ x in Icc (Fin.cons c a : Fin (q + 1) → ℝ) (Fin.cons d b : Fin (q + 1) → ℝ),
      (fderiv ℝ f (L x) (Pi.single i 1, 0))^2) =
      ∫ p in Icc a b ×ˢ Icc c d, (fderiv ℝ f p (Pi.single i 1, 0))^2 :=
    integral_cubeProductSplit_box a b c d (fun p ↦ (fderiv ℝ f p (Pi.single i 1, 0))^2)
  simpa only [hnormalInt, htangentInt, add_comm] using hp

end OTSelector.Reconstruction

end
end
