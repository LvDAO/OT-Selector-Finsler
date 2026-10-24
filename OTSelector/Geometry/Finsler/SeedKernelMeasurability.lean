import Mathlib.Analysis.Matrix.MeasurableSpace
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.LengthHessianRegularity
import OTSelector.Geometry.Finsler.IntrinsicLabelHessian
import OTSelector.Geometry.Finsler.Jacobi.LabelHessian
import OTSelector.Geometry.Finsler.TangentReadout
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerSeedKernelMeasurability.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerSeedKernelMeasurability`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.SeedKernelMeasurability

* **Conditions:** An actual seed with countably many Lipschitz readout charts and smooth strong convexity; generic helper hypotheses specify Borel domains and finite matrix sizes.
* **Objects:** Joint Borel original label Hessians and totalized matrix-inverse kernels, including restricted/indicator and AE forms.
* **Proof detail:** Compute the intrinsic Hessian through Borel ordinary derivatives on chart pieces, use zero totalized derivatives on nondifferentiability branches, then patch the countable cover and take measurable matrix inversion.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).

Source relation (derived): Measurability is proved from the actual family, without measurable selection of smooth comparisons. Matrix inversion at singular points follows the formal totalized convention.
-/

/-!
# Joint measurability of the original seed Hessian and inverse kernel

The actual seed has a countable cover by Lipschitz coordinate readouts. On each
piece its intrinsic label Hessian is computed by the Borel ordinary derivative
and the smooth fiber Hessian on the slit domain. At nondifferentiable points both
matrices vanish. Thus no measurable selection of smooth comparisons is needed.
-/

open Set Filter Metric MeasureTheory Matrix Module Manifold
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E W M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

private theorem measurable_indicator_of_subtype {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Zero β]
    {s : Set α} {f : α → β} (hs : MeasurableSet s)
    (hf : Measurable (fun x : s ↦ f x)) : Measurable (s.indicator f) := by
  apply measurable_of_restrict_of_restrict_compl hs
  · convert hf using 1
    funext x
    exact indicator_of_mem x.2 f
  · convert (measurable_const (a := (0 : β))) using 1
    funext x
    exact indicator_of_notMem x.2 f

/-- The usual matrix inverse, zero on singular matrices, is Borel. -/
theorem measurable_real_matrix_inverse [Fintype ι] [DecidableEq ι] :
    Measurable (fun A : Matrix ι ι ℝ ↦ A⁻¹) := by
  have hd : Measurable (fun A : Matrix ι ι ℝ ↦ A.det) :=
    continuous_id.matrix_det.measurable
  have ha : Measurable (fun A : Matrix ι ι ℝ ↦ A.adjugate) :=
    continuous_id.matrix_adjugate.measurable
  convert hd.inv.smul ha using 1
  funext A
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rfl

namespace IsSmoothStronglyConvex

/-- The genuine fiber Hessian, set to zero off the open slit chart domain, is Borel. -/
theorem measurable_chartLength_fiberHessian_slit (hF : F.IsSmoothStronglyConvex)
    (old : M) :
    Measurable ((chartEnergyDomain old).indicator (fun z : E × E ↦
      fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength old (z.1, v) : ℝ))) z.2)) := by
  classical
  have hc : ContinuousOn (fun z : E × E ↦
      fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength old (z.1, v) : ℝ))) z.2)
      (chartEnergyDomain old) :=
    fun z hz ↦ (hF.contDiffAt_chartLength_fiberHessian old hz).continuousAt.continuousWithinAt
  exact (continuousOn_iff_continuous_domRestrict.mp hc).measurable.dite measurable_const
    (isOpen_chartEnergyDomain old).measurableSet

/-- A Borel chart readout gives a Borel actual label Hessian whenever its time
velocity is legal or its entire derivative vanishes. -/
theorem measurable_chartFamilyLabelHessianMatrix_restrict
    (hF : F.IsSmoothStronglyConvex) (old : M) (bW : Basis ι ℝ W)
    (x : W × ℝ → E) (s : Set (W × ℝ))
    (hx : Measurable (fun q : s ↦ x q))
    (hlegal : ∀ q ∈ s, (x q, fderiv ℝ x q (0, 1)) ∈ chartEnergyDomain old ∨
      fderiv ℝ x q = 0) :
    Measurable (fun q : s ↦ F.chartFamilyLabelHessianMatrix old bW x q) := by
  let H := (chartEnergyDomain old).indicator (fun z : E × E ↦
    fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength old (z.1, v) : ℝ))) z.2)
  have hD : Measurable (fun q : s ↦ fderiv ℝ x q) :=
    (measurable_fderiv ℝ x).comp measurable_subtype_coe
  have hv : Measurable (fun q : s ↦ fderiv ℝ x q (0, 1)) :=
    (measurable_fderiv_apply_const ℝ x (0, 1)).comp measurable_subtype_coe
  have hH : Measurable (fun q : s ↦ H (x q, fderiv ℝ x q (0, 1))) :=
    (hF.measurable_chartLength_fiberHessian_slit old).comp (hx.prodMk hv)
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have heval : Continuous (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × ((W × ℝ) →L[ℝ] E) ↦
      p.1 (p.2 (bW j, 0)) (p.2 (bW i, 0))) := by
    fun_prop
  convert heval.measurable.comp (hH.prodMk hD) using 1
  funext q
  rcases hlegal q q.2 with hz | hz
  · simp only [Function.comp_apply, H, indicator_of_mem hz, chartFamilyLabelHessianMatrix]
  · simp only [Function.comp_apply, hz, _root_.zero_apply, _root_.map_zero,
      chartFamilyLabelHessianMatrix]

end IsSmoothStronglyConvex

namespace CalibratedLevelSeedPatch

variable {u : M → ℝ}

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The retained Lipschitz coordinate cover gives actual joint continuity at every
point of the original open label domain. -/
theorem continuousAt_joint_curve (S : CalibratedLevelSeedPatch F u)
    {q : S.covector.ker × ℝ} (hq : q.1 ∈ S.openLabels) :
    ContinuousAt (fun z : S.covector.ker × ℝ ↦ S.curve z.1 z.2) q := by
  have hcover : (q.2, q.1) ∈ ⋃ c ∈ S.centers, ball c (S.radius c) := by
    rw [S.local_cover]
    exact ⟨mem_univ _, hq⟩
  obtain ⟨c, hc, hqc⟩ := mem_iUnion₂.mp hcover
  obtain ⟨_, _, hsource, hlip⟩ := S.local_data c hc
  let old := S.curve c.2 c.1
  let x := fun z : S.covector.ker × ℝ ↦ extChartAt 𝓘(ℝ, E) old (S.curve z.1 z.2)
  have hxc : ContinuousAt x q :=
    (hlip.continuousOn.continuousAt
      (mem_of_superset (isOpen_ball.mem_nhds hqc) ball_subset_closedBall)).comp
        (f := Prod.swap) continuous_swap.continuousAt
  have hlegal := hsource (ball_subset_closedBall hqc)
  have hi := (continuousAt_extChartAt_symm' hlegal).comp (f := x) hxc
  apply hi.congr_of_eventuallyEq
  have hn : ∀ᶠ z : S.covector.ker × ℝ in 𝓝 q,
      (z.2, z.1) ∈ ball c (S.radius c) :=
    continuous_swap.continuousAt.eventually (isOpen_ball.mem_nhds hqc)
  filter_upwards [hn] with z hz
  exact ((extChartAt 𝓘(ℝ, E) old).left_inv
    (hsource (ball_subset_closedBall hz))).symm

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- At a differentiability point the original joint time derivative is nonzero,
as follows from the original curve's unit speed. -/
theorem joint_time_mfderiv_ne_zero (S : CalibratedLevelSeedPatch F u)
    {w : S.covector.ker} (hw : w ∈ S.labels) (t : ℝ)
    (hd : MDifferentiableAt 𝓘(ℝ, S.covector.ker × ℝ) 𝓘(ℝ, E)
      (fun q ↦ S.curve q.1 q.2) (w, t)) :
    mfderiv 𝓘(ℝ, S.covector.ker × ℝ) 𝓘(ℝ, E)
      (fun q ↦ S.curve q.1 q.2) (w, t) (0, 1) ≠ 0 := by
  have hs : HasFDerivAt (fun s : ℝ ↦ (w, s))
      (ContinuousLinearMap.inr ℝ S.covector.ker ℝ) t :=
    (hasFDerivAt_const w t).prodMk (hasFDerivAt_id t)
  have hD := mfderiv_comp t hd hs.differentiableAt.mdifferentiableAt
  rw [mfderiv_eq_fderiv, hs.fderiv] at hD
  have ht : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (S.curve w) t 1 =
      mfderiv 𝓘(ℝ, S.covector.ker × ℝ) 𝓘(ℝ, E)
        (fun q ↦ S.curve q.1 q.2) (w, t) (0, 1) :=
    congrArg (fun L : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, E) (S.curve w t) ↦ L 1) hD
  intro hz
  have hu := S.unit w hw t
  change F.toFun ⟨S.curve w t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (S.curve w) t 1⟩ = 1 at hu
  rw [ht, hz, F.map_zero] at hu
  exact zero_ne_one hu

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Every legal chart computes the exact intrinsic original matrix, including
points where the original joint map is not differentiable. -/
theorem chart_labelHessian_eq_intrinsic (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex) (old : M) (bW : Basis ι ℝ S.covector.ker)
    {q : S.covector.ker × ℝ} (hq : q.1 ∈ S.labels)
    (hx : S.curve q.1 q.2 ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    F.chartFamilyLabelHessianMatrix old bW
      (fun z ↦ extChartAt 𝓘(ℝ, E) old (S.curve z.1 z.2)) q =
      F.familyLabelHessianMatrix bW (fun z ↦ S.curve z.1 z.2) q := by
  by_cases hd : MDifferentiableAt 𝓘(ℝ, S.covector.ker × ℝ) 𝓘(ℝ, E)
      (fun z ↦ S.curve z.1 z.2) q
  · exact hF.chartFamilyLabelHessianMatrix_eq_intrinsic old bW hd hx
      (S.joint_time_mfderiv_ne_zero hq q.2 hd)
  · have hc : ¬ DifferentiableAt ℝ
        (fun z : S.covector.ker × ℝ ↦ extChartAt 𝓘(ℝ, E) old (S.curve z.1 z.2)) q := by
      intro hc
      apply hd
      exact (mdifferentiableAt_iff_target_of_mem_source
        (I := 𝓘(ℝ, S.covector.ker × ℝ)) (I' := 𝓘(ℝ, E))
        (by simpa only [extChartAt_source] using hx)).mpr
        ⟨S.continuousAt_joint_curve (S.labels_subset hq), hc.mdifferentiableAt⟩
    simp only [chartFamilyLabelHessianMatrix, familyLabelHessianMatrix,
      fderiv_zero_of_not_differentiableAt hc, mfderiv_zero_of_not_mdifferentiableAt hd,
      ContinuousLinearMap.comp_zero, _root_.zero_apply, _root_.map_zero]

/-- On each retained coordinate ball the intrinsic matrix is jointly Borel on
all original labels, with no pointwise differentiability hypothesis. -/
theorem measurable_labelHessian_on_chartBall (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ S.covector.ker)
    (c : S.centers) :
    Measurable (fun q : {q : S.covector.ker × ℝ |
        q.1 ∈ S.labels ∧ (q.2, q.1) ∈ ball c.1 (S.radius c)} ↦
      F.familyLabelHessianMatrix bW (fun z ↦ S.curve z.1 z.2) q) := by
  let old := S.curve c.1.2 c.1.1
  let x := fun z : S.covector.ker × ℝ ↦ extChartAt 𝓘(ℝ, E) old (S.curve z.1 z.2)
  let s := {q : S.covector.ker × ℝ |
    q.1 ∈ S.labels ∧ (q.2, q.1) ∈ ball c.1 (S.radius c)}
  obtain ⟨_, _, hsource, hlip⟩ := S.local_data c c.2
  have hx : Measurable (fun q : s ↦ x q) := by
    apply Continuous.measurable
    apply continuous_iff_continuousAt.mpr
    intro q
    have hc := (hlip.continuousOn.continuousAt
      (mem_of_superset (isOpen_ball.mem_nhds q.2.2) ball_subset_closedBall)).comp
        (f := Prod.swap) continuous_swap.continuousAt
    exact hc.comp (f := Subtype.val) continuous_subtype_val.continuousAt
  have hlegal : ∀ q ∈ s, (x q, fderiv ℝ x q (0, 1)) ∈ chartEnergyDomain old ∨
      fderiv ℝ x q = 0 := by
    intro q hq
    by_cases hd : DifferentiableAt ℝ x q
    · left
      have ht := (hd.hasFDerivAt.comp_hasDerivAt q.2
        ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))).deriv
      have hz := (hF.chartTangent_of_isEulerLagrangeAt
        (S.complete q.1 hq.1 q.2 (mem_univ _)) old
          (hsource (ball_subset_closedBall hq.2))).2
      change (x q, deriv (fun t ↦ x (q.1, t)) q.2) ∈ chartEnergyDomain old at hz
      change deriv (fun t ↦ x (q.1, t)) q.2 = _ at ht
      rwa [ht] at hz
    · exact Or.inr (fderiv_zero_of_not_differentiableAt hd)
  have hm := hF.measurable_chartFamilyLabelHessianMatrix_restrict old bW x s hx hlegal
  convert hm using 1
  funext q
  exact (S.chart_labelHessian_eq_intrinsic hF old bW q.2.1
    (hsource (ball_subset_closedBall q.2.2))).symm

/-- The original intrinsic label Hessian is Borel jointly in the retained label
and original time. This is the literal intrinsic matrix, not a selected version. -/
theorem measurable_familyLabelHessianMatrix (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ S.covector.ker) :
    Measurable (fun q : S.labels × ℝ ↦
      F.familyLabelHessianMatrix bW (fun z ↦ S.curve z.1 z.2) (q.1, q.2)) := by
  have : Countable S.centers := S.centers_countable.to_subtype
  let T := fun c : S.centers ↦ {q : S.labels × ℝ |
    (q.2, (q.1 : S.covector.ker)) ∈ ball c.1 (S.radius c)}
  have hT (c : S.centers) : MeasurableSet (T c) :=
    isOpen_ball.measurableSet.preimage (measurable_snd.prodMk
      (measurable_subtype_coe.comp measurable_fst))
  have hcover : ⋃ c, T c = univ := by
    apply eq_univ_of_forall
    intro q
    have hq : (q.2, (q.1 : S.covector.ker)) ∈ ⋃ c ∈ S.centers,
        ball c (S.radius c) := by
      rw [S.local_cover]
      exact ⟨mem_univ _, S.labels_subset q.1.2⟩
    obtain ⟨c, hc, hqc⟩ := mem_iUnion₂.mp hq
    exact mem_iUnion.mpr ⟨⟨c, hc⟩, hqc⟩
  let f := fun q : S.labels × ℝ ↦
    F.familyLabelHessianMatrix bW (fun z ↦ S.curve z.1 z.2) (q.1, q.2)
  have hm (c : S.centers) : Measurable (fun q : T c ↦ f q) := by
    have hp : Measurable (fun q : T c ↦
        (⟨((q.1.1 : S.covector.ker), q.1.2), q.1.1.2, q.2⟩ :
          {q : S.covector.ker × ℝ |
            q.1 ∈ S.labels ∧ (q.2, q.1) ∈ ball c.1 (S.radius c)})) :=
      ((measurable_subtype_coe.comp (measurable_fst.comp measurable_subtype_coe)).prodMk
        (measurable_snd.comp measurable_subtype_coe)).subtype_mk
    exact (S.measurable_labelHessian_on_chartBall hF bW c).comp hp
  have hl := measurable_liftCover T hT (fun c q ↦ f q) hm (fun _ _ _ _ _ ↦ rfl) hcover
  convert hl using 1
  funext q
  have hq : q ∈ ⋃ c, T c := by rw [hcover]; trivial
  obtain ⟨c, hc⟩ := mem_iUnion.mp hq
  exact (liftCover_of_mem (f := fun c q ↦ f q)
    (hf := fun _ _ _ _ _ ↦ rfl) (hS := hcover) hc).symm

/-- The original inverse label Hessian is jointly Borel, with the usual zero
matrix inverse at singular points. -/
theorem measurable_familyLabelKernel [Fintype ι] [DecidableEq ι]
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    (bW : Basis ι ℝ S.covector.ker) :
    Measurable (fun q : S.labels × ℝ ↦
      (F.familyLabelHessianMatrix bW (fun z ↦ S.curve z.1 z.2) (q.1, q.2))⁻¹) := by
  exact measurable_real_matrix_inverse.comp
    (S.measurable_familyLabelHessianMatrix hF bW)

/-- Extending the original label Hessian by zero outside the retained labels
produces a Borel matrix on the full label-time product. -/
theorem measurable_indicator_familyLabelHessianMatrix
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    (bW : Basis ι ℝ S.covector.ker) :
    Measurable ((S.labels ×ˢ (univ : Set ℝ)).indicator
      (F.familyLabelHessianMatrix bW (fun z ↦ S.curve z.1 z.2))) := by
  classical
  have hp : Measurable (fun q : S.labels ×ˢ (univ : Set ℝ) ↦
      (⟨q.1.1, q.2.1⟩, q.1.2) : (S.labels ×ˢ (univ : Set ℝ)) → S.labels × ℝ) :=
    ((measurable_fst.comp measurable_subtype_coe).subtype_mk).prodMk
      (measurable_snd.comp measurable_subtype_coe)
  have hm : Measurable (fun q : S.labels ×ˢ (univ : Set ℝ) ↦
      F.familyLabelHessianMatrix bW (fun z ↦ S.curve z.1 z.2) q) :=
    (S.measurable_familyLabelHessianMatrix hF bW).comp hp
  exact measurable_indicator_of_subtype (S.labels_measurable.prod MeasurableSet.univ) hm

/-- The same zero extension for the original inverse matrix is Borel. -/
theorem measurable_indicator_familyLabelKernel [Fintype ι] [DecidableEq ι]
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    (bW : Basis ι ℝ S.covector.ker) :
    Measurable ((S.labels ×ˢ (univ : Set ℝ)).indicator
      (fun q ↦ (F.familyLabelHessianMatrix bW (fun z ↦ S.curve z.1 z.2) q)⁻¹)) := by
  have hm := measurable_real_matrix_inverse.comp
    (S.measurable_indicator_familyLabelHessianMatrix hF bW)
  convert hm using 1
  funext q
  by_cases hq : q ∈ S.labels ×ˢ (univ : Set ℝ)
  · simp only [Function.comp_apply, indicator_of_mem hq]
  · simp only [Function.comp_apply, indicator_of_notMem hq, Matrix.inv_zero]

/-- The exact original inverse matrix is ae-measurable for every measure restricted
to the original label-time domain. -/
theorem aemeasurable_familyLabelKernel [Fintype ι] [DecidableEq ι]
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    (bW : Basis ι ℝ S.covector.ker) (μ : Measure (S.covector.ker × ℝ)) :
    AEMeasurable (fun q ↦
      (F.familyLabelHessianMatrix bW (fun z ↦ S.curve z.1 z.2) q)⁻¹)
      (μ.restrict (S.labels ×ˢ univ)) := by
  apply (S.measurable_indicator_familyLabelKernel hF bW).aemeasurable.congr
  filter_upwards [ae_restrict_mem (S.labels_measurable.prod MeasurableSet.univ)] with q hq
  exact indicator_of_mem hq _

end CalibratedLevelSeedPatch
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
