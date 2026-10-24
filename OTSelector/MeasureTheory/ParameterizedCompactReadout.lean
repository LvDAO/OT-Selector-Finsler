import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasureCountableTests
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneParameterizedCompactReadout.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneParameterizedCompactReadout`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.ParameterizedCompactReadout

## Lemma skeleton

* **Conditions:** A jointly compactly supported continuous parameter-edge kernel and a vaguely varying locally finite edge measure.
* **Objects:** Compact slices with one common edge support, uniform bounds and jointly continuous parameterized compact readout.
* **Proof detail:** Project the joint compact support, use uniform convergence of slices on it, and choose one nonnegative cutoff controlling local masses; split parameter error from vague-test error.

## Mathematical sources

- [Olav Kallenberg, Random Measures, Theory and Applications (Springer 2017)](https://link.springer.com/chapter/10.1007/978-3-319-41598-7_4): Chapter 4 opening, pp. 109–110, and Section 4.1 “Weak and vague topologies”, pp. 111–117.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=99): Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.

Source relation (composition): Compact-support joint continuity, not weak continuity for arbitrary noncompact tests.
-/

/-!
# Compact tests depending on the actual macroscopic parameter

A jointly compactly supported kernel has slices with one common compact edge
support. Compact-open convergence of these slices and a single nonnegative
cutoff give joint continuity against the actual vague locally finite plan.
-/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {V X : Type*} [TopologicalSpace V] [TopologicalSpace X]
  [MeasurableSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [PseudoMetrizableSpace X]

/-- The fixed compact edge projection of the actual joint kernel support. -/
def parameterizedCompactEdgeSupport (k : C_c(V × X, ℝ)) : Set X :=
  Prod.snd '' tsupport k

theorem isCompact_parameterizedCompactEdgeSupport (k : C_c(V × X, ℝ)) :
    IsCompact (parameterizedCompactEdgeSupport k) :=
  k.hasCompactSupport.image continuous_snd

/-- Every parameter slice is a genuine compact test on the original edge space. -/
def parameterizedCompactSlice (k : C_c(V × X, ℝ)) (w : V) : C_c(X, ℝ) where
  toFun x := k (w, x)
  continuous_toFun := k.continuous.comp (continuous_const.prodMk continuous_id)
  hasCompactSupport' := by
    apply (isCompact_parameterizedCompactEdgeSupport k).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (isCompact_parameterizedCompactEdgeSupport k).isClosed
    intro x hx
    exact ⟨(w, x), subset_closure hx, rfl⟩

@[simp] theorem parameterizedCompactSlice_apply (k : C_c(V × X, ℝ)) (w : V) (x : X) :
    parameterizedCompactSlice k w x = k (w, x) := rfl

theorem tsupport_parameterizedCompactSlice_subset (k : C_c(V × X, ℝ)) (w : V) :
    tsupport (parameterizedCompactSlice k w) ⊆ parameterizedCompactEdgeSupport k := by
  apply closure_minimal _ (isCompact_parameterizedCompactEdgeSupport k).isClosed
  intro x hx
  exact ⟨(w, x), subset_closure hx, rfl⟩

theorem parameterizedCompactSlice_eq_zero_of_notMem (k : C_c(V × X, ℝ))
    (w : V) {x : X} (hx : x ∉ parameterizedCompactEdgeSupport k) :
    parameterizedCompactSlice k w x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (tsupport_parameterizedCompactSlice_subset k w hh))

/-- Slicing never enlarges the original joint test's supremum norm. -/
theorem norm_parameterizedCompactSlice_le (k : C_c(V × X, ℝ)) (w : V) :
    ‖(parameterizedCompactSlice k w).toBoundedContinuousFunction‖ ≤
      ‖k.toBoundedContinuousFunction‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
  intro x
  exact k.toBoundedContinuousFunction.norm_coe_le_norm (w, x)

/-- The actual integral of a joint compact kernel at the actual parameter. -/
def parameterizedCompactReadout (k : C_c(V × X, ℝ)) (p : V × LocalFiniteMeasure X) : ℝ :=
  LocalFiniteMeasure.testIntegral p.2 (parameterizedCompactSlice k p.1)

/-- The projected support gives the actual source-window mass bound, also
when that window has infinite mass under a locally finite plan. -/
theorem ofReal_abs_parameterizedCompactReadout_le_window (k : C_c(V × X, ℝ))
    (w : V) (π : LocalFiniteMeasure X) (U : Set X) (hU : MeasurableSet U)
    (hsupport : parameterizedCompactEdgeSupport k ⊆ U) :
    ENNReal.ofReal |parameterizedCompactReadout k (w, π)| ≤
      ENNReal.ofReal ‖k.toBoundedContinuousFunction‖ * (π : Measure X) U := by
  have hb (x : X) : ‖parameterizedCompactSlice k w x‖ₑ ≤
      U.indicator (fun _ ↦ ENNReal.ofReal ‖k.toBoundedContinuousFunction‖) x := by
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx, Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (by
        simpa only [parameterizedCompactSlice_apply,
          CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply,
          Real.norm_eq_abs] using k.toBoundedContinuousFunction.norm_coe_le_norm (w, x))
    · rw [Set.indicator_of_notMem hx,
        parameterizedCompactSlice_eq_zero_of_notMem k w (fun hh ↦ hx (hsupport hh)), enorm_zero]
  calc
    _ = ‖∫ x, parameterizedCompactSlice k w x ∂(π : Measure X)‖ₑ := by
      rw [Real.enorm_eq_ofReal_abs]
      rfl
    _ ≤ ∫⁻ x, ‖parameterizedCompactSlice k w x‖ₑ ∂(π : Measure X) :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, U.indicator (fun _ ↦ ENNReal.ofReal ‖k.toBoundedContinuousFunction‖) x
        ∂(π : Measure X) := lintegral_mono hb
    _ = _ := by rw [lintegral_indicator hU]; simp

/-- A nonnegative scalar cutoff equal to one on the projected kernel support
controls every parameter slice using its original joint norm. -/
theorem abs_parameterizedCompactReadout_le_cutoff (k : C_c(V × X, ℝ))
    (w : V) (π : LocalFiniteMeasure X) (φ : C_c(X, ℝ))
    (hφ : ∀ x, 0 ≤ φ x) (hφK : EqOn φ 1 (parameterizedCompactEdgeSupport k)) :
    |parameterizedCompactReadout k (w, π)| ≤
      ‖k.toBoundedContinuousFunction‖ * LocalFiniteMeasure.testIntegral π φ := by
  have hb (x : X) : |parameterizedCompactSlice k w x| ≤
      ‖k.toBoundedContinuousFunction‖ * φ x := by
    by_cases hx : x ∈ parameterizedCompactEdgeSupport k
    · have heq : φ x = 1 := hφK hx
      rw [heq, mul_one]
      simpa only [Real.norm_eq_abs, parameterizedCompactSlice_apply,
        CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply] using
          k.toBoundedContinuousFunction.norm_coe_le_norm (w, x)
    · rw [parameterizedCompactSlice_eq_zero_of_notMem k w hx, abs_zero]
      exact mul_nonneg (norm_nonneg _) (hφ x)
  change |∫ x, parameterizedCompactSlice k w x ∂(π : Measure X)| ≤ _
  calc
    _ ≤ ∫ x, |parameterizedCompactSlice k w x| ∂(π : Measure X) := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x ↦ parameterizedCompactSlice k w x)
    _ ≤ ∫ x, ‖k.toBoundedContinuousFunction‖ * φ x ∂(π : Measure X) :=
      integral_mono (parameterizedCompactSlice k w).integrable.abs
        (φ.integrable.const_mul _) hb
    _ = _ := integral_const_mul _ _

/-- Parameter and plan may vary along any common filter. The integral still
converges in the original vague topology with the actual compact kernel. -/
theorem tendsto_parameterizedCompactReadout (k : C_c(V × X, ℝ))
    {I : Type*} {l : Filter I} (w : I → V) (π : I → LocalFiniteMeasure X)
    (w₀ : V) (π₀ : LocalFiniteMeasure X)
    (hw : Tendsto w l (𝓝 w₀)) (hπ : Tendsto π l (𝓝 π₀)) :
    Tendsto (fun i ↦ parameterizedCompactReadout k (w i, π i)) l
      (𝓝 (parameterizedCompactReadout k (w₀, π₀))) := by
  let K := parameterizedCompactEdgeSupport k
  have hK : IsCompact K := isCompact_parameterizedCompactEdgeSupport k
  obtain ⟨φ, hφK, hφbounds⟩ := LocalFiniteMeasure.exists_compact_cutoff hK
  have hφnonneg (x : X) : 0 ≤ φ x := (hφbounds x).1
  let C := |LocalFiniteMeasure.testIntegral π₀ φ| + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hmass : ∀ᶠ i in l, LocalFiniteMeasure.testIntegral (π i) φ < C := by
    apply (tendsto_order.mp ((LocalFiniteMeasure.continuous_testIntegral φ).tendsto π₀ |>.comp hπ)).2
    dsimp only [C]
    linarith [le_abs_self (LocalFiniteMeasure.testIntegral π₀ φ)]
  have hcurry : Tendsto (fun i ↦ k.toContinuousMap.curry (w i)) l
      (𝓝 (k.toContinuousMap.curry w₀)) :=
    (k.toContinuousMap.curry.continuous.tendsto w₀).comp hw
  have hunif : TendstoUniformlyOn (fun i x ↦ k (w i, x)) (fun x ↦ k (w₀, x)) l K :=
    (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hcurry) K hK
  have herror : Tendsto (fun i ↦
      LocalFiniteMeasure.testIntegral (π i) (parameterizedCompactSlice k (w i)) -
        LocalFiniteMeasure.testIntegral (π i) (parameterizedCompactSlice k w₀)) l (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let η := ε / (2 * C)
    have hη : 0 < η := div_pos hε (mul_pos (by norm_num) hC)
    filter_upwards [hmass, (Metric.tendstoUniformlyOn_iff.mp hunif) η hη] with i hi hiu
    have hb (x : X) : |parameterizedCompactSlice k (w i) x -
        parameterizedCompactSlice k w₀ x| ≤ η * φ x := by
      by_cases hx : x ∈ K
      · have heq : φ x = 1 := hφK hx
        rw [heq, mul_one]
        exact le_of_lt (by simpa only [Real.dist_eq, abs_sub_comm, parameterizedCompactSlice_apply] using hiu x hx)
      · rw [parameterizedCompactSlice_eq_zero_of_notMem k (w i) hx,
          parameterizedCompactSlice_eq_zero_of_notMem k w₀ hx, sub_self, abs_zero]
        exact mul_nonneg hη.le (hφnonneg x)
    have hib : Integrable (fun x ↦ parameterizedCompactSlice k (w i) x -
        parameterizedCompactSlice k w₀ x) (π i : Measure X) :=
      (parameterizedCompactSlice k (w i)).integrable.sub
        (parameterizedCompactSlice k w₀).integrable
    have hnorm : |LocalFiniteMeasure.testIntegral (π i) (parameterizedCompactSlice k (w i)) -
        LocalFiniteMeasure.testIntegral (π i) (parameterizedCompactSlice k w₀)| ≤
          η * LocalFiniteMeasure.testIntegral (π i) φ := by
      change |(∫ x, parameterizedCompactSlice k (w i) x ∂(π i : Measure X)) -
        ∫ x, parameterizedCompactSlice k w₀ x ∂(π i : Measure X)| ≤ _
      rw [← integral_sub (parameterizedCompactSlice k (w i)).integrable
        (parameterizedCompactSlice k w₀).integrable]
      calc
        _ ≤ ∫ x, |parameterizedCompactSlice k (w i) x - parameterizedCompactSlice k w₀ x|
            ∂(π i : Measure X) := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (fun x ↦ parameterizedCompactSlice k (w i) x - parameterizedCompactSlice k w₀ x)
        _ ≤ ∫ x, η * φ x ∂(π i : Measure X) :=
          integral_mono hib.abs (φ.integrable.const_mul η) hb
        _ = _ := integral_const_mul _ _
    rw [Real.dist_eq, sub_zero]
    apply lt_of_le_of_lt hnorm
    have hmul : η * LocalFiniteMeasure.testIntegral (π i) φ < η * C :=
      mul_lt_mul_of_pos_left hi hη
    have hηC : η * C = ε / 2 := by dsimp only [η]; field_simp
    rw [hηC] at hmul
    linarith
  have hfixed := ((LocalFiniteMeasure.continuous_testIntegral
    (parameterizedCompactSlice k w₀)).tendsto π₀).comp hπ
  have hsum := herror.add hfixed
  simpa only [zero_add, sub_add_cancel, Function.comp_apply, parameterizedCompactReadout] using hsum

/-- Joint compact kernels integrate continuously in the actual parameter and
actual locally finite plan equipped with the compact-test vague topology. -/
theorem continuous_parameterizedCompactReadout (k : C_c(V × X, ℝ)) :
    Continuous (parameterizedCompactReadout k) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact tendsto_parameterizedCompactReadout k Prod.fst Prod.snd p.1 p.2
    continuous_fst.continuousAt continuous_snd.continuousAt

/-- Continuous parameter and plan observations give a continuous joint readout
on the original scene space. -/
theorem continuous_parameterizedCompactReadout_comp {Y : Type*} [TopologicalSpace Y]
    (k : C_c(V × X, ℝ)) (w : Y → V) (π : Y → LocalFiniteMeasure X)
    (hw : Continuous w) (hπ : Continuous π) :
    Continuous (fun y ↦ parameterizedCompactReadout k (w y, π y)) :=
  (continuous_parameterizedCompactReadout k).comp (hw.prodMk hπ)

end OTSelector.Reconstruction

end
end
