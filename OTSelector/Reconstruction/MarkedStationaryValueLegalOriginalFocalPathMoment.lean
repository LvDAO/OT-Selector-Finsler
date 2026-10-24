import OTSelector.LinearAlgebra.Matrix.QuadraticMomentumBound
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryTightCut
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalFocalKinetic
import OTSelector.Reconstruction.OriginalCoefficientLocalization

/-!
# The original weighted stationary matching has finite mean displacement

The actual inverse-compliance marginal moments control the original full
transverse displacement. The conclusion needs no unweighted second moment and
allows the original coefficient to degenerate at null focal endpoints.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-- Completing the quadratic estimate with the actual compliance controls
absolute displacement in the fixed coordinate norm. -/
theorem norm_le_matrixQuadratic_add_inverse_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (v : ι → ℝ) :
    ‖v‖ ≤ matrixQuadratic A v + ‖A⁻¹‖ := by
  let _ := hA.isUnit.invertible
  have hinv : A⁻¹ *ᵥ (A *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  have hQ : 0 ≤ matrixQuadratic A v := by
    unfold matrixQuadratic
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simpa only [star_trivial] using hA.posSemidef.dotProduct_mulVec_nonneg v
  have henergy : (A *ᵥ v) ⬝ᵥ (A⁻¹ *ᵥ (A *ᵥ v)) = 2 * matrixQuadratic A v := by
    rw [hinv, dotProduct_comm]
    unfold matrixQuadratic
    ring
  have hdiag (i : ι) : (A⁻¹) i i ≤ ‖A⁻¹‖ := by
    let e : ι → ℝ := Pi.single i (1 : ℝ)
    have he : ‖e‖ = 1 := by simp only [e, Pi.norm_single, norm_one]
    have heval : ‖(A⁻¹) i i‖ ≤ ‖A⁻¹ *ᵥ e‖ := by
      have h := norm_le_pi_norm (A⁻¹ *ᵥ e) i
      simpa only [e, mulVec_single_one, col_apply] using h
    calc
      (A⁻¹) i i ≤ ‖(A⁻¹) i i‖ := le_abs_self _
      _ ≤ ‖A⁻¹ *ᵥ e‖ := heval
      _ ≤ ‖A⁻¹‖ * ‖e‖ := Matrix.linfty_opNorm_mulVec _ _
      _ = ‖A⁻¹‖ := by rw [he, mul_one]
  apply (pi_norm_le_iff_of_nonneg (add_nonneg hQ (norm_nonneg _))).mpr
  intro i
  have h := mulVec_component_sq_le_diag_quadratic hA.inv.posSemidef (A *ᵥ v) i
  rw [henergy, hinv] at h
  have hb : v i ^ 2 ≤ 2 * ‖A⁻¹‖ * matrixQuadratic A v := by
    calc
      _ ≤ (A⁻¹) i i * (2 * matrixQuadratic A v) := h
      _ ≤ ‖A⁻¹‖ * (2 * matrixQuadratic A v) :=
        mul_le_mul_of_nonneg_right (hdiag i) (by positivity)
      _ = _ := by ring
  rw [Real.norm_eq_abs]
  nlinarith [sq_abs (v i), abs_nonneg (v i), norm_nonneg (A⁻¹),
    sq_nonneg (matrixQuadratic A v), sq_nonneg ‖A⁻¹‖]

/-- Each real diagonal entry is bounded by the original fixed operator norm. -/
theorem diagonal_le_linfty_operator_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (i : ι) : A i i ≤ ‖A‖ := by
  let e : ι → ℝ := Pi.single i (1 : ℝ)
  have he : ‖e‖ = 1 := by simp only [e, Pi.norm_single, norm_one]
  have heval : ‖A i i‖ ≤ ‖A *ᵥ e‖ := by
    have h := norm_le_pi_norm (A *ᵥ e) i
    simpa only [e, mulVec_single_one, col_apply] using h
  calc
    A i i ≤ ‖A i i‖ := le_abs_self _
    _ ≤ ‖A *ᵥ e‖ := heval
    _ ≤ ‖A‖ * ‖e‖ := Matrix.linfty_opNorm_mulVec _ _
    _ = ‖A‖ := by rw [he, mul_one]

/-- The actual trace is bounded in the same fixed matrix operator norm. -/
theorem trace_le_card_mul_linfty_operator_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : A.trace ≤ (Fintype.card ι : ℝ) * ‖A‖ := by
  calc
    A.trace ≤ ∑ i : ι, ‖A‖ :=
      Finset.sum_le_sum (fun i _ ↦ diagonal_le_linfty_operator_norm A i)
    _ = _ := by simp

/-- A positive semidefinite matrix bounds the speed of its compliance path
by its quadratic energy and half of its trace. -/
theorem norm_mulVec_le_matrixQuadratic_add_half_trace
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (v : ι → ℝ) :
    ‖A *ᵥ v‖ ≤ matrixQuadratic A v + (1 / 2 : ℝ) * A.trace := by
  have hQ : 0 ≤ matrixQuadratic A v := by
    unfold matrixQuadratic
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg v
  have ht : 0 ≤ A.trace := Finset.sum_nonneg (fun _ _ ↦ hA.diag_nonneg)
  apply (pi_norm_le_iff_of_nonneg (add_nonneg hQ (by positivity))).mpr
  intro i
  let e : ι → ℝ := Pi.single i (1 : ℝ)
  have hee : e ⬝ᵥ (A *ᵥ e) = A i i := by simp [e, mulVec_single]
  have hev : e ⬝ᵥ (A *ᵥ v) = (A *ᵥ v) i := by simp [e]
  have hve : v ⬝ᵥ (A *ᵥ e) = (A *ᵥ v) i := by
    have hsym (j : ι) : A j i = A i j := by simpa using hA.isHermitian.apply i j
    change v ⬝ᵥ (A *ᵥ Pi.single i (1 : ℝ)) = (A *ᵥ v) i
    rw [mulVec_single_one]
    change (∑ j, v j * A j i) = ∑ j, A i j * v j
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j, mul_comm]
  have hp := hA.dotProduct_mulVec_nonneg (v + e)
  have hm := hA.dotProduct_mulVec_nonneg (v - e)
  simp only [star_trivial, mulVec_add, mulVec_sub, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub, hee, hev, hve] at hp hm
  have hd : A i i ≤ A.trace :=
    Finset.single_le_sum (f := fun j ↦ A j j) (fun _ _ ↦ hA.diag_nonneg) (Finset.mem_univ i)
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  dsimp [matrixQuadratic]
  constructor <;> linarith

/-- The literal integral path of a continuous positive compliance has length
controlled by the same integrated quadratic energy and trace. -/
theorem intervalIntegral_norm_mulVec_le_quadratic_add_half_trace
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℝ → Matrix ι ι ℝ}
    {a b : ℝ} (hab : a ≤ b) (hK : ContinuousOn K (Icc a b))
    (hpos : ∀ t ∈ Icc a b, (K t).PosSemidef) (v : ι → ℝ) :
    (∫ t in a..b, ‖K t *ᵥ v‖) ≤ matrixQuadratic (∫ t in a..b, K t) v +
      (1 / 2 : ℝ) * (∫ t in a..b, K t).trace := by
  let L : Matrix ι ι ℝ →ₗ[ℝ] ℝ := {
    toFun := fun A ↦ matrixQuadratic A v + (1 / 2 : ℝ) * A.trace
    map_add' := fun A B ↦ by
      simp only [matrixQuadratic, add_mulVec, dotProduct_add, trace_add]
      ring
    map_smul' := fun c A ↦ by
      simp only [matrixQuadratic, smul_mulVec, dotProduct_smul, trace_smul,
        smul_eq_mul, RingHom.id_apply]
      ring }
  let Lc := L.toContinuousLinearMap
  have hKi : IntervalIntegrable K volume a b := by
    exact (show ContinuousOn K (uIcc a b) by simpa only [uIcc_of_le hab] using hK).intervalIntegrable
  have hn : Continuous (fun A : Matrix ι ι ℝ ↦ ‖A *ᵥ v‖) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  have hni : IntervalIntegrable (fun t ↦ ‖K t *ᵥ v‖) volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab, Function.comp_def] using hn.comp_continuousOn hK
  have hLi : IntervalIntegrable (fun t ↦ Lc (K t)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab, Function.comp_def] using Lc.continuous.comp_continuousOn hK
  calc
    _ ≤ ∫ t in a..b, Lc (K t) := intervalIntegral.integral_mono_on hab hni hLi
      (fun t ht ↦ norm_mulVec_le_matrixQuadratic_add_half_trace (hpos t ht) v)
    _ = Lc (∫ t in a..b, K t) := Lc.intervalIntegral_comp_comm hKi
    _ = _ := rfl

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
/-- Absolute length of the actual original compliance path between the two
original clock endpoints, retaining the full original transverse displacement. -/
def originalSeedPairPathLength (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) : ℝ :=
  ∫ t in (m.1.1 - S.level)..(m.1.2 - S.level),
    ‖originalSeedKernel S w t *ᵥ (originalSeedPairCoefficient S w m.1 *ᵥ m.2)‖

/-- The genuine original compliance path length is a measurable readout of
both original clocks and the complete displacement. -/
theorem measurable_originalSeedPairPathLength (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex) {w : S.covector.ker} (hw : w ∈ S.labels) :
    Measurable (originalSeedPairPathLength S w) := by
  have hK : Measurable (originalSeedKernel S w) := by
    have h := (S.measurable_familyLabelKernel hF (Module.finBasis ℝ S.covector.ker)).comp
      ((measurable_const : Measurable (fun _ : ℝ ↦ (⟨w, hw⟩ : S.labels))).prodMk measurable_id)
    change Measurable (fun t : ℝ ↦ originalSeedKernel S w t)
    simpa only [originalSeedKernel, Function.comp_def, id_eq] using h
  have hmul : Continuous (fun p :
      Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ ×
        (Fin (finrank ℝ S.covector.ker) → ℝ) ↦ p.1 *ᵥ p.2) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  have hp := hmul.measurable.comp
    (((measurable_originalSeedPairCoefficient S hF hw).comp measurable_fst).prodMk measurable_snd)
  have hspeed : StronglyMeasurable (fun p :
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      ‖originalSeedKernel S w p.2 *ᵥ (originalSeedPairCoefficient S w p.1.1 *ᵥ p.1.2)‖) :=
    (hmul.measurable.comp ((hK.comp measurable_snd).prodMk (hp.comp measurable_fst))).norm.stronglyMeasurable
  change Measurable (fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
    ∫ t in (m.1.1 - S.level)..(m.1.2 - S.level),
      ‖originalSeedKernel S w t *ᵥ (originalSeedPairCoefficient S w m.1 *ᵥ m.2)‖)
  exact (stronglyMeasurable_intervalIntegral_with_endpoints hspeed
    (measurable_fst.fst.sub_const (S.level : ℝ))
    (measurable_fst.snd.sub_const (S.level : ℝ))).measurable

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- On every actual legal interior pair, the absolute length of the true
compliance path is paid by the same kinetic energy and actual compliance norm. -/
theorem originalSeedPairPathLength_le_original_energy_add_inverse_norm
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {a b : ℝ} (ha : a - S.level ∈ Ioo D.lo D.hi)
    (hb : b - S.level ∈ Ioo D.lo D.hi) (hab : a < b)
    (v : Fin (finrank ℝ S.covector.ker) → ℝ) :
    originalSeedPairPathLength S w ((a, b), v) ≤
      matrixQuadratic (originalSeedPairCoefficient S w (a, b)) v +
        (1 / 2 : ℝ) * (finrank ℝ S.covector.ker : ℝ) *
          ‖(originalSeedPairCoefficient S w (a, b))⁻¹‖ := by
  let A := originalSeedPairCoefficient S w (a, b)
  let C := ∫ t in (a - S.level)..(b - S.level), originalSeedKernel S w t
  have hpos := D.pair_compliance_posDef hF hw ha hb hab
  let _ := hpos.2.isUnit.invertible
  have hC : C = A⁻¹ := (D.inverse_pair_coefficient_eq hF hw ha hb hab).symm
  have hCv : C *ᵥ (A *ᵥ v) = v := by
    rw [hC, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  have hquad : matrixQuadratic C (A *ᵥ v) = matrixQuadratic A v := by
    unfold matrixQuadratic
    rw [hCv, dotProduct_comm]
  have hsub : Icc (a - S.level) (b - S.level) ⊆ Ioo D.lo D.hi :=
    Icc_subset_Ioo ha.1 hb.2
  have hK := D.original_kernel_regular hF hw
  have hlength := intervalIntegral_norm_mulVec_le_quadratic_add_half_trace
    (sub_le_sub_right hab.le _) (hK.1.mono hsub)
    (fun t ht ↦ (hK.2 t (hsub ht)).posSemidef) (A *ᵥ v)
  change originalSeedPairPathLength S w ((a, b), v) ≤ _ at hlength
  calc
    _ ≤ matrixQuadratic C (A *ᵥ v) + (1 / 2 : ℝ) * C.trace := hlength
    _ ≤ matrixQuadratic C (A *ᵥ v) +
        (1 / 2 : ℝ) * ((finrank ℝ S.covector.ker : ℝ) * ‖C‖) := by
      gcongr
      simpa only [Fintype.card_fin] using trace_le_card_mul_linfty_operator_norm C
    _ = _ := by rw [hquad, hC]; ring

/-- Original marginal compliance moments and the genuine weighted Palm energy
produce the full absolute displacement first moment on the unchanged matching. -/
theorem integrable_displacement_of_original_weighted_stationary
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    Integrable (fun m ↦ m.2) (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ∧
      Integrable (fun m ↦ ‖m.2‖) (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) := by
  let η := legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  let π : Measure (ℝ × ℝ) := η.map Prod.fst
  have hπ : Vlasov.IsCoupling π μ ν := by
    constructor
    · rw [show π.map Prod.fst = η.map (fun m ↦ m.1.1) from
        Measure.map_map measurable_fst measurable_fst]
      exact Q.source_clock
    · rw [show π.map Prod.snd = η.map (fun m ↦ m.1.2) from
        Measure.map_map measurable_snd measurable_fst]
      exact Q.target_clock
  have hforward : ∀ᵐ p ∂π, p.1 < p.2 := by
    exact (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_lt measurable_fst measurable_snd)).mpr Q.ae_palm_forward
  have hroot : (D.lo + D.hi) / 2 ∈ Ioo D.lo D.hi :=
    ⟨by linarith [D.support.lt], by linarith [D.support.lt]⟩
  have hC := D.integrable_inverse_pair_coefficient hF hw hroot hπ hforward
  have hmeasC := (measurable_real_matrix_inverse.comp
    (measurable_originalSeedPairCoefficient S hF hw)).norm
  have hCI : Integrable (fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
      ‖(originalSeedPairCoefficient S w m.1)⁻¹‖) η := by
    exact (integrable_map_measure hmeasC.aestronglyMeasurable measurable_fst.aemeasurable).mp hC.norm
  have ha : ∀ᵐ m ∂η, m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.1 ∈ μ.support := by
    have h : ∀ᵐ a ∂η.map (fun m ↦ m.1.1),
        a - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ a ∈ μ.support := by
      rw [Q.source_clock]
      exact D.support.source.ae_open.and μ.support_mem_ae
    exact ae_of_ae_map (μ := η) (f := fun m ↦ m.1.1)
      (p := fun a : ℝ ↦ a - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ a ∈ μ.support)
      measurable_fst.fst.aemeasurable h
  have hb : ∀ᵐ m ∂η, m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.2 ∈ ν.support := by
    have h : ∀ᵐ b ∂η.map (fun m ↦ m.1.2),
        b - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ b ∈ ν.support := by
      rw [Q.target_clock]
      exact D.support.target.ae_open.and ν.support_mem_ae
    exact ae_of_ae_map (μ := η) (f := fun m ↦ m.1.2)
      (p := fun b : ℝ ↦ b - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ b ∈ ν.support)
      measurable_fst.snd.aemeasurable h
  have hbound : ∀ᵐ m ∂η, ‖m.2‖ ≤ D.originalFocalKinetic gap m.1.1 m.1.2 m.2 +
      ‖(originalSeedPairCoefficient S w m.1)⁻¹‖ := by
    filter_upwards [ha, hb, Q.ae_palm_forward] with m ha hb hf
    rw [D.originalFocalKinetic_eq_of_original_support hbounds ha hb hf]
    exact norm_le_matrixQuadratic_add_inverse_norm
      (D.pair_compliance_posDef hF hw ha.1 hb.1 hf).2 m.2
  have hI : Integrable (fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦ m.2) η := by
    exact (Q.kinetic_integrable.add hCI).mono' measurable_snd.aestronglyMeasurable hbound
  exact ⟨hI, hI.norm⟩

/-- The actual original compliance path has finite mean absolute length under
the same genuine weighted stationary matching. Original marginal moment data
produce the bound; no displacement second moment is assumed. -/
theorem integrable_pathLength_of_original_weighted_stationary
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    Integrable (originalSeedPairPathLength S w)
      (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) := by
  let η := legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  let π : Measure (ℝ × ℝ) := η.map Prod.fst
  have hπ : Vlasov.IsCoupling π μ ν := by
    constructor
    · rw [show π.map Prod.fst = η.map (fun m ↦ m.1.1) from
        Measure.map_map measurable_fst measurable_fst]
      exact Q.source_clock
    · rw [show π.map Prod.snd = η.map (fun m ↦ m.1.2) from
        Measure.map_map measurable_snd measurable_fst]
      exact Q.target_clock
  have hforward : ∀ᵐ p ∂π, p.1 < p.2 := by
    exact (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_lt measurable_fst measurable_snd)).mpr Q.ae_palm_forward
  have hroot : (D.lo + D.hi) / 2 ∈ Ioo D.lo D.hi :=
    ⟨by linarith [D.support.lt], by linarith [D.support.lt]⟩
  have hC := D.integrable_inverse_pair_coefficient hF hw hroot hπ hforward
  have hmeasC := (measurable_real_matrix_inverse.comp
    (measurable_originalSeedPairCoefficient S hF hw)).norm
  have hCI : Integrable (fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
      ‖(originalSeedPairCoefficient S w m.1)⁻¹‖) η := by
    exact (integrable_map_measure hmeasC.aestronglyMeasurable measurable_fst.aemeasurable).mp hC.norm
  have ha : ∀ᵐ m ∂η, m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.1 ∈ μ.support := by
    have h : ∀ᵐ a ∂η.map (fun m ↦ m.1.1),
        a - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ a ∈ μ.support := by
      rw [Q.source_clock]
      exact D.support.source.ae_open.and μ.support_mem_ae
    exact ae_of_ae_map (μ := η) (f := fun m ↦ m.1.1)
      (p := fun a : ℝ ↦ a - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ a ∈ μ.support)
      measurable_fst.fst.aemeasurable h
  have hb : ∀ᵐ m ∂η, m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.2 ∈ ν.support := by
    have h : ∀ᵐ b ∂η.map (fun m ↦ m.1.2),
        b - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ b ∈ ν.support := by
      rw [Q.target_clock]
      exact D.support.target.ae_open.and ν.support_mem_ae
    exact ae_of_ae_map (μ := η) (f := fun m ↦ m.1.2)
      (p := fun b : ℝ ↦ b - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ b ∈ ν.support)
      measurable_fst.snd.aemeasurable h
  have hbound : ∀ᵐ m ∂η, ‖originalSeedPairPathLength S w m‖ ≤
      D.originalFocalKinetic gap m.1.1 m.1.2 m.2 +
        ((1 / 2 : ℝ) * (finrank ℝ S.covector.ker : ℝ)) *
          ‖(originalSeedPairCoefficient S w m.1)⁻¹‖ := by
    filter_upwards [ha, hb, Q.ae_palm_forward] with m ha hb hf
    have hnn : 0 ≤ originalSeedPairPathLength S w m := by
      apply intervalIntegral.integral_nonneg_of_forall (sub_le_sub_right hf.le _)
      intro t
      exact norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn,
      D.originalFocalKinetic_eq_of_original_support hbounds ha hb hf]
    simpa only [mul_assoc] using D.originalSeedPairPathLength_le_original_energy_add_inverse_norm
      hF hw ha.1 hb.1 hf m.2
  exact (Q.kinetic_integrable.add (hCI.const_mul
    ((1 / 2 : ℝ) * (finrank ℝ S.covector.ker : ℝ)))).mono'
      (measurable_originalSeedPairPathLength S hF hw).aestronglyMeasurable hbound

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
