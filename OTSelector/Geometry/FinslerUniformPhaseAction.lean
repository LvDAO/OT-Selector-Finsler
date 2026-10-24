import OTSelector.Geometry.FinslerParameterizedPhaseAction
import OTSelector.Analysis.Calculus.UniformParameterizedActionTransfer

/-!
# Uniform transfer of the original Finsler phase action

The parameters retain the actual second jet and both elapsed times. Uniform seed
control on the original allowed labels is transferred through the stationary action
on one compact parameter set. The resulting estimate uses the same distance cost.
-/

open Set Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

private theorem fderiv_parameter_direction_eq_zero
    {P Z : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {f : P × Z → ℝ} {p : P} {z : Z}
    (hf : DifferentiableAt ℝ f (p, z))
    (hs : HasFDerivAt (fun y ↦ f (p, y)) (0 : Z →L[ℝ] ℝ) z) (h : Z) :
    fderiv ℝ f (p, z) (0, h) = 0 := by
  have hi : HasFDerivAt (fun y : Z ↦ (p, y))
      ((0 : Z →L[ℝ] P).prod (ContinuousLinearMap.id ℝ Z)) z :=
    (hasFDerivAt_const p z).prodMk (hasFDerivAt_id z)
  have heq := (hf.hasFDerivAt.comp z hi).unique hs
  have hv := congrArg (fun L : Z →L[ℝ] ℝ ↦ L h) heq
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply] using hv

private theorem uniform_action_transfer_of_frozen_stationarity
    {P Z I T : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z]
    {f : P × Z → ℝ} {K : Set (P × Z)} (hK : IsCompact K)
    (hf : ∀ q ∈ K, ContDiffAt ℝ 3 f q)
    (hs : ∀ q ∈ K, HasFDerivAt (fun y ↦ f (q.1, y)) (0 : Z →L[ℝ] ℝ) q.2)
    (S : Set I) (z : I → P × Z) (hz : ∀ i ∈ S, z i ∈ K)
    (X Y : I → T → Z) (scale : T → ℝ) (hscale : ∀ t, 0 ≤ scale t)
    (allowed : I → T → Prop) {L R : ℝ} (hL : 0 ≤ L) (hR : 0 < R)
    (hsize : ∀ i ∈ S, ∀ t, scale t < R → allowed i t →
      ‖X i t - (z i).2‖ ≤ L * scale t ∧ ‖Y i t - (z i).2‖ ≤ L * scale t)
    (hmismatch : ∀ δ : ℝ, 0 < δ → ∃ r > 0, ∀ i ∈ S, ∀ t, scale t < r →
      allowed i t → ‖X i t - Y i t‖ ≤ δ * scale t)
    {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ i ∈ S, ∀ t, scale t < r → allowed i t →
      ‖f ((z i).1, X i t) - f ((z i).1, Y i t)‖ ≤ η * (scale t) ^ 2 := by
  exact uniform_parameterized_stationary_action_transfer_within hK hf
    (fun q hq h ↦ fderiv_parameter_direction_eq_zero
      ((hf q hq).differentiableAt (by norm_num)) (hs q hq) h)
    S z hz X Y scale hscale allowed hL hR hsize hmismatch hη

private theorem uniform_pair_action_transfer
    {P Z I W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : P × (Z × Z) → ℝ} {K : Set (P × (Z × Z))} (hK : IsCompact K)
    (hf : ∀ q ∈ K, ContDiffAt ℝ 3 f q)
    (hs : ∀ q ∈ K, HasFDerivAt (fun y ↦ f (q.1, y)) (0 : (Z × Z) →L[ℝ] ℝ) q.2)
    (S : Set I) (p : I → P) (c : I → Z) (hz : ∀ i ∈ S, (p i, (c i, c i)) ∈ K)
    (X Y : I → W → Z) (allowed : I → W → Prop) {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R)
    (hsize : ∀ i ∈ S, ∀ w, ‖w‖ < R → allowed i w →
      ‖X i w - c i‖ ≤ A * ‖w‖ ∧ ‖Y i w - c i‖ ≤ A * ‖w‖)
    (hmismatch : ∀ δ : ℝ, 0 < δ → ∃ r > 0, ∀ i ∈ S, ∀ w, ‖w‖ < r →
      allowed i w → ‖X i w - Y i w‖ ≤ δ * ‖w‖)
    {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ i ∈ S, ∀ w : W × W, ‖w‖ < r → allowed i w.1 → allowed i w.2 →
      ‖f (p i, (X i w.1, X i w.2)) - f (p i, (Y i w.1, Y i w.2))‖ ≤ η * ‖w‖ ^ 2 := by
  let z : I → P × (Z × Z) := fun i ↦ (p i, (c i, c i))
  let X' : I → W × W → Z × Z := fun i w ↦ (X i w.1, X i w.2)
  let Y' : I → W × W → Z × Z := fun i w ↦ (Y i w.1, Y i w.2)
  let valid : I → W × W → Prop := fun i w ↦ allowed i w.1 ∧ allowed i w.2
  have hsize' : ∀ i ∈ S, ∀ w : W × W, ‖w‖ < R → valid i w →
      ‖X' i w - (z i).2‖ ≤ A * ‖w‖ ∧ ‖Y' i w - (z i).2‖ ≤ A * ‖w‖ := by
    intro i hi w hw ha
    have hw₁ : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
    have hw₂ : ‖w.2‖ ≤ ‖w‖ := norm_snd_le w
    obtain ⟨hX₁, hY₁⟩ := hsize i hi w.1 (hw₁.trans_lt hw) ha.1
    obtain ⟨hX₂, hY₂⟩ := hsize i hi w.2 (hw₂.trans_lt hw) ha.2
    have hm₁ := mul_le_mul_of_nonneg_left hw₁ hA
    have hm₂ := mul_le_mul_of_nonneg_left hw₂ hA
    exact ⟨max_le (hX₁.trans hm₁) (hX₂.trans hm₂),
      max_le (hY₁.trans hm₁) (hY₂.trans hm₂)⟩
  have hmatch : ∀ δ : ℝ, 0 < δ → ∃ r > 0, ∀ i ∈ S, ∀ w : W × W, ‖w‖ < r →
      valid i w → ‖X' i w - Y' i w‖ ≤ δ * ‖w‖ := by
    intro δ hδ
    obtain ⟨r, hr, hb⟩ := hmismatch δ hδ
    refine ⟨r, hr, ?_⟩
    intro i hi w hw ha
    have hw₁ : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
    have hw₂ : ‖w.2‖ ≤ ‖w‖ := norm_snd_le w
    exact max_le ((hb i hi w.1 (hw₁.trans_lt hw) ha.1).trans
      (mul_le_mul_of_nonneg_left hw₁ hδ.le))
      ((hb i hi w.2 (hw₂.trans_lt hw) ha.2).trans
        (mul_le_mul_of_nonneg_left hw₂ hδ.le))
  obtain ⟨r, hr, hb⟩ := uniform_action_transfer_of_frozen_stationarity hK hf hs
    S z hz X' Y' (fun w ↦ ‖w‖) (fun _ ↦ norm_nonneg _) valid hA hR hsize' hmatch hη
  exact ⟨r, hr, fun i hi w hw ha hb' ↦ hb i hi w hw ⟨ha, hb'⟩⟩

private theorem uniform_phase_pair_action_transfer
    {E I W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : (ScalarSecondJet E × (ℝ × ℝ)) × ((E × E) × (E × E)) → ℝ}
    {K : Set ((ScalarSecondJet E × (ℝ × ℝ)) × ((E × E) × (E × E)))} (hK : IsCompact K)
    (hf : ∀ q ∈ K, ContDiffAt ℝ 3 f q)
    (hs : ∀ q ∈ K, HasFDerivAt (fun y ↦ f (q.1, y)) (0 : ((E × E) × (E × E)) →L[ℝ] ℝ) q.2)
    (S : Set I) (p : I → ScalarSecondJet E × (ℝ × ℝ)) (c : I → E × E)
    (hz : ∀ i ∈ S, (p i, (c i, c i)) ∈ K)
    (X Y : I → W → E × E) (allowed : I → W → Prop) {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R)
    (hsize : ∀ i ∈ S, ∀ w, ‖w‖ < R → allowed i w →
      ‖X i w - c i‖ ≤ A * ‖w‖ ∧ ‖Y i w - c i‖ ≤ A * ‖w‖)
    (hmismatch : ∀ δ : ℝ, 0 < δ → ∃ r > 0, ∀ i ∈ S, ∀ w, ‖w‖ < r →
      allowed i w → ‖X i w - Y i w‖ ≤ δ * ‖w‖)
    {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ i ∈ S, ∀ w : W × W, ‖w‖ < r → allowed i w.1 → allowed i w.2 →
      ‖f (p i, (X i w.1, X i w.2)) - f (p i, (Y i w.1, Y i w.2))‖ ≤ η * ‖w‖ ^ 2 := by
  have base := uniform_pair_action_transfer
    (P := ScalarSecondJet E × (ℝ × ℝ)) (Z := E × E)
    (I := I) (W := W) (f := f) (K := K) (A := A) (R := R) (η := η)
  have baseK := base hK
  have baseF := baseK hf
  have baseS := baseF hs
  exact baseS S p c hz X Y allowed hA hR hsize hmismatch hη

namespace ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Uniform first-order seed matching and common center displacement bounds give
second-order action matching on the original allowed labels. The geometric action
regularity and stationarity are explicit inputs supplied by calibrated tubes. -/
theorem uniform_phaseLengthAction_transfer_of_original_seeds
    (F : ContinuousFinslerNorm E M) (old : M) (Φ : (E × E) → ℝ → M)
    {G : E → ℝ} (hG : ContDiff ℝ 1 G)
    {K : Set E} (hK : IsCompact K)
    (hHess : ContinuousOn (fderiv ℝ (fderiv ℝ G)) K)
    {T : Set (ℝ × ℝ)} (hT : IsCompact T)
    (eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)))
    (hlegal : ∀ x ∈ K, (x, fderiv ℝ G x) ∈ eL.target)
    (hC3 : ∀ x ∈ K, ∀ t ∈ T,
      ContDiffAt ℝ 3 (F.parameterizedPhaseLengthAction old Φ)
        (((x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x), t),
          (eL.symm (x, fderiv ℝ G x), eL.symm (x, fderiv ℝ G x))))
    (hstationary : ∀ x ∈ K, ∀ t ∈ T,
      HasFDerivAt (F.phaseLengthAction old Φ
        (scalarSecondJetPolynomial (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x))
        t.1 t.2) (0 : ((E × E) × (E × E)) →L[ℝ] ℝ)
        (eL.symm (x, fderiv ℝ G x), eL.symm (x, fderiv ℝ G x)))
    (X Y : E → W → E × E) (allowed : E → W → Prop)
    {A : ℝ≥0} {R : ℝ} (hR : 0 < R)
    (hsize : ∀ x ∈ K, ∀ w, ‖w‖ < R → allowed x w →
      ‖X x w - eL.symm (x, fderiv ℝ G x)‖ ≤ (A : ℝ) * ‖w‖ ∧
      ‖Y x w - eL.symm (x, fderiv ℝ G x)‖ ≤ (A : ℝ) * ‖w‖)
    (hmismatch : ∀ δ : ℝ, 0 < δ → ∃ r > 0, ∀ x ∈ K, ∀ w, ‖w‖ < r →
      allowed x w → ‖X x w - Y x w‖ ≤ δ * ‖w‖)
    {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ x ∈ K, ∀ t ∈ T, ∀ w : W × W, ‖w‖ < r →
      allowed x w.1 → allowed x w.2 →
      let Q := scalarSecondJetPolynomial
        (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
      ‖F.phaseLengthAction old Φ Q t.1 t.2 (X x w.1, X x w.2) -
        F.phaseLengthAction old Φ Q t.1 t.2 (Y x w.1, Y x w.2)‖ ≤ η * ‖w‖ ^ 2 := by
  let z : E × (ℝ × ℝ) →
      (ScalarSecondJet E × (ℝ × ℝ)) × ((E × E) × (E × E)) := fun q ↦
    (((q.1, G q.1, fderiv ℝ G q.1, fderiv ℝ (fderiv ℝ G) q.1), q.2),
      (eL.symm (q.1, fderiv ℝ G q.1), eL.symm (q.1, fderiv ℝ G q.1)))
  let S := K ×ˢ T
  have hzK : IsCompact (z '' S) :=
    isCompact_original_phaseAction_parameters hG hK hHess hT eL hlegal
  have hf : ∀ q ∈ z '' S, ContDiffAt ℝ 3 (F.parameterizedPhaseLengthAction old Φ) q := by
    rintro q ⟨i, hi, rfl⟩
    exact hC3 i.1 hi.1 i.2 hi.2
  have hs : ∀ q ∈ z '' S,
      HasFDerivAt (fun y ↦ F.parameterizedPhaseLengthAction old Φ (q.1, y))
        (0 : ((E × E) × (E × E)) →L[ℝ] ℝ) q.2 := by
    rintro q ⟨i, hi, rfl⟩
    exact hstationary i.1 hi.1 i.2 hi.2
  have hbase := uniform_phase_pair_action_transfer (E := E)
    (I := E × (ℝ × ℝ)) (W := W)
    (f := F.parameterizedPhaseLengthAction old Φ) (K := z '' S)
    (A := (A : ℝ)) (R := R) (η := η) hzK hf hs
  let p : E × (ℝ × ℝ) → ScalarSecondJet E × (ℝ × ℝ) := fun i ↦ (z i).1
  let c : E × (ℝ × ℝ) → E × E := fun i ↦ eL.symm (i.1, fderiv ℝ G i.1)
  have hcenter : ∀ i ∈ S, (p i, (c i, c i)) ∈ z '' S := by
    intro i hi
    change z i ∈ z '' S
    exact mem_image_of_mem z hi
  let X' : E × (ℝ × ℝ) → W → E × E := fun i ↦ X i.1
  let Y' : E × (ℝ × ℝ) → W → E × E := fun i ↦ Y i.1
  let valid : E × (ℝ × ℝ) → W → Prop := fun i ↦ allowed i.1
  have hsize' : ∀ i ∈ S, ∀ w, ‖w‖ < R → valid i w →
      ‖X' i w - c i‖ ≤ (A : ℝ) * ‖w‖ ∧ ‖Y' i w - c i‖ ≤ (A : ℝ) * ‖w‖ :=
    fun i hi w hw ha ↦ hsize i.1 hi.1 w hw ha
  have hmis' : ∀ δ : ℝ, 0 < δ → ∃ r > 0, ∀ i ∈ S, ∀ w, ‖w‖ < r →
      valid i w → ‖X' i w - Y' i w‖ ≤ δ * ‖w‖ := by
    intro δ hδ
    obtain ⟨r, hr, hb⟩ := hmismatch δ hδ
    exact ⟨r, hr, fun i hi w hw ha ↦ hb i.1 hi.1 w hw ha⟩
  obtain ⟨r, hr, hb⟩ := hbase S p c hcenter X' Y' valid A.coe_nonneg hR hsize' hmis' hη
  exact ⟨r, hr, fun x hx t ht w hw ha hb' ↦ hb (x, t) ⟨hx, ht⟩ w hw ha hb'⟩

end ContinuousFinslerNorm
end OTSelector.Geometry
