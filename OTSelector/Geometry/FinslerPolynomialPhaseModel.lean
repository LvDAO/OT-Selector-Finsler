import OTSelector.Geometry.Finsler.CovectorNormalization
import OTSelector.Geometry.FinslerParameterizedPhaseAction

/-!
# The actual normalized polynomial phase model

Both initial states use the supplied polynomial level section and the same inverse
Legendre branch, normalized to unit speed. The quadratic coefficient is the actual
phase-action Hessian applied to the actual label derivative of this pair of states.
-/

open Set Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

/-- A stationary action Hessian evaluated on the actual label differential of a
joint state map. The parameter and state spaces are kept explicit for reuse. -/
def stationaryLabelQuadratic
    {P Q Z W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : P × Z → ℝ) (g : Q × W → Z) (p : P) (q : Q) (z : Z) (w : W) : ℝ :=
  let d := fderiv ℝ g (q, 0) (0, w)
  (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) (p, z) (0, d) (0, d)

namespace ContinuousFinslerNorm


set_option backward.isDefEq.respectTransparency false

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The pair of unit-speed initial states for one polynomial jet and
two independent labels, using the original inverse Legendre branch. -/
def polynomialPhasePair (F : ContinuousFinslerNorm E M) (old : M)
    (eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)))
    (σ : ScalarSecondJet E × W → E)
    (q : ScalarSecondJet E × (W × W)) : (E × E) × (E × E) :=
  (F.covectorNormalization old eL (1 / 2)
    (σ (q.1, q.2.1), fderiv ℝ (scalarSecondJetPolynomial q.1) (σ (q.1, q.2.1))),
   F.covectorNormalization old eL (1 / 2)
    (σ (q.1, q.2.2), fderiv ℝ (scalarSecondJetPolynomial q.1) (σ (q.1, q.2.2))))

/-- The actual stationary Hessian pulled back by the actual label differential
of the normalized pair. No fitted or auxiliary quadratic coefficient is used. -/
def polynomialPhaseQuadratic (F : ContinuousFinslerNorm E M) (old : M)
    (Φ : (E × E) → ℝ → M)
    (eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)))
    (σ : ScalarSecondJet E × W → E)
    (j : ScalarSecondJet E) (t : ℝ × ℝ) (w : W × W) : ℝ :=
  let z := eL.symm (j.1, j.2.2.1)
  stationaryLabelQuadratic (F.parameterizedPhaseLengthAction old Φ)
    (F.polynomialPhasePair old eL σ) (j, t) j (z, z) w

namespace IsSmoothStronglyConvex

variable {F : ContinuousFinslerNorm E M}

/-- The legal domain of the normalized polynomial pair is open and C1. Only the
centers need be legal a priori; nearby independent labels are covered by openness. -/
theorem exists_open_polynomialPhasePair_domain
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    {O J : Set (ScalarSecondJet E)} {B : Set W}
    (hO : IsOpen O) (hB : IsOpen B) (h0B : (0 : W) ∈ B) (hJO : J ⊆ O)
    {σ : ScalarSecondJet E × W → E} (hσ : ContDiffOn ℝ 1 σ (O ×ˢ B))
    (hσ₀ : ∀ j ∈ O, σ (j, 0) = j.1)
    (hlegal : ∀ j ∈ J, (j.1, j.2.2.1) ∈ eL.target) :
    ∃ V : Set (ScalarSecondJet E × (W × W)), IsOpen V ∧
      (∀ j ∈ J, (j, (0 : W × W)) ∈ V) ∧
      ContDiffOn ℝ 1 (F.polynomialPhasePair old eL σ) V ∧
      ∀ q ∈ V,
        (q.1, q.2.1) ∈ O ×ˢ B ∧ (q.1, q.2.2) ∈ O ×ˢ B ∧
        (σ (q.1, q.2.1),
          fderiv ℝ (scalarSecondJetPolynomial q.1) (σ (q.1, q.2.1))) ∈ eL.target ∧
        (σ (q.1, q.2.2),
          fderiv ℝ (scalarSecondJetPolynomial q.1) (σ (q.1, q.2.2))) ∈ eL.target := by
  let U := O ×ˢ (B ×ˢ B)
  have hU : IsOpen U := hO.prod (hB.prod hB)
  let s₁ : ScalarSecondJet E × (W × W) → E := fun q ↦ σ (q.1, q.2.1)
  let s₂ : ScalarSecondJet E × (W × W) → E := fun q ↦ σ (q.1, q.2.2)
  have hs₁ : ContDiffOn ℝ 1 s₁ U :=
    hσ.comp (contDiffOn_fst.prodMk contDiffOn_snd.fst) (fun _ hq ↦ ⟨hq.1, hq.2.1⟩)
  have hs₂ : ContDiffOn ℝ 1 s₂ U :=
    hσ.comp (contDiffOn_fst.prodMk contDiffOn_snd.snd) (fun _ hq ↦ ⟨hq.1, hq.2.2⟩)
  let Q : ScalarSecondJet E × E → E →L[ℝ] ℝ :=
    fun q ↦ fderiv ℝ (scalarSecondJetPolynomial q.1) q.2
  have hQ : ContDiff ℝ 1 Q := by
    apply contDiff_iff_contDiffAt.mpr
    intro q
    exact (contDiffAt_fiberLegendre
      contDiff_scalarSecondJetPolynomial_joint.contDiffAt).of_le (by simp)
  let q₁ : ScalarSecondJet E × (W × W) → E × (E →L[ℝ] ℝ) :=
    fun q ↦ (s₁ q, Q (q.1, s₁ q))
  let q₂ : ScalarSecondJet E × (W × W) → E × (E →L[ℝ] ℝ) :=
    fun q ↦ (s₂ q, Q (q.1, s₂ q))
  have hq₁ : ContDiffOn ℝ 1 q₁ U :=
    hs₁.prodMk (hQ.comp_contDiffOn (contDiffOn_fst.prodMk hs₁))
  have hq₂ : ContDiffOn ℝ 1 q₂ U :=
    hs₂.prodMk (hQ.comp_contDiffOn (contDiffOn_fst.prodMk hs₂))
  let V := (U ∩ q₁ ⁻¹' eL.target) ∩ q₂ ⁻¹' eL.target
  have hV : IsOpen V :=
    (hq₂.continuousOn.mono inter_subset_left).isOpen_inter_preimage
      (hq₁.continuousOn.isOpen_inter_preimage hU eL.open_target) eL.open_target
  have hVU : V ⊆ U := fun _ hq ↦ hq.1.1
  have hc : (0 : ℝ) < 1 / 2 := by norm_num
  have hN := ((hF.covectorNormalization_spec old heL hsource hInv hc).2.1).of_le
    (show (1 : ℕ∞) ≤ ∞ by simp)
  refine ⟨V, hV, ?_, ?_, ?_⟩
  · intro j hj
    have hs : σ (j, 0) = j.1 := hσ₀ j (hJO hj)
    have hq : (σ (j, 0), fderiv ℝ (scalarSecondJetPolynomial j) (σ (j, 0))) ∈
        eL.target := by
      rw [hs, (hasFDerivAt_scalarSecondJetPolynomial_center j).fderiv]
      exact hlegal j hj
    exact ⟨⟨⟨hJO hj, h0B, h0B⟩, hq⟩, hq⟩
  · exact (hN.comp (hq₁.mono hVU) (fun _ hq ↦ hq.1.2)).prodMk
      (hN.comp (hq₂.mono hVU) (fun _ hq ↦ hq.2))
  · intro q hq
    exact ⟨⟨hq.1.1.1, hq.1.1.2.1⟩, ⟨hq.1.1.1, hq.1.1.2.2⟩, hq.1.2, hq.2⟩

end IsSmoothStronglyConvex
end ContinuousFinslerNorm
end OTSelector.Geometry
