import OTSelector.Analysis.Calculus.VariationDerivatives
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.NonautonomousVariation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.NonautonomousVariation`; the selected original proof blocks follow. -/
section

/-!
Conditions: A C2 parameter/time family solves the stated time-dependent field, whose actual state derivative exists at the relevant points.

Objects: The actual parameter differential satisfies the nonautonomous linearized equation.

Proof detail: Differentiate the ODE in parameters and interchange the actual mixed derivatives of the family.

Sources: Gerald Teschl, Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56); Jiří Lebl, Section 8.6, Proposition 8.6.2, pp. 60–61 (equality of mixed second partial derivatives) (https://www.jirka.org/ra/realanal2.pdf#page=60).
Relation: Parameter-variation generalization that requires no derivative of the field in time beyond the actual signature.
-/

/-!
# Actual parameter variations of nonautonomous solution families

A jointly C2 family satisfying its original time-slice ODE has parameter derivatives
satisfying the actual state-linearized equation. The proof restricts each parameter
direction to an affine scalar variation and uses the proved C2 mixed-derivative theorem.
No interchange identity or variational equation is assumed. The vector field only needs
state differentiability at the point in question; no time derivative of it is required.
-/

open Set Filter
open scoped Topology ContDiff

namespace OTSelector.Geometry

variable {W E : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual parameter differential equals the joint differential on parameter directions. -/
theorem parameterVariation_eq_fderiv {Ψ : W × ℝ → E} {w₀ : W} {t : ℝ}
    (hΨ : DifferentiableAt ℝ Ψ (w₀, t)) (ξ : W) :
    fderiv ℝ (fun w ↦ Ψ (w, t)) w₀ ξ = fderiv ℝ Ψ (w₀, t) (ξ, 0) := by
  exact congrArg (fun D : W →L[ℝ] E ↦ D ξ)
    (hΨ.hasFDerivAt.comp w₀ (hasFDerivAt_prodMk_left w₀ t)).fderiv

/-- Actual parameter variations of a jointly C2 family are C1 on the open time slice. -/
theorem contDiffOn_parameterVariation {Ψ : W × ℝ → E} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : ContDiffOn ℝ 2 Ψ D) (w₀ ξ : W) :
    ContDiffOn ℝ 1 (fun t ↦ fderiv ℝ (fun w ↦ Ψ (w, t)) w₀ ξ) {t | (w₀, t) ∈ D} := by
  have h := (hΨ.fderiv_of_isOpen hD (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).clm_apply
    (contDiffOn_const (c := (ξ, 0)))
  have hc := h.comp (contDiffOn_const.prodMk contDiffOn_id)
    (show MapsTo (fun t : ℝ ↦ (w₀, t)) {t | (w₀, t) ∈ D} D from fun _ ht ↦ ht)
  apply hc.congr
  intro t ht
  exact parameterVariation_eq_fderiv
    ((hΨ.contDiffAt (hD.mem_nhds ht)).differentiableAt (by norm_num)) ξ

private theorem affine_parameter_hasDerivAt {Ψ : W × ℝ → E} {w₀ : W} {t : ℝ}
    (hΨ : DifferentiableAt ℝ Ψ (w₀, t)) (ξ : W) :
    HasDerivAt (fun r : ℝ ↦ Ψ (w₀ + r • ξ, t))
      (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀ ξ) 0 := by
  have hΨ' : HasFDerivAt Ψ (fderiv ℝ Ψ (w₀, t)) (w₀ + (0 : ℝ) • ξ, t) := by
    simpa only [zero_smul, add_zero] using hΨ.hasFDerivAt
  have hd := hΨ'.comp_hasDerivAt (0 : ℝ)
    (((hasDerivAt_const (0 : ℝ) w₀).add ((hasDerivAt_id (0 : ℝ)).smul_const ξ)).prodMk
      (hasDerivAt_const (0 : ℝ) t))
  simpa only [zero_smul, add_zero, zero_add, one_smul, Function.comp_def, Pi.add_apply, id_eq,
    parameterVariation_eq_fderiv hΨ ξ] using hd

/-- The actual parameter derivative of a genuine C2 solution family solves the true
nonautonomous state-linearized equation. Mixed equality follows from actual C2 symmetry. -/
theorem hasDerivAt_parameterVariation_of_nonautonomousODE
    {Ψ : W × ℝ → E} {X : ℝ → E → E} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : ContDiffOn ℝ 2 Ψ D)
    (hODE : ∀ z ∈ D, HasDerivAt (fun s ↦ Ψ (z.1, s)) (X z.2 (Ψ z)) z.2)
    {w₀ : W} {t : ℝ} (hz : (w₀, t) ∈ D)
    (hX : DifferentiableAt ℝ (X t) (Ψ (w₀, t))) (ξ : W) :
    HasDerivAt (fun s ↦ fderiv ℝ (fun w ↦ Ψ (w, s)) w₀ ξ)
      (fderiv ℝ (X t) (Ψ (w₀, t)) (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀ ξ)) t := by
  let σ : ℝ × ℝ → E := fun z ↦ Ψ (w₀ + z.1 • ξ, z.2)
  let D' : Set (ℝ × ℝ) := (fun z : ℝ × ℝ ↦ (w₀ + z.1 • ξ, z.2)) ⁻¹' D
  have hA : ContDiff ℝ 2 (fun z : ℝ × ℝ ↦ (w₀ + z.1 • ξ, z.2)) :=
    (contDiff_const.add (contDiff_fst.smul contDiff_const)).prodMk contDiff_snd
  have hD' : IsOpen D' := hD.preimage hA.continuous
  have hσ : ContDiffOn ℝ 2 σ D' := hΨ.comp hA.contDiffOn (fun _ hz ↦ hz)
  have hz' : (0, t) ∈ D' := by simpa only [D', mem_preimage, zero_smul, add_zero] using hz
  have hmixed := hasDerivAt_variationVelocity hD' hσ hz'
  have hΨa := (hΨ.contDiffAt (hD.mem_nhds hz)).differentiableAt (by norm_num)
  have hdir := affine_parameter_hasDerivAt hΨa ξ
  have hX' : HasFDerivAt (X t) (fderiv ℝ (X t) (Ψ (w₀, t)))
      (Ψ (w₀ + (0 : ℝ) • ξ, t)) := by
    simpa only [zero_smul, add_zero] using hX.hasFDerivAt
  have hright := hX'.comp_hasDerivAt (0 : ℝ) hdir
  have hn : ∀ᶠ r : ℝ in 𝓝 0, (w₀ + r • ξ, t) ∈ D := by
    have hc : ContinuousAt (fun r : ℝ ↦ (w₀ + r • ξ, t)) 0 :=
      (continuousAt_const.add (continuousAt_id.smul continuousAt_const)).prodMk continuousAt_const
    have hh := hc.preimage_mem_nhds (by simpa using hD.mem_nhds hz)
    exact hh
  have heq : (fun r ↦ variationVelocity σ (r, t)) =ᶠ[𝓝 0]
      (fun r ↦ X t (Ψ (w₀ + r • ξ, t))) := by
    filter_upwards [hn] with r hr
    exact (hODE (w₀ + r • ξ, t) hr).deriv
  have hvalue := hmixed.unique (hright.congr_of_eventuallyEq heq)
  have htime := (contDiffOn_variationField hD' hσ 0).contDiffAt
    ((hD'.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz')
  have hdtime := (htime.differentiableAt one_ne_zero).hasDerivAt
  rw [hvalue] at hdtime
  apply hdtime.congr_of_eventuallyEq
  have hnear : ∀ᶠ s in 𝓝 t, (w₀, s) ∈ D :=
    (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds (hD.mem_nhds hz)
  filter_upwards [hnear] with s hs
  exact (affine_parameter_hasDerivAt
    ((hΨ.contDiffAt (hD.mem_nhds hs)).differentiableAt (by norm_num)) ξ).deriv.symm

end OTSelector.Geometry

end
