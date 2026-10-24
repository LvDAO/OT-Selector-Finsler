import OTSelector.Geometry.Finsler.Jacobi.Pairing
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.RegraphedRank.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.RegraphedRank`; the selected original proof blocks follow. -/
section

/-!
Conditions: Original phase injectivity, covector normality, nonzero transverse velocity pairing, energy tangency and the actual reduced chain relation.

Objects: Injectivity of the reduced graph phase.

Proof detail: A zero reduced phase first forces the graph correction coefficient to vanish by normality, then the original phase vanishes and injectivity applies.

Sources: Ana Cannas da Silva, Homework 1, Symplectic Linear Algebra, p. 8; Section 2.2, pp. 9–10 (https://people.math.ethz.ch/~acannas/Papers/lsg.pdf#page=16); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15).
Relation: Local rank-transfer algebra for the actual reduced map; rank is not assumed for a substitute phase.
-/

/-!
# Kernel elimination for an actual regraphed phase derivative

This algebraic consumer takes the actual old and reduced derivative maps, together with
their chain-rule relation. Original phase injectivity, momentum normality and tangency
to the Hamiltonian energy level imply reduced phase injectivity. The geometric consumer
must derive the displayed relation and the energy identity from the same original family.
-/

noncomputable section
namespace OTSelector.Geometry

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- An injective normal energy-tangent phase derivative remains injective under the
true fixed-graph-time correction and positive-speed momentum normalization. -/
theorem injective_regraphed_phase_derivative
    {A : W →L[ℝ] ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ))}
    {R : W →L[ℝ] (V × (V →L[ℝ] ℝ))}
    {X : (ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)} {p : (ℝ × V) →L[ℝ] ℝ} {S : ℝ}
    (hA : Function.Injective A) (hc : X.1.1 ≠ 0) (hS : S ≠ 0) (hpv : p X.1 ≠ 0)
    (hnormal : ∀ ξ, p (A ξ).1 = 0)
    (henergy : ∀ ξ, canonicalPhasePairing X (A ξ) = 0)
    (hR : ∀ ξ,
      R ξ = (((A ξ).1 - ((A ξ).1.1 / X.1.1) • X.1).2,
        S⁻¹ • ((A ξ).2 - ((A ξ).1.1 / X.1.1) • X.2).comp
          (ContinuousLinearMap.inr ℝ ℝ V))) :
    Function.Injective R := by
  have hker (ξ : W) (hξ : R ξ = 0) : ξ = 0 := by
    let d := (A ξ).1.1 / X.1.1
    have hred := (hR ξ).symm.trans hξ
    have hx₂ : ((A ξ).1 - d • X.1).2 = 0 := congrArg Prod.fst hred
    have hx₁ : ((A ξ).1 - d • X.1).1 = 0 := by
      change (A ξ).1.1 - ((A ξ).1.1 / X.1.1) * X.1.1 = 0
      rw [div_mul_cancel₀ _ hc, sub_self]
    have hx : (A ξ).1 - d • X.1 = 0 := Prod.ext hx₁ hx₂
    have hd : d = 0 := by
      have h := congrArg p hx
      rw [map_sub, map_smul, hnormal, map_zero] at h
      change 0 - d * p X.1 = 0 at h
      have hm : d * p X.1 = 0 := by linarith
      exact (mul_eq_zero.mp hm).resolve_right hpv
    have hJ : (A ξ).1 = 0 := by simpa only [hd, zero_smul, sub_zero] using hx
    have hQ : (A ξ).2.comp (ContinuousLinearMap.inr ℝ ℝ V) = 0 := by
      have h := congrArg Prod.snd hred
      change S⁻¹ • ((A ξ).2 - d • X.2).comp (ContinuousLinearMap.inr ℝ ℝ V) = 0 at h
      rw [hd, zero_smul, sub_zero] at h
      exact (smul_eq_zero.mp h).resolve_left (inv_ne_zero hS)
    have hQv : (A ξ).2 X.1 = 0 := by
      have h := henergy ξ
      simpa only [canonicalPhasePairing, hJ, map_zero, sub_zero] using h
    have hQi (v : V) : (A ξ).2 (0, v) = 0 :=
      congrArg (fun f : V →L[ℝ] ℝ ↦ f v) hQ
    have hsplit (u : ℝ × V) : u = u.1 • (1, (0 : V)) + (0, u.2) := by
      ext <;> simp
    have hQ₀ : (A ξ).2 (1, 0) = 0 := by
      rw [hsplit X.1, map_add, map_smul, hQi, add_zero] at hQv
      exact (mul_eq_zero.mp hQv).resolve_left hc
    have hQzero : (A ξ).2 = 0 := by
      apply ContinuousLinearMap.ext
      intro u
      change (A ξ).2 u = 0
      rw [hsplit u, map_add, map_smul, hQ₀, hQi, smul_zero, add_zero]
    apply hA
    simpa only [map_zero] using (Prod.ext hJ hQzero : A ξ = 0)
  intro ξ η h
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, h, sub_self]

end OTSelector.Geometry

end
end
