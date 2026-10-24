import OTSelector.Geometry.Finsler.Energy.Transition
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Symplectic.CotangentChartPairing
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CotangentFamilyTransition.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CotangentFamilyTransition`; the selected original proof blocks follow. -/
section

/-!
Conditions: A C2 phase family through an actual cotangent chart lift, with the stated inverse and differential hypotheses.

Objects: C2 transition families and preservation of pairing and injectivity of actual parameter variations.

Proof detail: Apply the chain rule to the lift and use its pairing identity and invertible derivative to transfer the two conclusions.

Sources: Ana Cannas da Silva, Section 2.4, Proposition 2.1 and Corollary 2.2, pp. 11–12 (https://people.math.ethz.ch/~acannas/Papers/lsg.pdf#page=19); Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38).
Relation: Family-level chart adapter for cotangent naturality; actual derivative assumptions remain explicit.
-/

/-!
# Actual parameter variations under cotangent chart changes

The genuine manifold chart lift transports a C2 phase family to a C2 family.
Its true parameter differential preserves the original canonical pairing and
injectivity. The derivative is obtained by the chain rule for that same family;
no separately chosen variation or chart-pairing identity is assumed.
-/

open Set Manifold
open scoped Topology ContDiff

namespace OTSelector.Geometry

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Actual C2 phase families remain C2 under the genuine cotangent chart transition. -/
theorem contDiffOn_rechartedPhase (old new : M)
    {Ψ : W → E × (E →L[ℝ] ℝ)} {D : Set W} (hΨ : ContDiffOn ℝ 2 Ψ D)
    (hmap : ∀ q ∈ D, (Ψ q).1 ∈ chartTransitionDomain old new) :
    ContDiffOn ℝ 2
      (cotangentLift (chartTransition old new) (chartTransition new old) ∘ Ψ) D :=
  ((contDiffOn_chartCotangentLift old new).of_le (by simp)).comp hΨ
    (fun q hq ↦ ⟨hmap q hq, mem_univ _⟩)

/-- The actual derivative of a recharted family preserves the original variation pairing. -/
theorem rechartedPhase_fderiv_pairing (old new : M)
    {Ψ : W → E × (E →L[ℝ] ℝ)} {q : W} (hΨ : DifferentiableAt ℝ Ψ q)
    (hq : (Ψ q).1 ∈ chartTransitionDomain old new) (u v : W) :
    canonicalPhasePairing
      (fderiv ℝ (cotangentLift (chartTransition old new) (chartTransition new old) ∘ Ψ) q u)
      (fderiv ℝ (cotangentLift (chartTransition old new) (chartTransition new old) ∘ Ψ) q v) =
        canonicalPhasePairing (fderiv ℝ Ψ q u) (fderiv ℝ Ψ q v) := by
  have hT := ((contDiffOn_chartCotangentLift old new).contDiffAt
    (((isOpen_chartTransitionDomain old new).prod isOpen_univ).mem_nhds
      ⟨hq, mem_univ _⟩)).differentiableAt (by simp)
  rw [(hT.hasFDerivAt.comp q hΨ.hasFDerivAt).fderiv]
  exact chartCotangentLift_fderiv_pairing old new hq _ _

/-- A genuine cotangent chart change preserves injectivity of the actual family derivative. -/
theorem injective_rechartedPhase_fderiv (old new : M)
    {Ψ : W → E × (E →L[ℝ] ℝ)} {q : W} (hΨ : DifferentiableAt ℝ Ψ q)
    (hq : (Ψ q).1 ∈ chartTransitionDomain old new)
    (hinj : Function.Injective (fderiv ℝ Ψ q)) :
    Function.Injective
      (fderiv ℝ (cotangentLift (chartTransition old new) (chartTransition new old) ∘ Ψ) q) := by
  have hT := ((contDiffOn_chartCotangentLift old new).contDiffAt
    (((isOpen_chartTransitionDomain old new).prod isOpen_univ).mem_nhds
      ⟨hq, mem_univ _⟩)).differentiableAt (by simp)
  rw [(hT.hasFDerivAt.comp q hΨ.hasFDerivAt).fderiv]
  exact (injective_of_canonicalPhasePairing_preserved _
    (chartCotangentLift_fderiv_pairing old new hq)).comp hinj

/-- The same actual C2 time-dependent family retains its parameter variation pairing and
phase injectivity after a true chart change on any open overlap domain. -/
theorem rechartedFamily_parameter_structure (old new : M)
    {Ψ : W × ℝ → E × (E →L[ℝ] ℝ)} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : ContDiffOn ℝ 2 Ψ D)
    (hmap : ∀ q ∈ D, (Ψ q).1 ∈ chartTransitionDomain old new) :
    let Γ := cotangentLift (chartTransition old new) (chartTransition new old) ∘ Ψ
    ContDiffOn ℝ 2 Γ D ∧
      ∀ q ∈ D,
        let Z := fderiv ℝ (fun w ↦ Ψ (w, q.2)) q.1
        let R := fderiv ℝ (fun w ↦ Γ (w, q.2)) q.1
        (∀ u v : W, canonicalPhasePairing (R u) (R v) = canonicalPhasePairing (Z u) (Z v)) ∧
        (Function.Injective Z → Function.Injective R) := by
  refine ⟨contDiffOn_rechartedPhase old new hΨ hmap, ?_⟩
  intro q hq
  have hs : DifferentiableAt ℝ (fun w ↦ Ψ (w, q.2)) q.1 :=
    ((hΨ.contDiffAt (hD.mem_nhds hq)).differentiableAt (by norm_num)).comp q.1
      (differentiableAt_id.prodMk (differentiableAt_const q.2))
  exact ⟨fun u v ↦ rechartedPhase_fderiv_pairing old new hs (hmap q hq) u v,
    injective_rechartedPhase_fderiv old new hs (hmap q hq)⟩

end OTSelector.Geometry

end
