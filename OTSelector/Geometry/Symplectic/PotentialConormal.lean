import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Analysis.ODE.Flow.LocalVariational
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.Hessian
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Finsler.Jacobi.VariationalFlow
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.PotentialConormal.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.PotentialConormal`; the selected original proof blocks follow. -/
section

/-!
Conditions: A differentiable level section and potential with actual symmetric second derivatives; an immersion is required for the rank conclusion.

Objects: Conormal differential, isotropy and immersion rank, with transport by the actual Hamiltonian flow.

Proof detail: Differentiate (σ,a·df∘σ), use the level identity and Hessian symmetry to cancel canonical pairings, and use symplectic flow preservation for the transport variant.

Sources: Ana Cannas da Silva, Section 3.2, pp. 16–17; Section 3.3, Definition 3.5, Proposition 3.6 and Corollary 3.7, pp. 17–18 (https://people.math.ethz.ch/~acannas/Papers/lsg.pdf#page=24); Jiří Lebl, Section 8.6, Proposition 8.6.2, pp. 60–61 (equality of mixed second partial derivatives) (https://www.jirka.org/ra/realanal2.pdf#page=60); Matias Dahl, Section 7, Definition 7.5 and Proposition 7.6, pp. 31–32 (https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=31).
Relation: Finite-jet conormal/isotropy calculation derived from the classical conormal construction; it does not assert the smooth global bundle theorem under weaker hypotheses.
-/

/-!
# Actual potential conormal data on a smooth level set

For an arbitrary parameterization of a level set of a real potential, take the actual
differential of that potential, multiplied by a differentiable scalar. Its derivative
uses the actual potential Hessian. Symmetry follows from C2 regularity and gives zero
canonical pairing on tangent directions; immersion of the parameterization gives full
phase rank. No independent symmetric matrix or affine hypersurface is substituted.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Cotangent initial data from the actual potential and a level-set parameterization. -/
def potentialConormalState (f : E → ℝ) (σ : W → E) (a : W → ℝ) (w : W) :
    E × (E →L[ℝ] ℝ) := (σ w, a w • fderiv ℝ f (σ w))

/-- Its derivative contains the actual Hessian of the potential and derivative of the scale. -/
theorem hasFDerivAt_potentialConormalState
    {f : E → ℝ} {σ : W → E} {a : W → ℝ} {w : W}
    (hf : ContDiffAt ℝ 2 f (σ w)) (hσ : DifferentiableAt ℝ σ w)
    (ha : DifferentiableAt ℝ a w) :
    HasFDerivAt (potentialConormalState f σ a)
      ((fderiv ℝ σ w).prod
        (a w • ((fderiv ℝ (fderiv ℝ f) (σ w)).comp (fderiv ℝ σ w)) +
          (fderiv ℝ a w).smulRight (fderiv ℝ f (σ w)))) w := by
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  exact hσ.hasFDerivAt.prodMk (ha.hasFDerivAt.smul (hdf.hasFDerivAt.comp w hσ.hasFDerivAt))

/-- A local level-set parameterization pulls the actual differential back to zero. -/
theorem fderiv_comp_eq_zero_of_eventually_constant
    {f : E → ℝ} {σ : W → E} {w : W} {c : ℝ}
    (hf : DifferentiableAt ℝ f (σ w)) (hσ : DifferentiableAt ℝ σ w)
    (hlevel : (fun u ↦ f (σ u)) =ᶠ[𝓝 w] fun _ ↦ c) :
    (fderiv ℝ f (σ w)).comp (fderiv ℝ σ w) = 0 := by
  exact (hf.hasFDerivAt.comp w hσ.hasFDerivAt).unique
    ((hasFDerivAt_const (𝕜 := ℝ) c w).congr_of_eventuallyEq hlevel)

/-- The canonical pairing is the actual exterior product of scale and pulled-back potential.
The Hessian terms cancel by the symmetry of the true second derivative. -/
theorem potentialConormalState_fderiv_pairing
    {f : E → ℝ} {σ : W → E} {a : W → ℝ} {w : W}
    (hf : ContDiffAt ℝ 2 f (σ w)) (hσ : DifferentiableAt ℝ σ w)
    (ha : DifferentiableAt ℝ a w) (u v : W) :
    canonicalPhasePairing (fderiv ℝ (potentialConormalState f σ a) w u)
        (fderiv ℝ (potentialConormalState f σ a) w v) =
      fderiv ℝ a w v * fderiv ℝ f (σ w) (fderiv ℝ σ w u) -
        fderiv ℝ a w u * fderiv ℝ f (σ w) (fderiv ℝ σ w v) := by
  rw [(hasFDerivAt_potentialConormalState hf hσ ha).fderiv]
  have hsym := hf.isSymmSndFDerivAt (by norm_num) (fderiv ℝ σ w v) (fderiv ℝ σ w u)
  simp only [canonicalPhasePairing, ContinuousLinearMap.prod_apply,
    _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul]
  rw [hsym]
  ring

/-- The true scaled potential differential annihilates every level-set tangent direction. -/
theorem potentialConormalState_momentum_eq_zero
    {f : E → ℝ} {σ : W → E} {a : W → ℝ} {w : W} {c : ℝ}
    (hf : DifferentiableAt ℝ f (σ w)) (hσ : DifferentiableAt ℝ σ w)
    (hlevel : (fun u ↦ f (σ u)) =ᶠ[𝓝 w] fun _ ↦ c) (u : W) :
    (potentialConormalState f σ a w).2 (fderiv ℝ σ w u) = 0 := by
  have h := congrArg (fun D : W →L[ℝ] ℝ ↦ D u)
    (fderiv_comp_eq_zero_of_eventually_constant hf hσ hlevel)
  change a w * fderiv ℝ f (σ w) (fderiv ℝ σ w u) = 0
  simpa only [ContinuousLinearMap.comp_apply, _root_.zero_apply, mul_zero] using
    congrArg (fun r : ℝ ↦ a w * r) h

/-- An immersed actual level-set seed has injective phase derivative and zero canonical pairing. -/
theorem potentialConormalState_fderiv_properties
    {f : E → ℝ} {σ : W → E} {a : W → ℝ} {w : W} {c : ℝ}
    (hf : ContDiffAt ℝ 2 f (σ w)) (hσ : DifferentiableAt ℝ σ w)
    (ha : DifferentiableAt ℝ a w)
    (hlevel : (fun u ↦ f (σ u)) =ᶠ[𝓝 w] fun _ ↦ c)
    (himm : Function.Injective (fderiv ℝ σ w)) :
    Function.Injective (fderiv ℝ (potentialConormalState f σ a) w) ∧
      ∀ u v : W, canonicalPhasePairing (fderiv ℝ (potentialConormalState f σ a) w u)
        (fderiv ℝ (potentialConormalState f σ a) w v) = 0 := by
  constructor
  · rw [(hasFDerivAt_potentialConormalState hf hσ ha).fderiv]
    intro u v huv
    exact himm (congrArg Prod.fst huv)
  · intro u v
    rw [potentialConormalState_fderiv_pairing hf hσ ha]
    have h := fderiv_comp_eq_zero_of_eventually_constant
      (hf.differentiableAt (by norm_num)) hσ hlevel
    have hu := congrArg (fun D : W →L[ℝ] ℝ ↦ D u) h
    have hv := congrArg (fun D : W →L[ℝ] ℝ ↦ D v) h
    simp only [ContinuousLinearMap.comp_apply, _root_.zero_apply] at hu hv
    rw [hu, hv]
    ring


namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]
  {F : ContinuousFinslerNorm E M}

/-- A genuine Finsler flow transports the actual immersed potential-level seed.
All phase derivatives, zero pairings, rank and linearized equations use the same constructed
flow. The seed scale is explicit here; constant-energy normalization is a separate step. -/
theorem exists_chartHamiltonian_potentialConormalVariation (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {f : E → ℝ} {σ : W → E} {a : W → ℝ} {w₀ : W} {c : ℝ}
    (hf : ContDiffAt ℝ 2 f (σ w₀)) (hσ : DifferentiableAt ℝ σ w₀)
    (ha : DifferentiableAt ℝ a w₀)
    (hlevel : (fun w ↦ f (σ w)) =ᶠ[𝓝 w₀] fun _ ↦ c)
    (himm : Function.Injective (fderiv ℝ σ w₀))
    {v₀ : E} (hz : (σ w₀, v₀) ∈ chartEnergyDomain x₀)
    (hmatch : a w₀ • fderiv ℝ f (σ w₀) = fiberLegendre (F.chartEnergy x₀) (σ w₀, v₀))
    (t₀ : ℝ) :
    let L := F.chartEnergy x₀
    let z := (σ w₀, v₀)
    let p₀ := parametricLegendre L z
    let seed := potentialConormalState f σ a
    ∃ (e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)))
      (r : ℝ≥0) (T : ℝ) (Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)),
      let Z := fun t ↦ fderiv ℝ (fun w ↦ Φ (seed w, t)) w₀
      (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L ∧
      z ∈ e.source ∧ e.source ⊆ chartEnergyDomain x₀ ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧ 0 < r ∧ 0 < T ∧
      LocalFlow.IsLocalFlow (fun _ ↦ localHamiltonianVectorField L e)
        t₀ p₀ r (t₀ - T) (t₀ + T) Φ ∧
      MapsTo Φ (closedBall p₀ r ×ˢ Icc (t₀ - T) (t₀ + T)) e.target ∧
      (∀ᶠ w in 𝓝 w₀, seed w ∈ closedBall p₀ r) ∧
      (∀ u : W, (seed w₀).2 (fderiv ℝ σ w₀ u) = 0) ∧
      Z t₀ = fderiv ℝ seed w₀ ∧
      ∀ t ∈ Icc (t₀ - T) (t₀ + T),
        DifferentiableAt ℝ (fun w ↦ Φ (seed w, t)) w₀ ∧
        Function.Injective (Z t) ∧
        (∀ u v : W, canonicalPhasePairing (Z t u) (Z t v) = 0) ∧
        ∀ u : W, HasDerivWithinAt (fun s ↦ Z s u)
          (fderiv ℝ (localHamiltonianVectorField L e) (Φ (p₀, t)) (Z t u))
          (Icc (t₀ - T) (t₀ + T)) t := by
  let L := F.chartEnergy x₀
  let z := (σ w₀, v₀)
  let p₀ := parametricLegendre L z
  let seed := potentialConormalState f σ a
  have hseed : seed w₀ = p₀ := Prod.ext rfl hmatch
  have hdseed := hasFDerivAt_potentialConormalState hf hσ ha
  have hseedprop := potentialConormalState_fderiv_properties hf hσ ha hlevel himm
  obtain ⟨e, he, hzs, hzt, hsub, hG, _, hX, _⟩ :=
    hF.exists_smooth_chartHamiltonian x₀ hz
  obtain ⟨r, T, hr, hT, Φ, hflow, hmap, hdiff, hinit, hraw⟩ :=
    LocalFlow.exists_differentiableFlow_in_open e.open_target hX hzt t₀
  let I := Icc (t₀ - T) (t₀ + T)
  have hinitAt : fderiv ℝ (fun q ↦ Φ (q, t₀)) p₀ = ContinuousLinearMap.id ℝ _ := hinit
  have hL : ContDiffOn ℝ ∞ L e.source := (hF.contDiffOn_chartEnergy x₀).mono hsub
  have htarg (t : ℝ) (ht : t ∈ I) : Φ (p₀, t) ∈ e.target :=
    hmap ⟨mem_closedBall_self r.coe_nonneg, ht⟩
  have hpair (t : ℝ) (ht : t ∈ I) (u v : E × (E →L[ℝ] ℝ)) :
      canonicalPhasePairing (fderiv ℝ (fun q ↦ Φ (q, t)) p₀ u)
        (fderiv ℝ (fun q ↦ Φ (q, t)) p₀ v) = canonicalPhasePairing u v := by
    have hb (δ : E × (E →L[ℝ] ℝ)) (s : ℝ) (hs : s ∈ I) :=
      hasDerivWithinAt_hamiltonianFlowVariation_blocks he hL hG (htarg s hs) (hraw δ s hs)
    have h := hamiltonian_pairing_eq_on_Icc
      (t₀ := t₀) (by constructor <;> linarith : t₀ ∈ Ioo (t₀ - T) (t₀ + T))
      (fun s hs ↦ (hb u s hs).1) (fun s hs ↦ (hb u s hs).2)
      (fun s hs ↦ (hb v s hs).1) (fun s hs ↦ (hb v s hs).2)
      (fun s hs ↦ localHamiltonianBlockA_symm he hL hG (htarg s hs))
      (fun s hs ↦ localHamiltonianBlockC_symm he hL hG (htarg s hs)) t ht
    simpa only [canonicalPhasePairing, flowPositionVariation, flowMomentumVariation,
      hinitAt, ContinuousLinearMap.id_apply] using h
  have hchain (t : ℝ) (ht : t ∈ I) :
      fderiv ℝ (fun w ↦ Φ (seed w, t)) w₀ =
        (fderiv ℝ (fun q ↦ Φ (q, t)) p₀).comp (fderiv ℝ seed w₀) := by
    have hd : DifferentiableAt ℝ (fun q ↦ Φ (q, t)) (seed w₀) := hseed.symm ▸ hdiff t ht
    exact (hd.hasFDerivAt.comp w₀ hdseed.differentiableAt.hasFDerivAt).fderiv.trans
      (by rw [hseed])
  refine ⟨e, r, T, Φ, he, hzs, hsub, hG, hr, hT, hflow, hmap, ?_, ?_, ?_, ?_⟩
  · have hn := hdseed.continuousAt.preimage_mem_nhds
      (closedBall_mem_nhds (seed w₀) (show (0 : ℝ) < r from hr))
    change ∀ᶠ w in 𝓝 w₀, seed w ∈ closedBall (seed w₀) r at hn
    rw [hseed] at hn
    exact hn
  · exact fun u ↦ potentialConormalState_momentum_eq_zero
      (hf.differentiableAt (by norm_num)) hσ hlevel u
  · change fderiv ℝ (fun w ↦ Φ (seed w, t₀)) w₀ = fderiv ℝ seed w₀
    rw [hchain t₀ (by constructor <;> linarith), hinitAt]
    rfl
  · intro t ht
    have hd : DifferentiableAt ℝ (fun q ↦ Φ (q, t)) (seed w₀) := hseed.symm ▸ hdiff t ht
    refine ⟨hd.comp w₀ hdseed.differentiableAt, ?_, ?_, ?_⟩
    · change Function.Injective (fderiv ℝ (fun w ↦ Φ (seed w, t)) w₀)
      rw [hchain t ht]
      exact (injective_of_canonicalPhasePairing_preserved _ (hpair t ht)).comp hseedprop.1
    · intro u v
      change canonicalPhasePairing (fderiv ℝ (fun w ↦ Φ (seed w, t)) w₀ u)
        (fderiv ℝ (fun w ↦ Φ (seed w, t)) w₀ v) = 0
      rw [hchain t ht]
      exact (hpair t ht _ _).trans (hseedprop.2 u v)
    · intro u
      change HasDerivWithinAt (fun s ↦ fderiv ℝ (fun w ↦ Φ (seed w, s)) w₀ u)
        (fderiv ℝ (localHamiltonianVectorField L e) (Φ (p₀, t))
          (fderiv ℝ (fun w ↦ Φ (seed w, t)) w₀ u)) I t
      rw [hchain t ht]
      exact (hraw (fderiv ℝ seed w₀ u) t ht).congr_of_mem
        (fun s hs ↦ by rw [hchain s hs]; rfl) ht

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
