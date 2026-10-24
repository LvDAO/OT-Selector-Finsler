import OTSelector.Analysis.ODE.HamiltonianEndpointUniqueness
import OTSelector.Geometry.JacobiEndpoint
import OTSelector.Geometry.Jacobi.RegularCrossingAlgebra

/-!
Conditions: The state is continuous up to both endpoints, differentiable in the interior and satisfies the stated linear growth bound; Hamiltonian coefficients are continuous for the matrix variant.

Objects: Reverse endpoint norm bound and zero-endpoint uniqueness for the actual Hamiltonian pair.

Proof detail: Take the interior Grönwall bound to an endpoint by continuity, force the interior norm to zero and apply the block bound to the actual pair.

Sources: Gerald Teschl, Section 2.4, Lemma 2.7 and Theorem 2.8, pp. 42–44, equations (2.38)–(2.43) (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=53); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15).
Relation: Endpoint continuity extension of Grönwall. No invertibility or rank of a replacement phase is assumed.
-/

/-!
# Full phase rank through continuous Hamiltonian endpoints

A uniform differential growth bound propagates an interior value backwards from any
point of a continuous closed-interval extension. Thus zero at an endpoint forces zero
throughout the interior, without an endpoint derivative hypothesis. Applying this to a
Hamiltonian pair multiplied by a rank-one matrix shows that one nonsingular interior
position matrix forces trivial joint position/momentum kernel on the entire closed interval.

The existence theorem uses the actual continuous extension from `JacobiEndpoint`.
Wronskian conservation passes to the endpoints by continuity; together with a positive
Hamiltonian coefficient this proves bijectivity of the kernel-to-cokernel crossing map.
These are general finite-dimensional matrix ODE statements. No identification with a
Finsler geodesic variation, endpoint differentiability, or endpoint position invertibility
is assumed or asserted.
-/

open Set Filter
open scoped Topology NNReal

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





open Matrix
open scoped Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]



/-- A single nonsingular interior position matrix forces the full phase to have trivial
joint kernel everywhere on the closed interval, including both possibly focal endpoints. -/
theorem hamiltonian_jointKernel_trivial_on_Icc
    {J P A B C : ℝ → Matrix n n ℝ} {a b c : ℝ}
    (hJcont : ContinuousOn J (Icc a b)) (hPcont : ContinuousOn P (Icc a b))
    (hJ : ∀ s ∈ Ioo a b, HasDerivAt J (B s * J s + C s * P s) s)
    (hP : ∀ s ∈ Ioo a b, HasDerivAt P (-A s * J s - (B s)ᵀ * P s) s)
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hC : ContinuousOn C (Icc a b)) (hc : c ∈ Ioo a b) (hd : (J c).det ≠ 0) :
    ∀ t ∈ Icc a b, ∀ v : n → ℝ, J t *ᵥ v = 0 → P t *ᵥ v = 0 → v = 0 := by
  intro t ht v hJv hPv
  let Q : Matrix n n ℝ := Matrix.vecMulVec v v
  have hJQ : ∀ s ∈ Ioo a b, HasDerivAt (fun r ↦ J r * Q)
      (B s * (J s * Q) + C s * (P s * Q)) s := by
    intro s hs
    simpa only [Matrix.add_mul, Matrix.mul_assoc] using! (hJ s hs).mul_const Q
  have hPQ : ∀ s ∈ Ioo a b, HasDerivAt (fun r ↦ P r * Q)
      (-A s * (J s * Q) - (B s)ᵀ * (P s * Q)) s := by
    intro s hs
    simpa only [Matrix.sub_mul, Matrix.mul_assoc] using! (hP s hs).mul_const Q
  have hJt : J t * Q = 0 := by simp [Q, Matrix.mul_vecMulVec, hJv]
  have hPt : P t * Q = 0 := by simp [Q, Matrix.mul_vecMulVec, hPv]
  obtain ⟨hzero, _⟩ := hamiltonian_pair_eq_zero_of_endpoint_eq_zero
    (hJcont.mul continuousOn_const) (hPcont.mul continuousOn_const)
    hJQ hPQ hA hB hC hc ht hJt hPt
  change J c * Q = 0 at hzero
  have hQ : Q = 0 := by
    have h := congrArg (fun Z ↦ (J c)⁻¹ * Z) hzero
    rwa [Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.mpr hd),
      Matrix.mul_zero] at h
  simpa only [Q, Matrix.vecMulVec_eq_zero, or_self] using hQ

/-- An actual interior Hamiltonian solution with one nonsingular position matrix admits
continuous endpoint extensions whose full phase has trivial joint kernel everywhere. -/
theorem exists_continuous_hamiltonian_extension_jointKernel_trivial
    {J P A B C : ℝ → Matrix n n ℝ} {a b c : ℝ}
    (hJ : ∀ s ∈ Ioo a b, HasDerivAt J (B s * J s + C s * P s) s)
    (hP : ∀ s ∈ Ioo a b, HasDerivAt P (-A s * J s - (B s)ᵀ * P s) s)
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hC : ContinuousOn C (Icc a b)) (hc : c ∈ Ioo a b) (hd : (J c).det ≠ 0) :
    ∃ Jbar Pbar : ℝ → Matrix n n ℝ,
      ContinuousOn Jbar (Icc a b) ∧ ContinuousOn Pbar (Icc a b) ∧
      EqOn Jbar J (Ioo a b) ∧ EqOn Pbar P (Ioo a b) ∧
      ∀ t ∈ Icc a b, ∀ v : n → ℝ,
        Jbar t *ᵥ v = 0 → Pbar t *ᵥ v = 0 → v = 0 := by
  obtain ⟨Jbar, Pbar, hJbar, hPbar, hJeq, hPeq⟩ :=
    exists_continuous_hamiltonian_extension hJ hP hA hB hC hc
  have hJderiv : ∀ s ∈ Ioo a b,
      HasDerivAt Jbar (B s * Jbar s + C s * Pbar s) s := by
    intro s hs
    rw [hJeq hs, hPeq hs]
    exact (hJ s hs).congr_of_eventuallyEq
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hs) fun r hr ↦ hJeq hr)
  have hPderiv : ∀ s ∈ Ioo a b,
      HasDerivAt Pbar (-A s * Jbar s - (B s)ᵀ * Pbar s) s := by
    intro s hs
    rw [hJeq hs, hPeq hs]
    exact (hP s hs).congr_of_eventuallyEq
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hs) fun r hr ↦ hPeq hr)
  refine ⟨Jbar, Pbar, hJbar, hPbar, hJeq, hPeq, ?_⟩
  exact hamiltonian_jointKernel_trivial_on_Icc hJbar hPbar hJderiv hPderiv
    hA hB hC hc (by rwa [hJeq hc])

/-- Interior Hamiltonian Wronskian conservation extends continuously to both endpoints.
No differential equation at the endpoints is assumed. -/
theorem wronskian_identity_on_Icc
    {J P A B C : ℝ → Matrix n n ℝ} {a b c : ℝ}
    (hJcont : ContinuousOn J (Icc a b)) (hPcont : ContinuousOn P (Icc a b))
    (hJ : ∀ s ∈ Ioo a b, HasDerivAt J (B s * J s + C s * P s) s)
    (hP : ∀ s ∈ Ioo a b, HasDerivAt P (-A s * J s - (B s)ᵀ * P s) s)
    (hA : ∀ s ∈ Ioo a b, (A s)ᵀ = A s)
    (hC : ∀ s ∈ Ioo a b, (C s)ᵀ = C s)
    (hc : c ∈ Ioo a b) (hinit : (J c)ᵀ * P c = (P c)ᵀ * J c) :
    ∀ t ∈ Icc a b, (J t)ᵀ * P t = (P t)ᵀ * J t := by
  have hW : EqOn (fun t ↦ (J t)ᵀ * P t) (fun t ↦ (P t)ᵀ * J t) (Ioo a b) :=
    wronskian_identity_on_Ioo hJ hP hA hC hc hinit
  exact hW.of_subset_closure
    ((continuous_id.matrix_transpose.comp_continuousOn hJcont).mul hPcont)
    ((continuous_id.matrix_transpose.comp_continuousOn hPcont).mul hJcont)
    Ioo_subset_Icc_self (by rw [closure_Ioo (hc.1.trans hc.2).ne])

/-- A positive Hamiltonian position crossing is bijective at every closed-interval point,
with full phase rank derived from a single nonsingular interior position matrix. -/
theorem focalCrossingMap_bijective_on_Icc
    {J P A B C : ℝ → Matrix n n ℝ} {a b c : ℝ}
    (hJcont : ContinuousOn J (Icc a b)) (hPcont : ContinuousOn P (Icc a b))
    (hJ : ∀ s ∈ Ioo a b, HasDerivAt J (B s * J s + C s * P s) s)
    (hP : ∀ s ∈ Ioo a b, HasDerivAt P (-A s * J s - (B s)ᵀ * P s) s)
    (hAcont : ContinuousOn A (Icc a b)) (hBcont : ContinuousOn B (Icc a b))
    (hCcont : ContinuousOn C (Icc a b))
    (hA : ∀ s ∈ Ioo a b, (A s)ᵀ = A s)
    (hC : ∀ s ∈ Ioo a b, (C s)ᵀ = C s)
    (hc : c ∈ Ioo a b) (hd : (J c).det ≠ 0)
    (hinit : (J c)ᵀ * P c = (P c)ᵀ * J c) :
    ∀ t ∈ Icc a b, (C t).PosDef →
      Function.Bijective (focalCrossingMap (J t) (B t * J t + C t * P t)) := by
  intro t ht hCt
  exact focalCrossingMap_bijective
    (wronskian_identity_on_Icc hJcont hPcont hJ hP hA hC hc hinit t ht)
    (hamiltonian_jointKernel_trivial_on_Icc hJcont hPcont hJ hP
      hAcont hBcont hCcont hc hd t ht) hCt

end OTSelector.Geometry
