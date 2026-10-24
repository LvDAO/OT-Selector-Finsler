import Mathlib.LinearAlgebra.Matrix.PosDef
import OTSelector.Analysis.ODE.HamiltonianGronwall
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.JacobiPhaseRank.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.JacobiPhaseRank`; the selected original proof blocks follow. -/
section

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

/-- Reverse Gronwall control survives either endpoint by continuity. -/
theorem norm_le_endpoint_norm_mul_exp
    {f f' : ℝ → E} {a b c L : ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hL : 0 ≤ L) (hg : ∀ t ∈ Ioo a b, ‖f' t‖ ≤ L * ‖f t‖)
    (hc : c ∈ Ioo a b) {t : ℝ} (ht : t ∈ Icc a b) :
    ‖f c‖ ≤ ‖f t‖ * Real.exp (L * (b - a)) := by
  have hcl : t ∈ closure (Ioo a b) := by
    rw [closure_Ioo (hc.1.trans hc.2).ne]
    exact ht
  have : NeBot (𝓝[Ioo a b] t) := mem_closure_iff_nhdsWithin_neBot.mp hcl
  apply ge_of_tendsto
    (((hcont t ht).mono Ioo_subset_Icc_self).norm.mul_const (Real.exp (L * (b - a))))
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact norm_le_exp_of_norm_deriv_le_mul hf hL hg hs hc

/-- A zero value anywhere on the closed interval forces every interior value to vanish. -/
theorem eq_zero_of_endpoint_eq_zero_of_norm_deriv_le_mul
    {f f' : ℝ → E} {a b c L : ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hL : 0 ≤ L) (hg : ∀ t ∈ Ioo a b, ‖f' t‖ ≤ L * ‖f t‖)
    (hc : c ∈ Ioo a b) {t : ℝ} (ht : t ∈ Icc a b) (hzero : f t = 0) :
    f c = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [hzero, norm_zero, zero_mul] using
    norm_le_endpoint_norm_mul_exp hcont hf hL hg hc ht

open Matrix
open scoped Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Zero at any closed-interval point forces a continuous Hamiltonian pair to vanish
at every interior point; only interior ODE equations are needed. -/
theorem hamiltonian_pair_eq_zero_of_endpoint_eq_zero
    {J P A B C : ℝ → Matrix n n ℝ} {a b c : ℝ}
    (hJcont : ContinuousOn J (Icc a b)) (hPcont : ContinuousOn P (Icc a b))
    (hJ : ∀ s ∈ Ioo a b, HasDerivAt J (B s * J s + C s * P s) s)
    (hP : ∀ s ∈ Ioo a b, HasDerivAt P (-A s * J s - (B s)ᵀ * P s) s)
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hC : ContinuousOn C (Icc a b)) (hc : c ∈ Ioo a b)
    {t : ℝ} (ht : t ∈ Icc a b) (hJt : J t = 0) (hPt : P t = 0) :
    J c = 0 ∧ P c = 0 := by
  have hBT : ContinuousOn (fun s ↦ (B s)ᵀ) (Icc a b) :=
    continuous_id.matrix_transpose.comp_continuousOn hB
  have hg : ContinuousOn (fun s ↦ ‖A s‖ + ‖B s‖ + ‖C s‖ + ‖(B s)ᵀ‖) (Icc a b) :=
    ((hA.norm.add hB.norm).add hC.norm).add hBT.norm
  obtain ⟨L, hL⟩ := isCompact_Icc.bddAbove_image hg
  let f : ℝ → Matrix n n ℝ × Matrix n n ℝ := fun s ↦ (J s, P s)
  let f' : ℝ → Matrix n n ℝ × Matrix n n ℝ :=
    fun s ↦ (B s * J s + C s * P s, -A s * J s - (B s)ᵀ * P s)
  have hf : ∀ s ∈ Ioo a b, HasDerivAt f (f' s) s := fun s hs ↦
    (hJ s hs).prodMk (hP s hs)
  have hbound : ∀ s ∈ Ioo a b, ‖f' s‖ ≤ max L 0 * ‖f s‖ := by
    intro s hs
    exact (norm_hamiltonian_pair_le (A s) (B s) (C s) (J s) (P s)).trans
      (mul_le_mul_of_nonneg_right
        ((hL (mem_image_of_mem _ (Ioo_subset_Icc_self hs))).trans (le_max_left _ _))
        (norm_nonneg _))
  have hzero : f t = 0 := by simp [f, hJt, hPt]
  have hz := eq_zero_of_endpoint_eq_zero_of_norm_deriv_le_mul
    (hJcont.prodMk hPcont) hf (le_max_right L 0) hbound hc ht hzero
  exact ⟨congrArg Prod.fst hz, congrArg Prod.snd hz⟩









end OTSelector.Geometry

end
