import OTSelector.Geometry.JacobiEndpoint
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Hamiltonian equations at continuous Jacobi endpoints

A continuous interior derivative field determines the derivative within the entire
closed interval, including both endpoints. This is a direct specialization of mathlib's
boundary differentiability theorem, and requires no endpoint derivative premise.
For the matrix Hamiltonian system, continuity of the coefficients and of the solution
makes the derivative field continuous. The existence wrapper starts from an interior
solution and uses the actual endpoint extension constructed in `JacobiEndpoint`.

The generic derivative extension needs no completeness assumption. The conclusions at
the endpoints are one-sided derivatives; no extension to a larger open interval or
identification with actual Finsler Jacobi data is asserted.
-/

open Set Filter
open scoped Topology NNReal

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuous function and derivative fields extend the interior derivative to the
closed interval. Completeness of the target normed space is not needed. -/
theorem hasDerivWithinAt_Icc_of_continuousOn_derivative
    {a b : ℝ} {f g : ℝ → E} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (g t) t) :
    ∀ t ∈ Icc a b, HasDerivWithinAt f (g t) (Icc a b) t := by
  intro t ht
  have hcl : closure (Ioo a b) = Icc a b := closure_Ioo hab.ne
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← hcl]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun s hs ↦ (hd s hs).differentiableAt.differentiableWithinAt)
    (convex_Ioo a b) isOpen_Ioo
    (fun s hs ↦ (hf s (hcl ▸ hs)).mono Ioo_subset_Icc_self)
  have hg' := (ContinuousLinearMap.toSpanSingletonLIE ℝ E).continuous.continuousAt.tendsto.comp
    ((hg t ht).mono Ioo_subset_Icc_self)
  apply hg'.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (hd s hs).hasFDerivAt.fderiv.symm

/-- The same continuous derivative field gives the right derivative at the left endpoint
and the left derivative at the right endpoint. -/
theorem hasDerivWithinAt_endpoints_of_continuousOn_derivative
    {a b : ℝ} {f g : ℝ → E} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (g t) t) :
    HasDerivWithinAt f (g a) (Ici a) a ∧ HasDerivWithinAt f (g b) (Iic b) b := by
  have h := hasDerivWithinAt_Icc_of_continuousOn_derivative hab hf hg hd
  exact ⟨(h a ⟨le_rfl, hab.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hab),
    (h b ⟨hab.le, le_rfl⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hab)⟩

open Matrix
open scoped Matrix.Norms.Operator

variable {n : Type*} [Fintype n]

/-- Continuous Hamiltonian solutions satisfy their actual derivative equations within
the closed interval, including both possibly singular position endpoints. -/
theorem hamiltonian_hasDerivWithinAt_on_Icc
    {J P A B C : ℝ → Matrix n n ℝ} {a b : ℝ} (hab : a < b)
    (hJcont : ContinuousOn J (Icc a b)) (hPcont : ContinuousOn P (Icc a b))
    (hJ : ∀ t ∈ Ioo a b, HasDerivAt J (B t * J t + C t * P t) t)
    (hP : ∀ t ∈ Ioo a b, HasDerivAt P (-A t * J t - (B t)ᵀ * P t) t)
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hC : ContinuousOn C (Icc a b)) :
    ∀ t ∈ Icc a b,
      HasDerivWithinAt J (B t * J t + C t * P t) (Icc a b) t ∧
      HasDerivWithinAt P (-A t * J t - (B t)ᵀ * P t) (Icc a b) t := by
  have hBT : ContinuousOn (fun t ↦ (B t)ᵀ) (Icc a b) :=
    continuous_id.matrix_transpose.comp_continuousOn hB
  have hdJ := hasDerivWithinAt_Icc_of_continuousOn_derivative hab hJcont
    ((hB.mul hJcont).add (hC.mul hPcont)) hJ
  have hdP := hasDerivWithinAt_Icc_of_continuousOn_derivative hab hPcont
    ((hA.neg.mul hJcont).sub (hBT.mul hPcont)) hP
  exact fun t ht ↦ ⟨hdJ t ht, hdP t ht⟩

variable [DecidableEq n]

/-- An actual interior Hamiltonian solution extends continuously to the endpoints and
satisfies the Hamiltonian derivative equations within the entire closed interval.
The endpoint derivatives are conclusions, not assumptions on the extension. -/
theorem exists_closed_hamiltonian_extension
    {J P A B C : ℝ → Matrix n n ℝ} {a b c : ℝ}
    (hJ : ∀ t ∈ Ioo a b, HasDerivAt J (B t * J t + C t * P t) t)
    (hP : ∀ t ∈ Ioo a b, HasDerivAt P (-A t * J t - (B t)ᵀ * P t) t)
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hC : ContinuousOn C (Icc a b)) (hc : c ∈ Ioo a b) :
    ∃ Jbar Pbar : ℝ → Matrix n n ℝ,
      ContinuousOn Jbar (Icc a b) ∧ ContinuousOn Pbar (Icc a b) ∧
      EqOn Jbar J (Ioo a b) ∧ EqOn Pbar P (Ioo a b) ∧
      ∀ t ∈ Icc a b,
        HasDerivWithinAt Jbar (B t * Jbar t + C t * Pbar t) (Icc a b) t ∧
        HasDerivWithinAt Pbar (-A t * Jbar t - (B t)ᵀ * Pbar t) (Icc a b) t := by
  obtain ⟨Jbar, Pbar, hJbar, hPbar, hJeq, hPeq⟩ :=
    exists_continuous_hamiltonian_extension hJ hP hA hB hC hc
  have hJderiv : ∀ t ∈ Ioo a b,
      HasDerivAt Jbar (B t * Jbar t + C t * Pbar t) t := by
    intro t ht
    rw [hJeq ht, hPeq ht]
    exact (hJ t ht).congr_of_eventuallyEq
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) fun r hr ↦ hJeq hr)
  have hPderiv : ∀ t ∈ Ioo a b,
      HasDerivAt Pbar (-A t * Jbar t - (B t)ᵀ * Pbar t) t := by
    intro t ht
    rw [hJeq ht, hPeq ht]
    exact (hP t ht).congr_of_eventuallyEq
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) fun r hr ↦ hPeq hr)
  exact ⟨Jbar, Pbar, hJbar, hPbar, hJeq, hPeq,
    hamiltonian_hasDerivWithinAt_on_Icc (hc.1.trans hc.2) hJbar hPbar
      hJderiv hPderiv hA hB hC⟩

end OTSelector.Geometry
