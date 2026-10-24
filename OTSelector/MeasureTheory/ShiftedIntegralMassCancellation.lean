import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
## Lemma skeleton

* **Conditions:** Finite measures with integrable signed readouts; the shifted readouts are almost everywhere nonnegative and satisfy a genuine lower-integral liminf inequality. Physical means and later candidate masses converge as stated.
* **Objects:** Exact shift identities, a signed lower bound retaining s*(physical mass minus candidate mass), and cancellation when masses converge.
* **Proof detail:** Integrate the constant shift using each actual total mass, convert only the nonnegative shifted integral, pass the physical real limit through ofReal, then let the candidate mass defect vanish.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.
  https://measure.axler.net/MIRA.pdf#page=99
* D. H. Fremlin, *Measure Theory, Volume 2*, Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27

**Relationship to the sources:** Algebra and limit corollaries of integral linearity. The liminf lower bound is an input, not an extra Fatou result, and candidate/physical domains may differ.
-/

/-!
# Signed shift cancellation with the actual domain-mass defect

Candidate and physical measures may live on different spaces. A true shifted
ENNReal lower bound retains their different total masses explicitly. The
physical signed integral converges in the reals, so only the genuine shifted
nonnegative sequence uses liminf. Refining candidate masses then removes the
remaining signed shift error without identifying unequal domains.
-/

open Set Function Filter MeasureTheory Topology
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Adding a constant shift pays the actual finite measure's own mass. -/
theorem integral_add_shift_eq
    {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsFiniteMeasure ρ]
    (f : X → ℝ) (hf : Integrable f ρ) (s : ℝ) :
    (∫ x, f x+s ∂ρ) = (∫ x, f x ∂ρ) + s * ρ.real univ := by
  rw [integral_add hf (integrable_const s),integral_const,smul_eq_mul,mul_comm]

/-- A genuinely nonnegative shifted integrand keeps the exact original
signed integral and the original mass inside ofReal. -/
theorem lintegral_ofReal_add_shift_eq
    {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsFiniteMeasure ρ]
    (f : X → ℝ) (hf : Integrable f ρ) (s : ℝ)
    (hnonneg : ∀ᵐ x ∂ρ, 0 ≤ f x+s) :
    (∫⁻ x, ENNReal.ofReal (f x+s) ∂ρ) =
      ENNReal.ofReal ((∫ x, f x ∂ρ)+s*ρ.real univ) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (f := fun x ↦ f x+s)
    (hf.add (integrable_const s)) hnonneg,
    integral_add_shift_eq ρ f hf s]

/-- The true shifted ENNReal liminf lower bound gives the signed bound with
its exact two-domain mass defect. Candidate and physical spaces may differ,
and the physical space itself may depend on the sample-size index. -/
theorem integral_le_of_shifted_lintegral_le_liminf
    {X : Type*} {Y : ℕ → Type*} [MeasurableSpace X] [∀ n, MeasurableSpace (Y n)]
    (ρ : Measure X) [IsFiniteMeasure ρ]
    (μ : ∀ n, Measure (Y n)) [∀ n, IsFiniteMeasure (μ n)]
    (f : X → ℝ) (hf : Integrable f ρ)
    (g : ∀ n, Y n → ℝ) (hg : ∀ n, Integrable (g n) (μ n))
    (s : ℝ) (_hs : 0 ≤ s)
    (hfn : ∀ᵐ x ∂ρ, 0 ≤ f x+s)
    (hgn : ∀ n, ∀ᵐ y ∂μ n, 0 ≤ g n y+s)
    (mraw mphysical L : ℝ) (hρmass : ρ.real univ = mraw)
    (hμmass : ∀ n, (μ n).real univ = mphysical)
    (hphysical : Tendsto (fun n ↦ ∫ y, g n y ∂μ n) atTop (𝓝 L))
    (hshift : (∫⁻ x, ENNReal.ofReal (f x+s) ∂ρ) ≤
      liminf (fun n ↦ ∫⁻ y, ENNReal.ofReal (g n y+s) ∂μ n) atTop) :
    (∫ x, f x ∂ρ) ≤ L+s*(mphysical-mraw) := by
  have hreal : Tendsto (fun n ↦ (∫ y, g n y ∂μ n)+s*mphysical)
      atTop (𝓝 (L+s*mphysical)) := hphysical.add_const _
  have hphysicalShift (n : ℕ) : (∫ y, g n y+s ∂μ n) =
      (∫ y, g n y ∂μ n)+s*mphysical := by
    rw [integral_add_shift_eq (μ n) (g n) (hg n) s,hμmass n]
  have hlimitNonneg : 0 ≤ L+s*mphysical :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hreal (fun n ↦ by
      rw [← hphysicalShift n]
      exact integral_nonneg_of_ae (hgn n))
  have henn : Tendsto (fun n ↦ ∫⁻ y, ENNReal.ofReal (g n y+s) ∂μ n)
      atTop (𝓝 (ENNReal.ofReal (L+s*mphysical))) := by
    have heq (n : ℕ) : (∫⁻ y, ENNReal.ofReal (g n y+s) ∂μ n) =
        ENNReal.ofReal ((∫ y, g n y ∂μ n)+s*mphysical) := by
      rw [lintegral_ofReal_add_shift_eq (μ n) (g n) (hg n) s (hgn n),hμmass n]
    simp_rw [heq]
    simpa only [Function.comp_def] using ENNReal.continuous_ofReal.tendsto _ |>.comp hreal
  have hleft := lintegral_ofReal_add_shift_eq ρ f hf s hfn
  rw [hρmass] at hleft
  rw [hleft,henn.liminf_eq] at hshift
  have hbound := (ENNReal.ofReal_le_ofReal_iff hlimitNonneg).mp hshift
  linarith

/-- A fixed signed target below all candidate readouts survives the explicit
mass defects when those candidate masses approach the physical mass. -/
theorem le_of_signed_shift_mass_convergence
    (signedReadout mraw : ℕ → ℝ) (V L s mphysical : ℝ)
    (hmass : Tendsto mraw atTop (𝓝 mphysical))
    (hlower : ∀ n, V ≤ signedReadout n)
    (hupper : ∀ n, signedReadout n ≤ L+s*(mphysical-mraw n)) : V ≤ L := by
  have ht : Tendsto (fun n ↦ L+s*(mphysical-mraw n)) atTop (𝓝 L) := by
    simpa only [sub_self,mul_zero,add_zero] using
      (tendsto_const_nhds.add ((tendsto_const_nhds.sub hmass).const_mul s) :
        Tendsto (fun n ↦ L+s*(mphysical-mraw n)) atTop (𝓝 (L+s*(mphysical-mphysical))))
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds ht
    (fun n ↦ (hlower n).trans (hupper n))

/-- The actual measure-family conclusion: true shifted ENNReal lower bounds
for refined candidate domains imply the fixed signed target bound when their
own original masses recover the physical mass. No equal-domain mass identity
or signed-energy bound is supplied as a callback. -/
theorem le_of_shifted_candidate_mass_convergence
    {X Y : ℕ → Type*} [∀ j, MeasurableSpace (X j)] [∀ n, MeasurableSpace (Y n)]
    (ρ : ∀ j, Measure (X j)) [∀ j, IsFiniteMeasure (ρ j)]
    (μ : ∀ n, Measure (Y n)) [∀ n, IsFiniteMeasure (μ n)]
    (f : ∀ j, X j → ℝ) (hf : ∀ j, Integrable (f j) (ρ j))
    (g : ∀ n, Y n → ℝ) (hg : ∀ n, Integrable (g n) (μ n))
    (s : ℝ) (hs : 0 ≤ s)
    (hfn : ∀ j, ∀ᵐ x ∂ρ j, 0 ≤ f j x+s)
    (hgn : ∀ n, ∀ᵐ y ∂μ n, 0 ≤ g n y+s)
    (mphysical V L : ℝ) (hμmass : ∀ n, (μ n).real univ = mphysical)
    (hphysical : Tendsto (fun n ↦ ∫ y, g n y ∂μ n) atTop (𝓝 L))
    (hmass : Tendsto (fun j ↦ (ρ j).real univ) atTop (𝓝 mphysical))
    (hlower : ∀ j, V ≤ ∫ x, f j x ∂ρ j)
    (hshift : ∀ j, (∫⁻ x, ENNReal.ofReal (f j x+s) ∂ρ j) ≤
      liminf (fun n ↦ ∫⁻ y, ENNReal.ofReal (g n y+s) ∂μ n) atTop) : V ≤ L := by
  apply le_of_signed_shift_mass_convergence (fun j ↦ ∫ x, f j x ∂ρ j)
    (fun j ↦ (ρ j).real univ) V L s mphysical hmass hlower
  intro j
  exact integral_le_of_shifted_lintegral_le_liminf (ρ j) μ (f j) (hf j) g hg s hs
    (hfn j) hgn ((ρ j).real univ) mphysical L rfl hμmass hphysical (hshift j)

end OTSelector.Reconstruction
