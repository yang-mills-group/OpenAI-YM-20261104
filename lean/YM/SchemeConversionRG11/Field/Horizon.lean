import YM.Pert.Rigid.Spin
import YM.Next.MAXWELL.Shelves
import YM.Next.MAXWELL.System

/-!
# Shared free horizon coordinates

These are exactly freeTable separated fields and their engineering filtration. Use the Wick
symbol isomorphism to define the splitting (no freely changing bases across horizons). Interaction
label maps and actual interpolation stencils need additional proofs, and there is no analogous
claim of grade projection on pre-quotient coincidence distributions.
-/

set_option autoImplicit false
noncomputable section

namespace YM.SchemeConversionRG11.Horizon

open Pert.Position Pert.Rigid Maxwell

variable {G : Gauge} (F : Labels.Frames G)

/-- Inclusion is within the Wick labels indexing both prescriptions. -/
abbrev incl {d e : ℕ} (h : d ≤ e) : E F d →ₗ[ℂ] E F e := (Free.scheme F).rise h

theorem incl_injective {d e : ℕ} (h : d ≤ e) : Function.Injective (incl F h) :=
  (Free.scheme F).inject (table_sym F) (Free.scheme_filters F) h

theorem incl_range {d e : ℕ} (h : d ≤ e) : LinearMap.range (incl F h) = lower F d e := by
  apply SetLike.coe_injective
  rw [← upward F h (Free.scheme F) (Free.scheme_filters F), stairs_eq]

theorem incl_self {d : ℕ} (v : E F d) : incl F le_rfl v = v :=
  (Free.scheme F).arrival (table_sym _) (Free.scheme_filters _) v

theorem incl_repeat {d e b : ℕ} (h : d ≤ e) (k : e ≤ b) (v : E F d) :
    incl F k (incl F h v) = incl F (h.trans k) v :=
  (Free.scheme F).transit (table_sym _) (Free.scheme_filters _) h k v

theorem incl_unit {d e : ℕ} (h : d ≤ e) : incl F h ((freeTable F).unit d) = (freeTable F).unit e :=
  (Free.scheme F).fixs (Free.scheme_filters _) (table_regular _) _

abbrev bar (d : ℕ) := (freeTable F).conj (Free.spin_free F) d

theorem incl_bar {d e : ℕ} (h : d ≤ e) (v : E F d) : incl F h (bar F d v) = bar F e (incl F h v) :=
  ((Free.phase_orientation F).realInc h v).symm

theorem incl_rotate {d e : ℕ} (h : d ≤ e) (s : Signed) (v : E F d) :
    incl F h (Extra.FD.rideO F s.ortho d v) = Extra.FD.rideO F s.ortho e (incl F h v) := by
  rw [← wear_ride, ← wear_ride]
  exact ((Free.phase_orientation F).mirrorInc h s v).symm

section Grade
open Maxwell.Free

/-- Wick through-grade projection on symbols. -/
private def throughGrade (d : ℕ) : WickPol G →ₗ[ℂ] WickPol G :=
  ∑ i ∈ Finset.range (d+1), gloss (fun j ↦ j+2) i

private theorem through_coeff (d : ℕ) (p : WickPol G) (s : Slot G →₀ ℕ) :
    MvPolynomial.coeff s (throughGrade d p) = if degree s ≤ d then MvPolynomial.coeff s p else 0 := by
  classical
  rw [throughGrade, LinearMap.sum_apply, MvPolynomial.coeff_sum]
  simp_rw [gloss, MvPolynomial.coeff_weightedHomogeneousComponent]
  change (∑ i ∈ Finset.range _, if degree s = i then _ else _) = _
  simp only [Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff]

private theorem through_idem {d : ℕ} (p : WickPol G) (h : p ∈ shellSector G d) : throughGrade d p = p := by
  classical
  ext i
  rw [through_coeff]
  obtain ⟨hc, -⟩ := sector.mp h
  rw [lowerCap, MvPolynomial.mem_restrictSupport_iff] at hc
  split_ifs with hh
  · rfl
  exact (by_contra fun H ↦ hh (hc (MvPolynomial.mem_support_iff.mpr (Ne.symm H))))

private theorem through_in {d e : ℕ} (p : WickPol G) (h : p ∈ shellSector G e) : throughGrade d p ∈ shellSector G d := by
  classical
  have he : throughGrade d p ∈ shellSector G e := by
    rw [throughGrade, LinearMap.sum_apply]
    exact (shellSector G e).sum_mem (fun _ _ ↦ colors_grade _ _ h)
  refine sector.mpr ⟨?_, (sector.mp he).2⟩
  rw [lowerCap, MvPolynomial.mem_restrictSupport_iff]
  intro i hi
  have ht : ¬ MvPolynomial.coeff i (throughGrade d p) = 0 := MvPolynomial.mem_support_iff.mp hi
  by_contra hn
  change ¬ degree i ≤ d at hn
  rw [through_coeff, if_neg hn] at ht
  contradiction

/-- Keep through d from e, no embeddings silently recomputed at higher horizon. -/
def cut (d e : ℕ) : E F e →ₗ[ℂ] E F d :=
  (fields F d).symm.toLinearMap.comp
    (((throughGrade d).comp (address F e)).codRestrict (shellSector G d) (fun p ↦ through_in _ (address_in F e p)))

private theorem cut_eq (d e : ℕ) (p : E F e) : address F d (cut F d e p) = throughGrade d (address F e p) := by
  rw [cut, LinearMap.comp_apply, LinearEquiv.coe_coe, address_eval, LinearEquiv.apply_symm_apply]; rfl

/-- Useful explicit adapter back to a Wick-polynomial representative. -/
theorem coeff_cut (d e : ℕ) (p : E F e) (u : Slot G →₀ ℕ) :
    (address F d (cut F d e p)).coeff u =
      if degree u ≤ d then (address F e p).coeff u else 0 := by rw [cut_eq, through_coeff]

theorem cut_repeat {d e k : ℕ} (p : E F k) (h : d ≤ e) : cut F d e (cut F e k p) = cut F d k p := by
  apply address_inj F d
  ext u
  simp only [coeff_cut]
  by_cases hh : degree u ≤ d
  · rw [if_pos hh, if_pos (hh.trans h), if_pos hh]
  rw [if_neg hh, if_neg hh]

theorem cut_incl {d e : ℕ} (h : d ≤ e) (v : E F d) : cut F d e (incl F h v) = v :=
  address_inj F d (by rw [cut_eq, incl, address_rise, through_idem _ (address_in F d v)])

theorem cut_bar {d e : ℕ} (p : E F e) : cut F d e (bar F e p) = bar F d (cut F d e p) := by
  apply address_inj F _
  rw [cut_eq, bar, bar, address_star, address_star, cut_eq]
  simp only [throughGrade, LinearMap.sum_apply, _root_.map_sum, real_gloss]

theorem cut_rotate {d e : ℕ} (p : E F e) (s : Signed) :
    cut F d e (Extra.FD.rideO F s.ortho e p) = Extra.FD.rideO F s.ortho d (cut F d e p) := by
  apply address_inj F _
  rw [← wear_ride, ← wear_ride, wear, wear, cut_eq, address_motion, address_motion, cut_eq]
  simp only [throughGrade, LinearMap.sum_apply, _root_.map_sum, gloss_mirror]
end Grade

end YM.SchemeConversionRG11.Horizon
