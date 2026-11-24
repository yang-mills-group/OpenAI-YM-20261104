import YM.LocalLTE.Sail.Ratio

/-! The all-configuration forecast keeps the actual marked polymer covering
of the flags. Only its regular exponent is replaced by the forecast. -/

namespace YM.LocalLTE.Sail.Round2

open Lattice RG Wilson Marker MergeProof MergeProof.Accent Overlay
open scoped BigOperators

variable {G : Gauge} {n : Side} {I : Type} [DecidableEq I] [Fintype I]

noncomputable def retainedForecast (B : Census I) (P : Rep G n) (O : Appendix B P)
    (F : I → Config G n → ℂ) (K : I → ℕ → Config G n → ℂ) (U : Config G n) : Poly B :=
  (Real.exp (P.exponent U) : ℂ) •
    (Poly.pass (forecast B O F U) *
      field (fun box => bar P.activities B U box +
        Mach B (fun j => profile P.activities (K j) box U) + O.K box U)
        (flags P.p.threshold U))

theorem retainedForecast_eq (B : Census I) (P : Rep G n) (O : Appendix B P)
    (o : I → Site n) (F F' : I → Config G n → ℂ) (K : I → ℕ → Config G n → ℂ)
    (X : Config G n → Poly B) (h : Appendix.Prepared B P O o F K X) (U : Config G n)
    (hr : (receipt B O F U).part B.quiet = 0) (hf : (forecast B O F' U).part B.quiet = 0) :
    retainedForecast B P O F' K U =
      X U * Poly.pass (forecast B O F' U - receipt B O F U) := by
  have hδ : (forecast B O F' U - receipt B O F U).part B.quiet = 0 := by
    rw [Extra.Trajectories.part_sub, hr, hf, sub_zero]
  have hexp : Poly.pass (receipt B O F U) * Poly.pass (forecast B O F' U - receipt B O F U) =
      Poly.pass (forecast B O F' U) := by
    rw [← Extra.Trajectories.pass_add hr hδ]
    congr 1
    abel
  have hlog : Mach B (fun i => F i U) + ∑ i, O.H i U = receipt B O F U := by
    unfold receipt Bands.extra
    simp only [h.bank, Pi.zero_apply, Poly.send_zero, Finset.sum_const_zero, zero_add, h.headings]
  rw [h.density]
  unfold retainedForecast restore
  rw [hlog, smul_mul_assoc, mul_right_comm (Poly.pass (receipt B O F U)), hexp]

end YM.LocalLTE.Sail.Round2
