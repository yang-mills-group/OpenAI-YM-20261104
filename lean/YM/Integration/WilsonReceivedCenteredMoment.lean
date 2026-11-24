import YM.Integration.WilsonReceivedPostLog
import YM.Integration.WilsonReceivedIdentityField
import YM.Integration.FVA1Physical.Round2.CP5GalleryLog
import YM.UVNext.COUPLING_RESET.Probe
import YM.Comparison.RG02.Cumulants.Parents

/-! The ordinary product minus a filed counterterm on one original Wilson source.
The full pair includes its two proper singleton factors. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedCenteredMoment
open Finset Marker Lattice Wilson RG QuadraticLocal Extra.Trajectories Comparison.RG02 Comparison.RG02.Cumulants
open FVA1Physical.Round2.CP5
open scoped Classical BigOperators

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}

theorem gallery_quiet {G : Gauge} {n : Side} {P : Rep G n} {T ι : Type} {o : V → Site n}
    (A : Gallery T ι o P R) (x : T) :
    ((((P.eval 1:ℂ)⁻¹) • A.density x 1).part R.quiet) = 1 := by
  have clear := UVNext.CouplingReset.flags_one (n:=n) (G:=G) P.p
  have zero : (A.E.log x 1).part R.quiet=0 := by
    by_cases sums : Summable (fun j => A.E.frame j x 1)
    · exact Lamps.quiet_of_hasSum x 1 sums
    · rw [Lamps.log,tsum_eq_zero_of_not_summable sums]
      rfl
  have vac : P.eval 1 = Real.exp (P.exponent 1) := by
    rw [Rep.eval,P.activities.gas_one (p:=P.p) clear,mul_one]
  have positive : (Real.exp (P.exponent 1):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  rw [Gallery.density,gallery_gas_one A x 1 clear,mul_one,Poly.part_smul,Poly.part_smul,
    Poly.pass_part _ zero,mul_one,vac,inv_mul_cancel₀ positive]

/-- The independent singleton on the right of the telescope and the true singleton
on its left are evaluated on their respective complete common vacua. -/
theorem identity (Y T : Poly R) (quiet : Y.part R.quiet = 1)
    (a b c : V) (s : R.Mode) (h : a≠b) (pair : s.val={a,b}) :
    let L := Order.logTo (Fintype.card V) Y
    let err := fun t => (L-T).part t
    (Y.part s - Y.part (R.fire c)) -
      (T.part s - T.part (R.fire c) + T.part (R.fire a)*T.part (R.fire b)) =
      err s - err (R.fire c) + err (R.fire a)*Y.part (R.fire b) +
        T.part (R.fire a)*err (R.fire b) := by
  dsimp only
  rw [← Order.log_to Y quiet (Fintype.card V) (fun _ => Finset.card_le_univ _)]
  simp only [part_sub,twins a b s Y quiet h pair,lamp a Y quiet,lamp b Y quiet,lamp c Y quiet]
  ring

theorem priced (Y T : Poly R) (quiet : Y.part R.quiet = 1)
    (a b c : V) (s : R.Mode) (h : a≠b) (pair : s.val={a,b}) (cost : R.Mode → ℝ)
    (paid : ∀ t ∈ ({s,R.fire c,R.fire a,R.fire b} : Finset R.Mode),
      ‖(Order.logTo (Fintype.card V) Y-T).part t‖ ≤ cost t) :
    ‖(Y.part s - Y.part (R.fire c)) -
      (T.part s - T.part (R.fire c) + T.part (R.fire a)*T.part (R.fire b))‖ ≤
      cost s + cost (R.fire c) + cost (R.fire a)*‖Y.part (R.fire b)‖ +
        ‖T.part (R.fire a)‖*cost (R.fire b) := by
  rw [identity Y T quiet a b c s h pair]
  let D := Order.logTo (Fintype.card V) Y-T
  calc
    _ ≤ ‖D.part s - D.part (R.fire c) + D.part (R.fire a)*Y.part (R.fire b)‖ +
        ‖T.part (R.fire a)*D.part (R.fire b)‖ := norm_add_le _ _
    _ ≤ (‖D.part s - D.part (R.fire c)‖ + ‖D.part (R.fire a)*Y.part (R.fire b)‖) +
        ‖T.part (R.fire a)*D.part (R.fire b)‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := by
      rw [norm_mul,norm_mul]
      apply add_le_add
      · exact add_le_add ((norm_sub_le _ _).trans (add_le_add (paid s (by simp)) (paid (R.fire c) (by simp))))
          (mul_le_mul_of_nonneg_right (paid (R.fire a) (by simp)) (norm_nonneg _))
      · exact mul_le_mul_of_nonneg_left (paid (R.fire b) (by simp)) (norm_nonneg _)

end YM.Integration.WilsonReceivedCenteredMoment
