import YM.Integration.WilsonGraphCenteredFarBilinearCauchy

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedTwoClocks

open Function Filter Real PowerSeries Finset Continuation
open Register MS MS.Native MS.Land MS.Book MS.Book.Program
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Scale Dframe Reg.Point
open scoped BigOperators Classical

variable {G : Gauge} (N : Register.WilsonPrescription G)
  (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
  {simple : G.Simple} {P : MS.Land.Prescription (Press.portDeck G)}
  (H : Main.Match N simple M P true)
local notation "ψ" => GroupS.ψ N.criterion M (Teller.logNu 1)

/-- Each field coefficient and the kernel are still complete series at the moment of substitution. -/
def pulled (h : ℕ) (x : Scale.Stage 2) (q : Cn) (A B : Guard G h) (u v : Sec G h) : PowerSeries ℂ :=
  ∑ c : Fin 2 → Dime G h, tax A u (c 0) * tax B v (c 1) *
    Reg.Point.story (Program.substitute q (book N h 2 x)) (fun i => dime G h (c i))

private theorem terms (h : ℕ) (x : Scale.Stage 2) (q : Cn) (hq : Rooted q)
    (A B : Guard G h) (u v : Sec G h) :
    (AppointedBilinearCauchy.full N h x A B u v).subst q =
      ∑ c : Fin 2 → Dime G h, (tax A u (c 0)).subst q * (tax B v (c 1)).subst q *
        Reg.Point.story (Program.substitute q (book N h 2 x)) (fun i => dime G h (c i)) := by
  have ok : HasSubst (S:=ℂ) q := HasSubst.of_constantCoeff_zero' ((coeff_zero_eq_constantCoeff_apply _).symm.trans hq)
  unfold AppointedBilinearCauchy.full
  simp only [Reg.Point.moves _ _ hq, ←coe_substAlgHom ok, map_sum, map_mul]

private theorem unit (h : ℕ) (u : Sec G h) (b : Dime G h) :
    tax (1 : Guard G h) u b = PowerSeries.C ((dime G h).repr u b) := by
  refine PowerSeries.ext fun j => ?_
  simp only [tax, coeff_mk, coeff_one, coeff_C]
  by_cases hj : j=0
  · subst j; rfl
  · simp [hj]

include H in
theorem twice (h : ℕ) (x : Scale.Stage 2) (s : ℝ) (u v : Sec G h) :
    pulled N h x (ψ (-s)) (AppointedCenteredReverse.reverseSeries N M h s)
        (AppointedCenteredReverse.reverseSeries N M h s) u v =
      (AppointedBilinearCauchy.full N h x (Kseries N M h s) (Kseries N M h s) u v).subst (ψ (-s)) := by
  rw [terms N _ _ _ ((H.dilation (Teller.logNu 1)).check.led (-s)).start]
  unfold pulled
  simp only [AppointedBilinearCauchy.reverseField N M H]

include H in
theorem once (h : ℕ) (x : Scale.Stage 2) (s : ℝ) (u v : Sec G h) :
    pulled N h x (ψ (-s)) (AppointedCenteredReverse.reverseSeries N M h s) 1 u v =
      (AppointedBilinearCauchy.full N h x (Kseries N M h s) 1 u v).subst (ψ (-s)) := by
  rw [terms N _ _ _ ((H.dilation (Teller.logNu 1)).check.led (-s)).start]
  unfold pulled
  simp only [AppointedBilinearCauchy.reverseField N M H, unit, subst_C]
  rfl

include H in
/-- The two r-born slots at the far geometry recover the very same near-stage correlation. -/
theorem original (h : ℕ) (x : Scale.Stage 2) (s : ℝ) (u v : Sec G h) :
    pulled N h (Facets.posing s x) (ψ (-s)) (AppointedCenteredReverse.reverseSeries N M h s)
        (AppointedCenteredReverse.reverseSeries N M h s) u v = Reg.Point.story (book N h 2 x) ![u,v] := by
  let law := (H.dilation (Teller.logNu 1)).check
  have rooted (a : ℝ) : HasSubst (S:=ℂ) (ψ a) := HasSubst.of_constantCoeff_zero'
    ((coeff_zero_eq_constantCoeff_apply _).symm.trans (law.led a).start)
  have invert : (ψ s).subst (ψ (-s)) = X := by
    have c := (law.toTouched.additive (-s) s).1
    simpa only [neg_add_cancel, law.toTouched.ground.1] using c.symm
  rw [twice N M H, AppointedBilinearCauchy.equivariant N M H,
    Reg.Point.moves _ _ (law.led s).start, subst_comp_subst_apply (rooted s) (rooted (-s)), invert, X_subst]

end YM.FVA2.GradedFar.AppointedTwoClocks
