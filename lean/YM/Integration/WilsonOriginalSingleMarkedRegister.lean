import YM.Integration.WilsonOriginalRegisteredRawPage

/-! The literal occupied coefficient of an unnormalized finite Wick log with one active source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSingleMarkedRegister
open Function Finset Marker Multi PowerSeries Comparison.RG02 Comparison.RG02.Order
open Integration.WilsonVacuumPreResetFiniteRegister
open PertExtension.Series Extra.Trajectories
open scoped Classical BigOperators
variable {V:Type}[Fintype V][DecidableEq V](J:Census V)(r:ℕ)

def token (i:J.Mode) : Grade J r := Join.injectLeft J (indices r) (Poly.send i 1)

theorem clean (P:PowerSeries ℝ) : bottom J r (register J r P)=register J r P :=by
  apply Join.both_parts
  intro t u
  by_cases h:t=J.quiet
  · subst t;rw [bottom_value,if_pos rfl]
  · rw [bottom_value,if_neg h,WilsonVacuumPreResetFiniteRegister.read,if_neg h,mul_zero]

theorem token_read (i t:J.Mode)(u:Index r)(A:Grade J r)(vac:bottom J r A=A) :
    (token J r i*A).part (Join.pair t u) =
      (if t=i then A.part (Join.pair J.quiet u) else 0) :=by
  have eq:token J r i*A=token J r i*(bottom J r A) :=by rw [vac]
  rw [eq,token,bottom,AlgHom.comp_apply,Join.separate,Poly.part_send]
  change (if t=i then (1:ℂ) else 0)*A.part (Join.pair J.quiet u) = _
  split <;> simp

private theorem quiet (i:J.Mode)(hi:i.val.Nonempty)(A:Grade J r):
    (token J r i * A).part (Board J r).quiet=0:=by
  have hn:J.quiet≠i:=fun he=>hi.ne_empty (congrArg Subtype.val he.symm)
  rw [Poly.quiet_mul,token,Join.inject_left_quiet,Poly.part_send,if_neg hn,zero_mul]

private theorem squared (i:J.Mode)(hi:i.val.Nonempty)(A:Grade J r):
    (token J r i*A)^2=0:=by
  have h:(Poly.send i (1:ℂ))^2=0:=by
    rw [pow_two];by_contra bad
    obtain ⟨t,hmeet,_⟩:=merges_of_tagged_mul bad
    obtain ⟨v,hv⟩:=hi
    exact Finset.disjoint_left.mp hmeet hv hv
  rw [mul_pow,token,←map_pow,h,map_zero,zero_mul]

theorem exponential (i:J.Mode)(hi:i.val.Nonempty)(A:Grade J r)(P:PowerSeries ℝ)(hP:constantCoeff P=0):
    Poly.pass (register J r P+token J r i*A) =
      register J r (WilsonCoeffUV.Blue.raiseE P)*(1+ token J r i*A) :=by
  have vacant:(register J r P).part (Board J r).quiet=0:=by
    rw [←Join.pair_quiet,WilsonVacuumPreResetFiniteRegister.read]
    have hm: ((indices r).quiet.val.card : ℕ) = 0 := rfl
    rw [hm,if_pos rfl,coeff_zero_eq_constantCoeff_apply,hP];simp
  rw [pass_add vacant (quiet J r i hi A),←WilsonVacuumPreResetFiniteRegister.exponential J r P hP]
  congr 1
  letI : Module ℚ (Grade J r) := Module.compHom _ (algebraMap ℚ ℂ)
  let b:=token J r i*A
  have he:IsNilpotent.exp b=Poly.pass b:=by
    rw [IsNilpotent.exp_eq_sum (Poly.stops b (quiet J r i hi A) _ (Nat.lt_succ_self _))]
    apply sum_congr rfl
    intro n _
    change (algebraMap ℚ ℂ ((n.factorial:ℚ)⁻¹)) • (b^n) = _
    simp
  rw [←he,IsNilpotent.exp_eq_sum (squared J r i hi A)]
  simp [sum_range_succ]

end YM.Integration.WilsonOriginalSingleMarkedRegister
