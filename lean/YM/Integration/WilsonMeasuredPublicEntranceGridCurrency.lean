import YM.Integration.WilsonOriginalAlternativeTrialGrid
import YM.Integration.WilsonAddressedPublicGridRooms

/-! Carry a named scalar on the actual cutoff cylinder and the separately
guarded original trial, through their own finite Wilson conditionals. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceGridCurrency
open Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories MergeProof MergeProof.Accent
open PhysicalNext PhysicalNext.Repeat.Legato WilsonThermometerReflectedTrajectory
open WilsonMeasuredPublicEntranceGridDebit
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){f N K per:ℕ}

private theorem carried (S:History G)(N per top:ℕ)(a:ℂ)(F:Config G (S.S.side top per) → ℂ)
    {i:ℕ}(hi:i≤top):gust S N per top (a • F) i hi=a • gust S N per top F i hi:=by
  induction hi using Nat.decreasingInduction with
  | self=>simp only [gust_base]
  | of_succ i h ih=>
    rw [gust_step S N per top _ h,ih,gust_step S N per top F h]
    funext U
    simp only [StepData.push,Pi.smul_apply,smul_comm _ a,integral_smul]

theorem transport (a:ℂ)(F:Config G (R.family.side K per) → ℂ)(hi:f≤K)(U:Config G (R.family.side f per)):
    actualTransport R.family (N:=N) (fun T=>a*F T) hi U=a*actualTransport R.family (N:=N) F hi U:=by
  have eq : (fun T=>(R.family.path.rep N per K).eval T • (a*F T)) =
      a • (fun T=>(R.family.path.rep N per K).eval T • F T):=by
    funext T;simp only [Pi.smul_apply,smul_eq_mul,Complex.real_smul];ring
  rw [actualTransport,eq,carried,actualTransport]
  simp only [Pi.smul_apply,smul_eq_mul,Complex.real_smul]
  ring

theorem physical (d:ℕ)(Y:R.family.label d)(a:ℂ)(o:Site (R.family.side f per))(deep:f≤N)(U:Config G (R.family.side f per)):
    actualTransport R.family (N:=N) (fun T=>a*R.family.O N per Y (anchorAt R o N) T) deep U=
      a*actualTransport R.family (N:=N) (named R d f N per deep o Y) deep U:=by
  rw [WilsonAddressedPublicGridRooms.top R deep o]
  exact transport R a _ deep U

theorem trial {V:Type} (d:V→ℕ)(n:ℕ)(o:V → Site (R.family.side f per))(v:∀i,R.family.label (d i))
    (a:V→ℂ)(j:V)(U:Config G (R.family.side f per)):
    actualTransport R.family (N:=N)
      (WilsonOriginalAlternativeTrialSource.arm R d N per (f+n) (WilsonOriginalAlternativeTrialGrid.pins R per f n o)
        v (fun i=>a i*WilsonOriginalAlternativeTrialGrid.factor R d f n i) j) (Nat.le_add_right f n) U =
      a j*actualTransport R.family (N:=N) (WilsonMeasuredPublicEntranceGridDebit.trial R (d j) f n N per (o j) (v j)) (Nat.le_add_right f n) U:=by
  have eq: (WilsonOriginalAlternativeTrialSource.arm R d N per (f+n) (WilsonOriginalAlternativeTrialGrid.pins R per f n o)
        v (fun i=>a i*WilsonOriginalAlternativeTrialGrid.factor R d f n i) j)=
      fun T=>a j*WilsonMeasuredPublicEntranceGridDebit.trial R (d j) f n N per (o j) (v j) T:=by
    funext T
    rw [← WilsonOriginalAlternativeTrialGrid.guard R d N per f n o v j]
    exact mul_assoc _ _ _
  rw [eq,transport]

end YM.Integration.WilsonMeasuredPublicEntranceGridCurrency
end
