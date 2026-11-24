import YM.Integration.WilsonReceivedDepositedOrbitalFixedLabels

/-! A submitted source weight is charged once per original binder at every actual page assignment. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalNameWages
open Finset Lattice Wilson Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalCensusCopyGraphs
open WilsonReceivedDepositedOrbitalFixedLabels (name whole home)
open scoped Classical BigOperators

variable {I U β:Type}[DecidableEq I][DecidableEq U][CommMonoid β]
theorem booked (s:Finset I)(p:s→U)(w:I→β):
    (∏a:graph s p,w a.val.1)=∏i∈s,w i:=by
  calc
    _=∏j∈(univ:Finset (graph s p)).map (name s p),w j:=by rw [prod_map];rfl
    _=_:=by rw [whole]

def central (f:Side):Fin (Pages f f):=⟨0,by simp [Pages]⟩

theorem on_board {I:Type}(f:Side)(s:Finset I)(v:(s→Fin (Pages f f))→ℂ):
    ∑p:s→Fin (Pages f f),v p=v (fun _=>central f):=by
  have count:Pages f f=1:=by simp [Pages]
  have only (p:s→Fin (Pages f f)):p=(fun _=>central f):=by
    funext i
    apply Fin.ext
    have number:=(p i).isLt
    change (p i).val=0
    omega
  calc
    _=∑_p:s→Fin (Pages f f),v (fun _=>central f):=sum_congr rfl (fun p _=>congrArg v (only p))
    _=_:=by simp [count]

end YM.Integration.WilsonReceivedDepositedOrbitalNameWages
end
