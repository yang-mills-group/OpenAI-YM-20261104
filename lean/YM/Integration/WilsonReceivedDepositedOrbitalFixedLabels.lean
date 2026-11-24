import YM.Integration.WilsonOriginalCensusCopyGraphs
import YM.Integration.WilsonOriginalCensusChildPages

/-! A page assignment has one genuine lifted site per occupied binder. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalFixedLabels
open Finset Lattice RG Wilson
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalCensusCopyGraphs
open scoped Classical BigOperators
variable {I U:Type}[DecidableEq I][DecidableEq U](s:Finset I)(p:s→U)

def name:(graph s p)↪I where
  toFun j:=j.val.1
  inj' u v eqn:=Subtype.ext (one s p u.property v.property eqn)

theorem whole:(Finset.univ:Finset (graph s p)).map (name s p)=s:=by
  ext v
  simp only [Finset.mem_map,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨j,rfl⟩
    exact (member.mp j.property).choose
  · intro hv
    exact ⟨⟨(v,p ⟨v,hv⟩),member.mpr ⟨hv,rfl⟩⟩,rfl⟩

variable {f F:Side}(h:f.val∣F.val)(z:I→Site f)(pages:s→Fin (Pages f F))
def home (l:I):Cover:=
  if owned:l∈s then Lattice.lift (page h (z l) (pages ⟨l,owned⟩)).val else 0

theorem attached (u:graph s pages):
    home s h z pages (name s pages u)=Lattice.lift (page h (z u.val.1) u.val.2).val:=by
  obtain ⟨du,slot⟩:=member.mp u.property
  change (if owned:u.val.1∈s then Lattice.lift (page h (z u.val.1) (pages ⟨u.val.1,owned⟩)).val else 0)=_
  rw [dif_pos du,slot]

end YM.Integration.WilsonReceivedDepositedOrbitalFixedLabels
end
