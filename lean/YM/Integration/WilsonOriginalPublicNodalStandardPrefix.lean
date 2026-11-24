import YM.Integration.WilsonOriginalPublicNodalPrefixFree
import YM.Integration.WilsonOriginalPublicNodalHelperCircuit

/-! The actual two-length Wilson sample and the temporary grouped sample share every funded initial flap. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalStandardPrefix
open Lattice RG XSpace RegulatorIR RegulatorIR.Oracle RegulatorIR.Older RegulatorIR.Ledger
open WilsonIndependentExactPlate (Requests M S)
open WilsonOriginalPublicNodalHelperShape (length)
open WilsonOriginalPublicNodalHelperCircuit (circuit)
open WilsonOriginalPublicNodalPrefixFree (Route)
open scoped Classical
variable {X:Type}(V:Run)(E r:X → ℕ)(a k:ℕ)(pos:0<a)(late:4≤k)
    (j:Choice (M V a))(l:Choice (length E r a))(i:Requests a)(x:X)
local notation "C" => S V a pos k late
local notation "D" => circuit V E r a k pos late

theorem route (age:j.age i=l.age x)(residue:i.val%a=r x):Route C D j l i x:=by
  refine ⟨age,fun _ _ _=>rfl,?_⟩
  intro t ht hs
  change WilsonIndependentEvenPassport.power V (if t=0 then a+i.val%a else a)=
    WilsonIndependentEvenPassport.power V (if t=0 then a+r x else a)
  rw [residue]

theorem root:(C).l (Page.opening _ i)=(D).l (Page.opening _ x):=by
  have left:0<(V.step i.val).p.side.val:=(V.step i.val).p.side.pos
  have right:0<(WilsonOriginalPublicNodalHelperShape.n V E r a (Page.opening _ x)).val:=
    (WilsonOriginalPublicNodalHelperShape.n V E r a (Page.opening _ x)).pos
  change ((V.step i.val).p.side.val:ℝ)/(WilsonIndependentExactPlate.n V a (Page.opening _ i)).val=
    ((WilsonOriginalPublicNodalHelperShape.n V E r a (Page.opening _ x)).val:ℝ)/
    (WilsonOriginalPublicNodalHelperShape.n V E r a (Page.opening _ x)).val
  rw [WilsonIndependentExactPlate.starting]
  simp [Nat.ne_of_gt left,Nat.ne_of_gt right]

end YM.Integration.WilsonOriginalPublicNodalStandardPrefix
end
