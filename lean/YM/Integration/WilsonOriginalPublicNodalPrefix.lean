import YM.Integration.WilsonOriginalPublicNodalCommonRaw
import YM.RegulatorIR.Older.Trunk

/-! Request-local agreement through the genuine deposited quiet and every angular row on a shared prefix. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalPrefix
open Lattice RG Source Labels PertExtension XSpace
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Prim
open RegulatorIR.Profiles RegulatorIR.Cluster RegulatorIR.Budget.Packet RegulatorIR.Budget.Layer RegulatorIR.Gain
open RegulatorIR.Halo RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Older
open WilsonIndependentRawRosterOrbit (report)
open WilsonOriginalPublicNodalCommonRaw (Court value)
open scoped Classical
variable {G:Gauge}{X X' I:Type}{p p':ℕ}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
    (σ:I → Bool)(d:I → ℕ)(key:∀i,(R.family.labels.level (d i)).Index)(arms:Composite I)
    (A:Court G X p)(B:Court G X' p')(j:Choice A.M)(k:Choice B.M)(w:X)(w':X')
    (sites:X → I → Cover)(homes:X' → I → Cover)

theorem program (joint:Overlap A.V B.V w w' j k)(birth:sites w=homes w')
    (t:ℕ)(a:t≤j.age w)(b:t≤k.age w'):
    (report R W σ d key arms A.T sites).main (briefly j w t a)=
      (report R W σ d key arms B.T homes).main (briefly k w' t b):=by
  let old:=report R W σ d key arms A.T sites
  let new:=report R W σ d key arms B.T homes
  induction t with
  | zero => change WilsonIndependentRawRosterWord.bank R W σ d key arms (sites w)=_
            rw [birth];rfl
  | succ t ih =>
    let f:=wingS j w t a
    let g:=wingS k w' t b
    change old.main f.next=new.main g.next
    rw [←old.step_m f,←new.step_m g,
      show old.main f.prev=new.main g.prev from ih (by omega) (by omega),
      show A.T.bulk f.prev=B.T.bulk g.prev from
        processes A.T B.T A.common A.funds.port B.common B.funds.port joint t (by omega) (by omega)]
    exact (sing A.common B.common joint t a b).marks ..

theorem scalar (joint:Overlap A.V B.V w w' j k)(birth:sites w=homes w')(q:ℕ):
    value R W σ d key arms A sites (j.choose w) q=value R W σ d key arms B homes (k.choose w') q:=by
  have eq:=program R W σ d key arms A B j k w w' sites homes joint birth (j.age w) le_rfl joint.atJ.le
  have atPage:briefly k w' (j.age w) joint.atJ.le=k.choose w':=by
    change (⟨w',j.age w,_⟩:Page B.M)=⟨w',k.age w',_⟩
    congr 1
    exact joint.atJ
  rw [atPage] at eq
  exact congrArg (fun z=>(note (z q 0):ℂ)) eq

end YM.Integration.WilsonOriginalPublicNodalPrefix
end
