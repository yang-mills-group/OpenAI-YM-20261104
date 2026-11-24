import YM.Integration.WilsonOriginalPublicNodalPrefixOperators

/-! Prefix restriction of the full genuine payroll and its nonlinear signed bank at a prescribed clock. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalPrefixFrame
open Lattice RG Source Labels PertExtension XSpace
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer RegulatorIR.Budget.Packet
open RegulatorIR.Profiles RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain RegulatorIR.Halo
open RegulatorIR.Oracle RegulatorIR.Older RegulatorIR.Taping RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open RegulatorIR.Calibration RegulatorIR.Uniform
open WilsonOriginalPublicNodalPrefixFree (Route)
open WilsonIndependentRawRosterOrbit (report)
open scoped Classical
variable {X X':Type}{M:X → ℕ}{M':X' → ℕ}{n:Page M → Side}{n':Page M' → Side}
    (C:Circuit M n)(D:Circuit M' n')(j:Choice M)(k:Choice M')(x:X)(y:X')
    (T:Route C D j k x y)(birth:C.l (Page.opening M x)=D.l (Page.opening M' y))
    {K:KernelChoices}(Y:Program K)(G:Gauge)(Z:∀P:Patch,P.Branches K G)(F:Tent M)(F':Tent M')
    (wage:∀t h h',sheet F (briefly j x t h)=sheet F' (briefly k y t h'))

include T birth wage in
theorem overlap:Overlap (C.lane Y G Z (sheet F)) (D.lane Y G Z (sheet F')) x y j k:=
  ⟨T.age,birth,wage,WilsonOriginalPublicNodalPrefixOperators.patch C D j k x y T,fun _ _ _=>rfl,
    WilsonOriginalPublicNodalPrefixOperators.mean C D j k x y T Y G,
    WilsonOriginalPublicNodalPrefixOperators.covariance C D j k x y T Y G Z⟩

include T birth wage in
theorem quiet (t:ℕ)(a:t≤j.age x)(b:t≤k.age y):
    (C.payroll Y G Z (sheet F)).bulk (briefly j x t a)=(D.payroll Y G Z (sheet F')).bulk (briefly k y t b):=
  processes _ _ (fun _=>rfl) (C.follows Y G Z (sheet F)) (fun _=>rfl) (D.follows Y G Z (sheet F'))
    (overlap C D j k x y T birth Y G Z F F' wage) t a b

variable {I:Type}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(σ:I → Bool)(d:I → ℕ)
    (key:∀i,(R.family.labels.level (d i)).Index)(arms:Composite I)
    (sites:X → I → Cover)(homes:X' → I → Cover)
include T birth wage in
theorem active (same:sites x=homes y)(t:ℕ)(a:t≤j.age x)(b:t≤k.age y):
    (report R W σ d key arms (C.payroll Y G Z (sheet F)) sites).main (briefly j x t a)=
      (report R W σ d key arms (D.payroll Y G Z (sheet F')) homes).main (briefly k y t b):=by
  let old:=report R W σ d key arms (C.payroll Y G Z (sheet F)) sites
  let new:=report R W σ d key arms (D.payroll Y G Z (sheet F')) homes
  induction t with
  | zero => change WilsonIndependentRawRosterWord.bank R W σ d key arms (sites x)=_
            rw [same];rfl
  | succ t ih =>
    let f:=wingS j x t a
    let g:=wingS k y t b
    change old.main f.next=new.main g.next
    rw [←old.step_m f,←new.step_m g,
      show old.main f.prev=new.main g.prev from ih (by omega) (by omega),
      show (C.payroll Y G Z (sheet F)).bulk f.prev=(D.payroll Y G Z (sheet F')).bulk g.prev from
        quiet C D j k x y T birth Y G Z F F' wage t (by omega) (by omega)]
    exact (sing (fun _=>rfl) (fun _=>rfl) (overlap C D j k x y T birth Y G Z F F' wage) t a b).marks ..

end YM.Integration.WilsonOriginalPublicNodalPrefixFrame
end
