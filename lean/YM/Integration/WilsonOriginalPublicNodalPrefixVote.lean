import YM.Integration.WilsonOriginalPublicNodalPrefixCut

/-! A separately tuned notebook on the same prefix has identical measured marked jets through the paid order. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalPrefixVote
open Lattice RG Source Labels PertExtension XSpace
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer RegulatorIR.Budget.Packet
open RegulatorIR.Profiles RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain RegulatorIR.Halo
open RegulatorIR.Oracle RegulatorIR.Older RegulatorIR.Taping RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open RegulatorIR.Calibration RegulatorIR.Uniform RegulatorIR.Clocks RegulatorIR.FVAAlt2
open WilsonIndependentRawRosterOrbit (report)
open WilsonOriginalPublicNodalPrefixFree (Route)
open WilsonOriginalPublicNodalPrefixCut (height last into cut clock own)
open scoped Classical
variable {G:Gauge}{I X X':Type}{M:X → ℕ}{M':X' → ℕ}{n:Page M → Side}{n':Page M' → Side}
    (C:Circuit M n){K:KernelChoices}(Y:Program K)(Z:∀P:Patch,P.Branches K G)(col:G.ColorIndex)
    (F F':Tent M){p:ℕ}
    (one:Notebook C Y G Z col (Rocket.native _) F p)(two:Notebook C Y G Z col (Rocket.native _) F' p)
    (R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(σ:I → Bool)(d:I → ℕ)
    (key:∀i,(R.family.labels.level (d i)).Index)(arms:Composite I)(sites:X → I → Cover)

include one two in
theorem record {grade:ℕ}(A:(C.payroll Y G Z (sheet F)).Report grade)
    (B:(C.payroll Y G Z (sheet F')).Report grade)
    (start:∀w,Matches p (A.main (Page.opening _ w)) (B.main (Page.opening _ w))):
    ∀a,Matches p (A.main a) (B.main a):=by
  refine Page.proves (g:=fun a=>Matches p (A.main a) (B.main a)) start ?_
  intro f ih
  rw [←A.step_m f,←B.step_m f]
  have h:=recognized C Y G Z col one two f.prev
  have step:=slims C Y G Z (sheet F) f h
  exact step.wave_step (uniques C Y G Z col one two f.prev) ih

include one two in
theorem measured (a:Page M):
    Matches p ((report R W σ d key arms (C.payroll Y G Z (sheet F)) sites).main a)
      ((report R W σ d key arms (C.payroll Y G Z (sheet F')) sites).main a):=by
  let A:=report R W σ d key arms (C.payroll Y G Z (sheet F)) sites
  let B:=report R W σ d key arms (C.payroll Y G Z (sheet F')) sites
  have start (w:X):A.main (Page.opening _ w)=B.main (Page.opening _ w):=by
    change WilsonIndependentRawRosterWord.bank R W σ d key arms (sites w)=_
    rfl
  exact record C Y Z col F F' one two A B (fun w q _=>congrFun (start w) q) a

end YM.Integration.WilsonOriginalPublicNodalPrefixVote
end
