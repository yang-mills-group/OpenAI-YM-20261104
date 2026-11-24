import YM.Integration.WilsonIndependentRawRosterOrbit
import YM.RegulatorIR.Profiles.Chance

/-! Translation of a complete submitted word through the actual strides of its funded orbit. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalOrbitShift
open Function Lattice RG Source Labels Gauge PertExtension XSpace
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Budget.Packet RegulatorIR.Profiles RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain
open RegulatorIR.Halo RegulatorIR.Taping RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Step
open RegulatorIR.Motion RegulatorIR.Uniform
open WilsonIndependentRawRosterOrbit (report)
open WilsonIndependentRawRosterWord (body bank degree enrolled)
open scoped Classical
variable {G:Gauge}{J I:Type}{M:J→ℕ}{n:Page M→Side}{S:Heir n G}(V:Reel S)

def stride (j:Page M):Cover → Cover:=
  seriesC (X:=fun _=>Cover → Cover) (fun _=>id) (fun w r t=>r (strideR (V.steps w) t)) j

theorem opening (w:J)(t:Cover):stride V (Page.opening M w) t=t:=rfl

theorem next (w:Flap M)(t:Cover):stride V w.next t=stride V w.prev (strideR (V.steps w) t):=by
  unfold stride
  rw [laterC]

theorem length (j:Page M)(t:Cover):slide (S.ε j.bindW) (stride V j t)=slide (S.l j) t:=by
  apply Page.proves (g:=fun p=>∀v,slide (S.ε p.bindW) (stride V p v)=slide (S.l p) v) (fun _ _=>rfl) _ j t
  intro w ih v
  rw [next,indentX V]
  exact ih _

variable (R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(σ:I→Bool)(d:I→ℕ)
    (key:∀i,(R.family.labels.level (d i)).Index)(arms:Composite I)

theorem translated (sites:I → Cover)(t:Cover):
    body R W σ d key arms (fun i=>sites i+t)=convey t (body R W σ d key arms sites):=by
  induction arms with
  | atom i =>
    funext u X
    apply congrArg ((WilsonIndependentRawNamedStencil.brand R W (σ i) (d i) (key i)) u)
    exact funext fun v=>by simp [Lattice.translate,add_assoc]
  | pair a b ha hb =>
    change body R W σ d key a _*body R W σ d key b _=_
    rw [ha,hb]
    rfl

variable {T:S.Accounts}
theorem filed (sites homes:J→I → Cover)(pass:Passage V)(common:Common V)(follows:V.Follows T):
    ∀(j:Page M)(t:Cover), (∀i,homes j.bindW i=sites j.bindW i+stride V j t) →
      ∀e r,Echos (carryX t)
        ((report R W σ d key arms T sites).main j e r)
        ((report R W σ d key arms T homes).main j e r):=by
  let A:=report R W σ d key arms T sites
  let B:=report R W σ d key arms T homes
  refine Page.proves (g:=fun j=>∀t:Cover,(∀i,homes j.bindW i=sites j.bindW i+stride V j t)→
    ∀e r,Echos (carryX t) (A.main j e r) (B.main j e r)) ?_ ?_
  · intro w t placed
    have hsites:homes w=fun i=>sites w i+t:=funext placed
    have offered:body R W σ d key arms (homes w)=convey t (body R W σ d key arms (sites w)):=by
      rw [hsites,translated]
    have H:=enrolled R W σ d key arms (homes w)
    have Q:=enrolled R W σ d key arms (sites w)
    have peer:=Q.1.vayne t
    rw [offered] at H
    have price:=certifies H.1 peer H.2 (fun e r live=>Q.2 e r (fun hz=>live (by rw [hz,echo_zero])))
    intro e r
    change Echos (carryX t) _ (bank R W σ d key arms (homes w) e r)
    rw [price]
    exact echos _ _
  · intro w ih t placed e r
    rw [←A.step_m w,←B.step_m w]
    have prev:∀i,homes w.prev.bindW i=sites w.prev.bindW i+stride V w.prev (strideR (V.steps w) t):=by
      intro i
      rw [←next]
      exact placed i
    exact flames (carryX (strideR (V.steps w) t)) (carryX t) (pass.cells common follows w.prev _)
      (pass.levels w t).1 (pass.levels w t).2 (Passage.assets common w t) (ih _ prev) e r

theorem scalar (sites homes:J→I → Cover)(pass:Passage V)(common:Common V)(follows:V.Follows T)
    (j:Page M)(t:Cover)(placed:∀i,homes j.bindW i=sites j.bindW i+stride V j t)(q:ℕ):
    note ((report R W σ d key arms T homes).main j q 0)=note ((report R W σ d key arms T sites).main j q 0):=by
  have h:=filed V R W σ d key arms sites homes pass common follows j t placed q 0 Fin.elim0
  rwa [Subsingleton.elim (onPath _ _) (Fin.elim0:Tuple _ 0)] at h

end YM.Integration.WilsonOriginalPublicNodalOrbitShift
end
