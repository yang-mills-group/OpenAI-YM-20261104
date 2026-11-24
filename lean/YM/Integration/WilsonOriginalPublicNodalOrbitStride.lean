import YM.Integration.WilsonOriginalPublicNodalSafeCopies

/-! The spatial deck group at an actual page is the integer product of all of its elapsed block sizes. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalOrbitStride
open Lattice RegulatorIR RegulatorIR.Halo RegulatorIR.Geometry RegulatorIR.Budget RegulatorIR.Motion
open RegulatorIR.Halo RegulatorIR.Binding RegulatorIR.Profiles RegulatorIR.Gain RegulatorIR.Cluster RegulatorIR.Budget.Layer RegulatorIR.Budget.Packet RegulatorIR.Taping
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Prim RegulatorIR.Uniform
open WilsonOriginalPublicNodalOrbitShift (stride)
open scoped Classical
variable {G:Gauge}{X:Type}{M:X → ℕ}{n:Page M → Side}{S:Heir n G}(V:Reel S)

def blocks (j:Page M):ℕ:=seriesC (X:=fun _=>ℕ) (fun _=>1)
  (fun e p=>p*(V.steps e).patch.L.val) j

theorem positive (j:Page M):0<blocks V j:=by
  apply Page.proves (g:=fun j=>0<blocks V j) (fun _=>Nat.zero_lt_one) _ j
  intro e ih
  rw [blocks,laterC]
  exact Nat.mul_pos ih (V.steps e).patch.L.pos

theorem actual (j:Page M)(t:Cover):stride V j t=blocks V j • t:=by
  apply Page.proves (g:=fun j=>∀t,stride V j t=blocks V j • t) (fun x t=>by
    change t=(1:ℕ) • t
    rw [one_smul]) _ j t
  intro e ih t
  rw [WilsonOriginalPublicNodalOrbitShift.next,ih,show blocks V e.next=blocks V e.prev*(V.steps e).patch.L.val from laterC e]
  change blocks V e.prev • ((V.steps e).patch.L.val • t)=(blocks V e.prev*(V.steps e).patch.L.val) • t
  rw [mul_smul]

end YM.Integration.WilsonOriginalPublicNodalOrbitStride
end
