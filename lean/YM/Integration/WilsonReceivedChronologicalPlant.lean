import YM.Integration.WilsonReceivedChronologicalReadout
import YM.Integration.WilsonOriginalMicroscopicEntrancePooledBoard

/-! The complete deposited canonical trial at its true birth date, with the old vacuum from N. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalPlant
open Finset MeasureTheory Lattice RG Wilson Marker
open Extra.Histories Extra.Histories.Relay MergeProof Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat.Legato
open WilsonOriginalMicroscopicEntranceGridRow (pin factor)
open WilsonOriginalMicroscopicEntranceDoseGrid (mass)
open WilsonOriginalMicroscopicGuardedTrial (raw)
open WilsonOriginalMicroscopicEntranceFiling (print supplied)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){N per f n:ℕ}
local notation "J" => Stock.census (Fin 3)
local notation "K" => f+n
local notation "fk" => Nat.le_add_right f n
local notation "X" j:max => Config G (R.family.side j per)
variable (o:Fin 3→Site (R.family.side f per))(v:∀a:Fin 3,R.family.label (d a))(c:Fin 3→ℂ)
local notation "src" => raw R d N per K (pin R fk o) v

def top (U:X K):Poly J:=fun s=>mass c s*(print R d (N:=N) (src) U).part s

/-- All faces enter on the same old vacuum, including the unmarked face and all deposited constants. -/
def rows (past:∀j,X j→Poly J):∀j,X j→Poly J:=Function.update past K (top R d (n:=n) (N:=N) o v c)

theorem live (active:K≤N):Integrable (top R d (n:=n) (N:=N) o v c) (prior G _):=by
  have z:=WilsonOriginalMicroscopicEntranceFiling.bill R d active (src)
    (fun a=>(supplied R d (N:=N) (pin R fk o) v a).2)
  apply integrable_pi_iff.mpr
  intro s
  exact (((Poly.get s).restrictScalars ℝ).integrable_comp z).const_mul _

theorem lower (past:∀j,X j→Poly J){j:ℕ}(old:j<K):rows R d (n:=n) (N:=N) o v c past j=past j:=
  Function.update_of_ne old.ne _ _

theorem filed (active:K≤N)(past:∀j,X j→Poly J)(s:(J).Mode):
    WilsonReceivedChronologicalReadout.face R N per (rows R d (n:=n) (N:=N) o v c past) s K=
      WilsonAddressedFiniteGuardTrial.printed R d (N:=N) (pin R fk o) v (fun a=>c a*factor R d K a)
        WilsonOriginalAlternativeFiniteSource.fired s:=by
  funext U
  have nonzero:((R.family.path.rep N per K).eval U:ℂ)≠0:=
    Complex.ofReal_ne_zero.mpr (Multi.AxisShift.chosen_positive R.makes.wilson active U).ne'
  rw [WilsonOriginalMicroscopicEntrancePooledSocket.filed R d active o v s c U]
  simp only [WilsonReceivedChronologicalReadout.face,rows,Function.update_self,top,Poly.part,print,Complex.real_smul]
  field_simp [nonzero]

end YM.Integration.WilsonReceivedChronologicalPlant
end
