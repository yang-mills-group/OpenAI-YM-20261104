import YM.Integration.WilsonOriginalMicroscopicEntrancePooledCutoff
import YM.Integration.WilsonAddressedFiniteGuardTrial

/-! The complete true three-column cutoff hearing is the directly charged cutoff minus the declared physical socket. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntrancePooledSocket
open MeasureTheory Lattice RG Source Wilson Labels PhysicalNext.Repeat.Legato
open Pert.Asymptotics RG16 RG16.Literal
open WilsonOriginalMicroscopicEntranceEarlier (face)
open WilsonOriginalMicroscopicGuardedTrial (raw)
open WilsonOriginalMicroscopicEntranceGridRow (pin factor)
open WilsonOriginalMicroscopicEntranceTwoExits (originalRead)
open WilsonOriginalMicroscopicEntranceDoseGrid (mass)
open WilsonOriginalMicroscopicEntrancePooledCutoff (sourced)
open WilsonOriginalMicroscopicEntranceFiling (units supplied)
open WilsonAddressedFiniteGuardTrial (printed)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){N per f n:ℕ}
local notation "J" => Stock.census (Fin 3)
local notation "K" => f+n
local notation "fk" => Nat.le_add_right f n
local notation "X" j:max => Config G (R.family.side j per)
variable (live:f+n≤N)(Y:∀a:Fin 3,R.family.label (d a))(o:Fin 3→Site (R.family.side f per))
  (v:∀a:Fin 3,R.family.label (d a))(s:(J).Mode)(c:Fin 3→ℂ)
local notation "slots" => pin R fk o
local notation "tops" => pin R ((fk).trans live) o
local notation "lit₀" => WilsonOriginalAlternativeFiniteSource.fired (V:=Fin 3)
local notation "z₀" => fun a=>c a*factor R d K a
local notation "file" => printed R d (N:=N) slots v z₀ lit₀ s
local notation "m" => mass c s

include live in
theorem filed (U:X K):
    file U=m*(units R d K s*face (raw R d N per K slots v) s U):=by
  unfold printed mass units face
  rw [←Finset.prod_mul_distrib,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a _
  change _=c a*(factor R d K a*WilsonPositionProgramBlockedTrialAddBack.uncut R (d a) N per K (slots a) (v a) U)
  rw [WilsonPositionProgramBlockedTrialFiling.filed R (d a) N per K live (slots a) (v a) U,←mul_assoc,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp only [WilsonAddressedFiniteGuardTrial.submitted,WilsonOriginalAlternativeFiniteSource.fired,one_mul,
    WilsonPositionProgramReportedField.entire,gMap,Frame.scaled_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem original {u:ℕ}(uf:u≤f)(W:X u):
    m*originalRead R d live Y o v s uf W=
      actualTransport R.family (N:=N) (sourced R d live Y o s c) (uf.trans ((fk).trans live)) W-
      actualTransport R.family (N:=N) file (uf.trans fk) W:=by
  let fin:=raw R d N per K slots v
  have physical:=WilsonOriginalMicroscopicEntranceFiling.original R d Y tops live fin
    (fun i=>(supplied R d (N:=N) slots v i).2) (uf.trans fk) s W
  change originalRead R d live Y o v s uf W=_ at physical
  have old:sourced R d live Y o s c=fun U=>m*(∏a∈s.val,R.family.O N per (Y a) (tops a) U):=by
    funext U
    exact Finset.prod_mul_distrib
  have elected:file=fun U=>m*(units R d K s*face fin s U):=funext (filed R d live o v s c)
  simp only [physical,old,elected,WilsonMeasuredPublicEntranceGridCurrency.transport,mul_sub]
end YM.Integration.WilsonOriginalMicroscopicEntrancePooledSocket
end
