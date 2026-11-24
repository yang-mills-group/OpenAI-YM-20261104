import YM.Integration.WilsonOriginalMicroscopicEntrancePooledSocket
import YM.Integration.WilsonOriginalMicroscopicEntranceDoseElected

/-! Restore the complete earlier normalized physical hearing of the previously registered public board. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntrancePooledBoard
open Finset MeasureTheory Lattice RG Wilson Source Labels PhysicalNext.Repeat.Legato
open WilsonThermometerReflectedTrajectory (anchorAt)
open WilsonOriginalMicroscopicEntranceGridRow (factor pin)
open WilsonOriginalMicroscopicEntranceDoseBoard (Board source)
open WilsonOriginalMicroscopicEntranceTwoExits (originalRead)
open WilsonOriginalMicroscopicEntranceDoseGrid (mass)
open WilsonAddressedFiniteGuardTrial (printed)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){N per f n t:ℕ}
variable {o:Fin 3→Site (R.family.side f per)}(B:Board R d N per f o t)
local notation "J" => Stock.census (Fin 3)
local notation "K" => f+n
local notation "fk" => Nat.le_add_right f n
local notation "X" j:max => Config G (R.family.side j per)
variable (live:f+n≤N)(v:∀a:Fin 3,R.family.label (d a))(s:(J).Mode)(c:Fin 3→ℂ)
local notation "z₀" => fun a=>c a*factor R d K a
local notation "file" => printed R d (N:=N) (pin R fk o) v z₀ WilsonOriginalAlternativeFiniteSource.fired s
local notation "m" => mass c s

def actual (U:X N):ℂ:=∏a∈s.val,c a*R.family.O N per (source R B a) (anchorAt R (o a) N) U

theorem joined {u:ℕ}(uf:u≤f)(W:X u):
    m*originalRead R d live (source R B) o v s uf W=
      actualTransport R.family (N:=N) (actual R d B s c) (uf.trans ((fk).trans live)) W-
      actualTransport R.family (N:=N) file (uf.trans fk) W:=by
  have name:actual R d B s c=WilsonOriginalMicroscopicEntrancePooledCutoff.sourced R d live (source R B) o s c:=by
    funext U
    unfold actual WilsonOriginalMicroscopicEntrancePooledCutoff.sourced
    simp only [WilsonAddressedPublicGridRooms.top R B.live.le,pin]
  rw [name]
  exact WilsonOriginalMicroscopicEntrancePooledSocket.original R d live (source R B) o v s c uf W

theorem original (nz:∀a,c a≠0)(r:Fin 3→ℝ)(positive:∀a,0≤r a){u:ℕ}(uf:u≤f)(W:X u)
    {fee:ℝ}(paid:‖actualTransport R.family (N:=N) (actual R d B s c) (uf.trans ((fk).trans live)) W-
      actualTransport R.family (N:=N) file (uf.trans fk) W‖≤fee):
    (∏i∈s.val,(r i)^(d i))*‖originalRead R d live (source R B) o v s uf W‖≤
      (∏i∈s.val,(r i)^(d i)*‖(c i)⁻¹‖)*fee:=by
  have balance:=joined R d B live v s c uf W
  have ne:m≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>nz i)
  rw [←balance,norm_mul] at paid
  have unwind:=mul_le_mul_of_nonneg_left paid (norm_nonneg m⁻¹)
  rw [←mul_assoc,←norm_mul,inv_mul_cancel₀ ne,norm_one,one_mul] at unwind
  have outward:(∏i∈s.val,(r i)^(d i)*‖(c i)⁻¹‖)=(∏i∈s.val,(r i)^(d i))*‖m⁻¹‖:=by
    rw [Finset.prod_mul_distrib,mass,←Finset.prod_inv_distrib,norm_prod]
  rw [outward,mul_assoc]
  exact mul_le_mul_of_nonneg_left unwind (Finset.prod_nonneg (fun i _=>pow_nonneg (positive i) _))
end YM.Integration.WilsonOriginalMicroscopicEntrancePooledBoard
end
