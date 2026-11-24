import YM.Integration.WilsonOriginalMicroscopicEntranceFiling
import YM.Integration.WilsonOriginalMicroscopicGuardedVerseBalance

/-! The entrance in the signed physical corridor, on the jointly selected bare
offer and the fully expanded fixed-socket K print at its actual engineering units. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceSockets
open MergeProof MergeProof.Accent MergeProof.East MergeProof.Replicums RG05Readout.Records
open Function Finset MeasureTheory Lattice Wilson RG Source Labels Marker Push OPE.Therm
open Extra.Histories Extra.Trajectories PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Carp
open WilsonPointChildFiledPress OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonOriginalMicroscopicEntranceDeposits (funded)
open WilsonOriginalMicroscopicEntranceEarlier (face salary)
open WilsonOriginalMicroscopicEntranceFiling (units print supplied)
open WilsonOriginalMicroscopicGuardedTrial (raw guarded footprint gap)
open WilsonOriginalMicroscopicGuardedVerseBalance (printed)
open WilsonReceivedCanonicalSocketPost (lit)
open private scale from YM.Integration.WilsonThermometerOccupiedLinear
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N p K:ℕ}
local notation "J" => Stock.census (Fin 3)
local notation "X" i:max => Config G (R.family.side i p)

theorem scaled (live:K≤N){u:ℕ}(step:u≤K)(F:X K→ℂ)(paid:funded F)(c:ℂ)(W:X u):
    actualTransport R.family (N:=N) (fun U=>c*F U) step W=c*actualTransport R.family (N:=N) F step W:=by
  obtain ⟨m,M,bound⟩:=paid
  let H:=fun U:X K=>(R.family.path.rep N p K).eval U • F U
  have bill:Integrable H (prior G _):=by
    have known:=actualTransport_weighted_integrable R.family R.makes live m.aestronglyMeasurable bound (le_rfl:K≤K)
    rwa [actualTransport_base R.family R.makes live] at known
  have input:(fun U=>(R.family.path.rep N p K).eval U • (c*F U))=c • H:=by
    funext U
    exact smul_comm _ c (F U)
  unfold actualTransport
  rw [input,scale R c H bill step]
  exact smul_comm _ c _

variable (d:Fin 3→ℕ){h:Fin 3→ℕ}(κ:(a:Fin 3)→Knob (h a))(pt:Fin 3→Chamber)
variable (Y:∀a:Fin 3,R.family.book.Ref (d a))(upper:Fin 3→Site (R.family.side N p))
  (o:Fin 3→Site (R.family.side K p))(v:∀a:Fin 3,R.family.label (d a))
local notation "Z" => WilsonOriginalAlternativeBarePorts.offer R d N p Y upper lit
local notation "F" => raw R d N p K o v
local notation "Q" => guarded R d N p K o v
def bare (s:(J).Mode)(U:X N):ℂ:=∏a∈s.val,R.family.O N p (Y a) (upper a) U

def read (live:K≤N){u:ℕ}(step:u≤K)(B:Fin 3→X K→ℂ)(s:(J).Mode)(W:X u):ℂ:=
  WilsonOriginalJointTrialHearing.read R N p W step (gust R.family.path N p N Z K live-print R d (N:=N) B) s

theorem original (live:K≤N){u:ℕ}(step:u≤K)(s:(J).Mode)(W:X u):
    read R d Y upper live step F s W=
      actualTransport R.family (N:=N) (bare R d Y upper s) (step.trans live) W-
        units R d K s*printed R d κ pt N p K o v s.val step W:=by
  let paid:=fun a=>(supplied R d (N:=N) o v a).2
  have grade:=WilsonOriginalMicroscopicEntranceFiling.original R d Y upper live F paid step s W
  have income:=WilsonReceivedCanonicalVersePosterior.original R d κ pt N p K live v o s.val u step W
  have shape:face F s=(fun U:X K=>∏a:s.val,WilsonPositionProgramBlockedTrialAddBack.uncut R (d a) N p K (o a) (v a) U):=by
    funext U
    exact (Finset.prod_coe_sort s.val (fun a=>WilsonPositionProgramBlockedTrialAddBack.uncut R (d a) N p K (o a) (v a) U)).symm
  rw [scaled R live step _ (salary F paid s),shape,income] at grade
  exact grade

include κ pt in
theorem correction (live:K≤N){u:ℕ}(step:u≤K)(s:(J).Mode)(W:X u):
    read R d Y upper live step F s W-read R d Y upper live step Q s W=
      -(units R d K s)*actualTransport R.family (N:=N) (gap R d N p K o v s.val) step W:=by
  let pay:=fun a=>(supplied R d (N:=N) o v a).1
  have west:=original R d κ pt Y upper o v live step s W
  have east:=WilsonOriginalMicroscopicEntranceFiling.original R d Y upper live Q pay step s W
  rw [scaled R live step _ (salary Q pay s)] at east
  have closed:=WilsonOriginalMicroscopicGuardedVerseBalance.original R d κ pt N p K live o v s.val step W
  have east' : read R d Y upper live step Q s W=
      actualTransport R.family (N:=N) (bare R d Y upper s) (step.trans live) W-
      units R d K s*actualTransport R.family (N:=N) (WilsonOriginalMicroscopicGuardedTrial.face Q s.val) step W:=east
  rw [west,east',←closed]
  ring

end YM.Integration.WilsonOriginalMicroscopicEntranceSockets
end
