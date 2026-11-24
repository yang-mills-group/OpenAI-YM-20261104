import YM.Integration.WilsonMovingForkDepositedPrint
import YM.Integration.WilsonThermometerUnitFilingFlatRead

/-! Only sheets on the active physical collar are issued. The last full
ordinary Wilson reading is the explicit sum of the independently deposited
finite scalar coefficients on those sheets. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.WilsonMovingForkTerminalFile
open Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open Push Push.AbsoluteSums PhysicalNext PhysicalNext.Repeat.Legato Trace.Pilot OPE
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet Pert.Asymptotics
open WilsonMovingForkPrintedFile (Board Program registered allSlots parent)
open WilsonMovingForkDepositedPrint (Sheet board polynomial)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMovingForkMixedSeed (doses)
open WilsonThermometerUnitFilingFourSquare (Arm)
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFlatTelescope
open scoped Classical BigOperators Topology
variable {G:Gauge}{R:Run G}{n u K:ℕ}{d:Fin n → ℕ}

def quiet {side:Side}(pins:Fin n → Site side):Board G pins where
  index:=Fin 0
  load:=fun _=>0
  order:=0
  strip:=0
  binder:=Fin.elim0
  copies:=fun i=>Fin.elim0 i
  wallet:=fun _=>⟨0,by norm_num [room,disk]⟩

abbrev Source (R:Run G){n:ℕ}(d:Fin n → ℕ)(u K:ℕ):=
  ∀(N per:ℕ),K ≤ N → ((a:Fin n) → R.family.label (d a)) → (ξ:Fin n → Site (R.family.side K per)) →
    (i:ℕ) → u ≤ i → (ik:i<K) → Sheet R N i (parent R ik.le per ξ)

def programme (issued:Source R d u K):Program R d K:=
  fun N per w ξ i ik=>if active:K ≤ N ∧ u ≤ i then board (issued N per active.1 w ξ i active.2 ik)
    else quiet _

variable (old:Filed R d K)(issued:Source R d u K){S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
  {x:∀a,S.Field (d a)}(arms:∀a,Arm R.family S (l:Filter _) (d a) (x a))

theorem original {N per j:ℕ}(kn:K ≤ N)(uk:u<K)(jk:j ≤ K)(o:Fin n → Cover):
    let w:=doses R d old.station (N:=N) (per:=per) (old.A N per) (fun a=>(arms a).source (N,per))
    let ξ:=WilsonMovingForkSeededPoint.seats (R:=R) jk per o
    let H:=issued N per kn w ξ u le_rfl uk
    let g:=regulatorRun R.family N per u
    let M:=WilsonMovingForkCapturedFee.word (registered old (programme issued)) arms jk o (N,per)
    reading R (N:=N) (numerator R N per u (M u)) u le_rfl=(polynomial H g).part (allSlots n):=by
  intro w ξ H g M
  have name:programme issued N per w ξ u uk=board H:=dif_pos ⟨kn,le_rfl⟩
  have life:=WilsonThermometerUnitFilingFlatRead.original R (uk.le.trans kn) (R.family.path.rep N per u) rfl (M u)
  refine life.trans ?_
  have printed:=WilsonMovingForkPrintedFile.original old (programme issued) arms jk uk o (N,per) (1:Config G _)
  change M u 1=(WilsonOriginalTwoFlatIRMounted.value (programme issued N per w ξ u uk).binder
    (programme issued N per w ξ u uk).load (programme issued N per w ξ u uk).copies g
    (programme issued N per w ξ u uk).wallet 1).part (allSlots n) at printed
  rw [name,WilsonMovingForkDepositedPrint.flat] at printed
  exact printed

end YM.Integration.WilsonMovingForkTerminalFile
