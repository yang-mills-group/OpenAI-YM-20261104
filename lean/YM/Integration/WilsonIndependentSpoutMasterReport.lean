import YM.Integration.WilsonIndependentSpoutMasterArms
import YM.Integration.WilsonIndependentSpoutMasterBasisCutoff

/-! The two normalized conditional histories each return their master coefficients to the same measuring variable. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutMasterReport
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Source Source.Drops Labels
open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonIndependentSpoutMasterArms (arm)
open WilsonIndependentSpoutMasterCoordinates (axis)
open WilsonIndependentSpoutScalarLedger (ground)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonMarkedIndependentNormalizedElection (normalized)
open scoped BigOperators Classical
variable {G:Gauge}{n:ℕ}(L:Levels G)(O:ChartRatio G)(simple:G.Simple)(valid:LocalRatio O)
    (Q:Fin (n+1)→SealR G)(F:Wilt Q)(b:Herit Q)(m K N v:ℕ)(y:ℝ)(o:CellR)

theorem collected {J:Type}[Fintype J](X:J→Era G ℝ):ground (∑j,X j)=∑j,ground (X j):=by
  ext e
  simp only [ground,WilsonOlderFreshSoftSocketKinetic.reading,PowerSeries.coeff_mk,map_sum,
    Prod.snd_sum,Finset.sum_apply]

theorem passage (older:v ≤ m)(prior:m ≤ K):
    stopped L O Q F b m K N v y o=
      cruises L O N (capP Q) K v (Ashore Q L O F (normalized L O Q b m N) m K N y o):=by
  exact (cruisesMore L O _ older prior).symm

include simple valid in
theorem finite (older:v ≤ m)(prior:m ≤ K)(top:K ≤ N)
    (paid:∀i a,Auth (Q i).h (arm L O (Q i) (F i) (axis (Q i) a) m K N y o)):
    ground (stopped L O Q F b m K N v y o)=
      ∑a:(∀i,Alma (Q i).F),clock L O N m v (∏i,b i (a i))*
        ground (stopped L O Q F (WilsonIndependentSpoutMasterArms.basis Q a) m K N v y o):=by
  let k:=capP Q
  let relative:=reel (relativeC L O N m (K-m))
  let bank (a:∀i,Alma (Q i).F):=Ashore Q L O F (normalized L O Q (WilsonIndependentSpoutMasterArms.basis Q a) m N) m K N y o
  let cost (a:∀i,Alma (Q i).F):=∏i,b i (a i)
  let rows a:=affiled (relative (cost a)) (bank a)
  have entered a:Auth k (bank a):=manCo _ (fun i=>(Q i).h) (fun i=>paid i (a i))
  have ready a:Auth k (rows a):=WilsonIndependentMatchedOpeningFee.grant _ (entered a) _
  rw [passage L O Q F b m K N v y o older prior,
    WilsonIndependentSpoutMasterArms.original L O Q F b m K N y o paid]
  change ground (cruises L O N k K v (∑a,rows a))=_
  rw [WilsonIndependentSpoutDoseBoundary.checkedSum L O simple valid N K v k (older.trans prior) top rows ready,collected]
  apply Finset.sum_congr rfl
  intro a _
  rw [passage L O Q F (WilsonIndependentSpoutMasterArms.basis Q a) m K N v y o older prior]
  change ground (cruises L O N k K v (rows a))=clock L O N m v (cost a)*ground (cruises L O N k K v (bank a))
  have kept:=WilsonOlderFreshSoftSocketHistory.original L O simple valid N k K v (older.trans prior) top (rows a)
    (bank a) (relative (cost a)) (ready a) (entered a) (fun _=>rfl)
  unfold ground
  rw [kept,WilsonOlderFreshSoftSocketKinetic.valued,
    ←WilsonOlderFreshSoftSocketKinetic.combine L O N K m v older prior]
  have home:=WilsonIndependentFittedRelativeClock.restored L O simple valid N m (K-m) (by omega) (cost a)
  simpa only [show m+(K-m)=K by omega,relative] using congrArg (fun z=>clock L O N m v z*
    WilsonOlderFreshSoftSocketKinetic.reading (cruises L O N k K v (bank a)).2 Fin.elim0) home

def report (N m v:ℕ)(X:Cost):Cost:=reel (relativeC L O N v (m-v)) X

include simple valid in
theorem cancellation (near:v ≤ m)(live:m ≤ N)(x:Cost):
    report L O N m v (clock L O N m v x)=x:=by
  have he:=WilsonIndependentFittedRelativeClock.reported L O N v (m-v) x
  rw [show v+(m-v)=m by omega] at he
  rw [he]
  change ((reel (relativeC L O N v (m-v))).comp (reel (relativeF L O N v (m-v)))) x=x
  rw [reel_chart,(direction simple valid (by omega:v+(m-v)≤N)).1,reel_one]

include simple valid in
theorem bare (near:v ≤ m)(live:m ≤ N)(x:Cost):
    clock L O N N m (WilsonIndependentSpoutDoseBoundary.into L O N v x)=report L O N m v x:=by
  have schedule:=WilsonOlderFreshSoftSocketKinetic.combine L O N N m v near live
    (WilsonIndependentSpoutDoseBoundary.into L O N v x)
  rw [WilsonIndependentSpoutDoseBoundary.restored L O simple valid N v (near.trans live) x] at schedule
  have read:=congrArg (report L O N m v) schedule
  simpa only [cancellation L O simple valid m N v near live] using read

include simple valid in
theorem original (older:v ≤ m)(prior:m ≤ K)(top:K ≤ N)
    (paid:∀i a,Auth (Q i).h (arm L O (Q i) (F i) (axis (Q i) a) m K N y o)):
    report L O N m v (ground (stopped L O Q F b m K N v y o))=
      ∑a:(∀i,Alma (Q i).F),(∏i,b i (a i))*
        report L O N m v (ground (stopped L O Q F (WilsonIndependentSpoutMasterArms.basis Q a) m K N v y o)):=by
  rw [finite L O simple valid Q F b m K N v y o older prior top paid]
  simp only [report,map_sum,map_mul]
  exact Finset.sum_congr rfl fun a _=>congrArg (·*_) (cancellation L O simple valid m N v older (prior.trans top) _)

end YM.Integration.WilsonIndependentSpoutMasterReport
end
