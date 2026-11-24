import YM.Integration.WilsonOriginalObservedRoseParity
import YM.Integration.WilsonMaxwellThermometerPublicEvenGround
import YM.Integration.WilsonOriginalObservedRoseTransfer

/-! On the actual original positions the finite ground after the full source
correction drops the odd upper part, on every proper and full face. The
remaining even upper and its scalar stay on that original board. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseCoarse

open Function Filter Finset Set Metric Spec Extraction Table RG Lattice OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Wilson PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame Precision Cells
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus XSpace.Photo XSpace.Graph3
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonMaxwellThermometerSignedWallet
open WilsonMaxwellThermometerPublicGalop (quotient)
open XSpace.Retirement XSpace.Tornado XSpace.AxesTangent WilsonMaxwellThermometerFirstDetector
open WilsonMaxwellThermometerPublicEvenSlope (entered)
open WilsonMaxwellThermometerPositionCurrency (received)
open WilsonMaxwellThermometerChargedHeads (head sector)
open WilsonMaxwellThermometerVotedCurrency (pay)
open WilsonMaxwellThermometerSharedGroundFaces (tree)
open WilsonMaxwellThermometerSharedGroundPanel (change)
open WilsonOriginalObservedRoseJoint (locations lowerSite)
open WilsonOriginalObservedRoseLedger (Visit)
open scoped Classical Topology BigOperators

variable {G:Gauge}(R:Run G)(D:ChartRatio G)(W:Initialize G){V:Normalize.Store G}(simple:G.Simple)

def retained (x:Sample 3)(k:ℕ)(v:∀i,Axes R i) : Tags G 6 3 :=
  let top:=R.family.labels.level 6
  let upper:=pay top x (R.family.S.a k) (v 0)
  let L:=R.family.labels.level 4
  entered (sector top upper-sector top (head top upper))
    (received x (R.family.S.a k) (sector L (v 1)))
    (received x (R.family.S.a k) (sector L (v 2)))

include simple in
theorem registered (law:LocalRatio D){w:Visit}{k:ℕ}(live:k≤w.2.1)
    (vote:V.Meets W (board R k w.1 w.2.2) 6)(v:∀i,Axes R i)(o:locations R w.2)(s:Finset (Fin 3)) :
    let x:=lowerSite R k w.1 w.2 live o
    let p:=deposited R k w.1 w.2.2 v
    tree R D W (V:=V) x p s-change R W (V:=V) x p s=
      quotient W (V:=V) x (retained R x k v) 0 s := by
  dsimp only
  let x:=lowerSite R k w.1 w.2 live o
  let p:=deposited R k w.1 w.2.2 v
  have tag:p=entered (received x (R.family.S.a k) (sector _ (v 0)))
      (received x (R.family.S.a k) (sector _ (v 1)))
      (received x (R.family.S.a k) (sector _ (v 2))) := by
    funext i;fin_cases i <;>rfl
  have paid:V.Meets W x.F 6:=vote
  have fee:=WilsonMaxwellThermometerSharedGroundFaces.reported R D W (V:=V) x p law s
  change tree R D W (V:=V) x p s-quotient W (V:=V) x p 0 s=change R W (V:=V) x p s at fee
  change tree R D W (V:=V) x p s-change R W (V:=V) x p s=_
  rw [←fee,sub_sub_cancel,tag]
  exact WilsonMaxwellThermometerPublicEvenGround.original W x simple paid
    (R.family.labels.level 6) (R.family.labels.level 4) (v 0) (v 1) (v 2) (R.family.S.a k) s

end YM.Integration.WilsonOriginalObservedRoseCoarse
