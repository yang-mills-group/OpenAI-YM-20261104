import YM.Integration.WilsonPositionProgramRelativeClock
import YM.Integration.WilsonPositionProgramDatedClockBill
import YM.Integration.WilsonPositionProgramOriginalQuietTrajectory
import YM.QuadraticLocal.Fk.Attire
import YM.Integration.WilsonSubmittedCalendar

/-! The actual finite Wilson quiet pupil in the chronological coupling coordinate. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramChronologicalReversal
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetOriginalOutput Marker Multi
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G:Gauge}(R:Run G)

open WilsonVacuumPreResetTorusDeposit (bank)
open WilsonVacuumPreResetTorusGrade (evaluated)
open FVA1Physical.TwoReset (MassCall)
open AllOrder.Floe.Step
open AllOrder.Ker Primitives.TwoWave.RealSlice


open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetMeasuredCoin (Agrees)
open WilsonVacuumPreResetDepositedGeometric (source)
open QuadraticLocal.Earn AllOrder.Floe

open WilsonFiledPeriodSeam WilsonCoeffUV.Bank.Realm ActualRunAdmissionScales
open WilsonVacuumPreResetFiniteHeatCourse
open scoped Classical BigOperators

open WilsonVacuumPreResetDatedCourse (coin)
open FVA1Physical.TwoReset (massJets)
open AllOrder.Floe

open FVA1Physical.TwoReset (Prescription AffineMass)
open AllOrder.Floe.Step.PlanV

open PhysicalNext PhysicalNext.Repeat Legato WilsonLimitConstruction Next.Foundations
open WilsonSubmittedPeriodSeam (price weight Bill)

open QuadraticLocal.Rebirth QuadraticLocal.Faith Comparison.RG02.Adjacent

def material {N j:ℕ}(p e:ℕ)(π:ℕ→Layout G)(live:j<N)
    (F:Forest (step R j p).ratio)(tag:(step R j p).Choices)
    {T:Type}[DecidableEq T][Fintype T]{J:Census T}(Q:Bulk.Colors J G (fine R j p))
    (clock:UnitCost)(k:ℕ)(x:Stationary.Link G (coarse R j p)):ℂ:=
  born (Symmetry.Orbit.ground ((RunFormalChain.fromRun R).step N j p live) F tag
    (QuadraticLocal.Fk.grant (π (j+1)) (Step.tape (e+2)) Q) (e+2)) clock 0 (e+2) k (Stationary.arm G _ 1 x)

def deposited {N j:ℕ}(p e:ℕ)(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(origin:Γ j 0=0)
    (clock:UnitCost)(k:ℕ)(x:Stationary.Link G (coarse R j p)):ℂ:=
  let K:=(caliber (Γ j) origin).back (e+2)
  let lower:=Pace.grouping 0 (π j) (Step.tape (e+2)) (R.family.path.levels.params j).clip
    (R.alloy.B.kin.path N j)
  born (Spirit.suction (n:=coarse R j p) lower) (WilsonPositionProgramRelativeClock.relative K clock)
    0 (e+2) k (flatten (Stationary.arm G _ 1 x))

def invoice {j:ℕ}(p e:ℕ)(clock:UnitCost)(cost:ℕ→ℕ)(k:ℕ)
    (x y:Stationary.Link G (coarse R j p)):ℝ:=
  WilsonPositionProgramDatedClockBill.cost clock 0 (e+2) k (·+2)
    (fun t a=>price R t (cost t) j p * weight R t j p ((a:ℝ) • x) ((a:ℝ) • y))

theorem paid (simple:G.Simple)(clock:UnitCost){N j:ℕ}(p e:ℕ)(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
    (origin:Γ j 0=0)(live:j<N)(legal:Legal (Step.tape (e+2)) (π j))(cost:ℕ→ℕ)
    (paid:∀t≤e+2,WilsonPositionProgramOriginalQuietTrajectory.Paid R N j p e t (cost t) π Γ live)
    (F:Forest (step R j p).ratio)(tag:(step R j p).Choices)
    {T:Type}[DecidableEq T][Fintype T]{J:Census T}(Q:Bulk.Colors J G (fine R j p)){k:ℕ}(hk:k≤e+2)
    (x y:Stationary.Link G (coarse R j p)):
    ‖material R p e π live F tag Q clock k x-material R p e π live F tag Q clock k y-
      (deposited R (N:=N) p e π Γ origin clock k x-deposited R (N:=N) p e π Γ origin clock k y)‖ ≤ invoice R p e clock cost k x y:=by
  let n:=coarse R j p
  let op:=(RunFormalChain.fromRun R).step N j p live
  let model:=QuadraticLocal.Fk.grant (π (j+1)) (Step.tape (e+2)) Q
  let actual:=Symmetry.Orbit.ground op F tag model (e+2)
  let reg:=R.family.path.levels.params j
  let P:=R.alloy.B.kin.path N j
  let data:=Pace.grouping (Γ j) (π j) (Step.tape (e+2)) reg.clip P
  let native:=Spirit.suction (n:=n) data
  let K:=(caliber (Γ j) origin).back (e+2)
  let ax:=Stationary.arm G n 1
  have at_date:=R.makes.wilson.represents N p j live.le
  have bounds:P.Bounds reg.clip reg.width reg.paths (R.family.path.levels.clock.loopCap j):=by
    change (R.alloy.B.kin.path N j).Bounds reg.clip _ _ _
    have same:(R.family.path.rep N p j).clip=reg.clip:=at_date.clip
    rw [←CommonConstruction.runAlong_actual_path R N j p live.le,←same]
    exact at_date.good.paths
  have field:Charge (e+2) (fun t=>((t+2:ℕ):ℤ)) actual:=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using LocalScript.rank op F tag model (e+2)
  have prescribed:Charge (e+2) (fun t=>((t+2:ℕ):ℤ)) native:=by
    intro t _
    exact_mod_cast Spirit.charges (n:=n) (Γ j) P reg.clip (π j) (Step.tape (e+2)) simple legal bounds t
  let lower:=Pace.grouping 0 (π j) (Step.tape (e+2)) reg.clip P
  let rel:=WilsonPositionProgramRelativeClock.relative K clock
  have back (t:ℕ)(ht:t≤e+2):
      born native K 0 (e+2) t=Spirit.suction (n:=n) lower t:=
    Spirit.returned (Γ j) origin (e+2) P reg.clip (π j) (Step.tape (e+2)) simple legal bounds ht
  have rebase:born (Spirit.suction (n:=n) lower) rel 0 (e+2) k
      =born native clock 0 (e+2) k:=by
    exact (WilsonPositionProgramRelativeClock.same_rows 0 (e+2) rel back k).symm.trans
      (WilsonPositionProgramRelativeClock.restored (e+2) native (fun t=>((t+2:ℕ):ℤ))
        prescribed (fun x y h=>by
          change ((x+2:ℕ):ℤ)≤((y+2:ℕ):ℤ)
          exact_mod_cast Nat.add_le_add_right h 2) K clock k hk)
  have receive (u:Stationary.Link G n):
      deposited R (N:=N) p e π Γ origin clock k u=born native clock 0 (e+2) k (flatten (ax u)) :=
    congrFun rebase _
  unfold material invoice
  rw [receive x,receive y]
  apply WilsonPositionProgramDatedClockBill.original clock 0 _ k (fun t=>t+2) actual native
    field prescribed
  intro t ht a _
  have budget:=paid t ht F tag Q ((a:ℝ) • x) ((a:ℝ) • y)
  have linear (u:Stationary.Link G n):ax ((a:ℝ) • u)=(a:ℝ) • ax u:=map_smul ..
  have coordinates (u:Stationary.Link G n):flatten ((a:ℝ) • ax u)=(a:ℝ) • flatten (ax u):=rfl
  have sample:‖actual t (ax ((a:ℝ) • x))-actual t (ax ((a:ℝ) • y))+
      ((data t n (flatten (ax ((a:ℝ) • x)))-data t n (flatten (ax ((a:ℝ) • y))):ℝ):ℂ)‖≤
      price R t (cost t) j p * weight R t j p ((a:ℝ) • x) ((a:ℝ) • y):=budget
  change ‖actual t ((a:ℝ) • ax x)-actual t ((a:ℝ) • ax y)-
    (native t ((a:ℝ) • flatten (ax x))-native t ((a:ℝ) • flatten (ax y)))‖≤_
  refine (le_of_eq ?_).trans sample
  apply congrArg norm
  simp only [native,Spirit.suction,←coordinates,←linear,Complex.ofReal_sub]
  ring

end YM.Integration.WilsonPositionProgramChronologicalReversal
end
