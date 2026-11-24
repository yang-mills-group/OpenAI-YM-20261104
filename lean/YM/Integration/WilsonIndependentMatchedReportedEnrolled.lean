import YM.Integration.WilsonIndependentMatchedPhysicalReportedCash
import YM.Integration.WilsonIndependentMatchedBufferCohort
/-! Return the genuine filed physical arms on the actual elected levels at every named receiving date. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedReportedEnrolled
open Function Filter Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost
open WilsonPositionProgramTrialStationHome (chargeAt mass Seated)
open WilsonPositionProgramTrialAccrued (home)
open WilsonIndependentMatchedFiledIncome (charge plate)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonPositionProgramNormalizedMaster (fee)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped BigOperators Topology Classical
variable {G:Gauge}{n h D k u e:ℕ}{T:Type*}[Fintype T]
local notation "C" => Credit.leanC
local notation "I" => Fin (n+1)


open WilsonPositionProgramTrialHomeFaces (Outcome)
open WilsonIndependentMatchedOpeningSubfaces (Pictured)
open WilsonIndependentMatchedBufferGate (first demand distance)
open WilsonIndependentMatchedBufferSalary (price)
open WilsonIndependentMatchedRosterPlanted (response)
open WilsonIndependentMatchedPhysicalReturn (ordinary)
open WilsonIndependentMatchedPhysicalSector (stamp)

def Entered (R:Run G)(W:Initialize G)(l d:I→ℕ)(admit:∀i,l i<d i)(kind:I→Bool)
    (own:∀i,Rails (l i) k u e)(arity:T→ℕ)(leg:∀t,Fin (arity t+1)→I)
    (V:Realm G (e+1) C)(ticket:Credit)(low b out:ℕ)
    (primary:∀t,Fin (arity t+1)→Credit)(mid last:∀t,(Fin (arity t+1)→Bool)→Credit):Prop:=
  let Q:=deck (G:=G) l d admit
  let L:=R.family.path.levels
  ∀(α:∀i,Alma (R.family.labels.level (l i))→ℝ)(Z B:I→Credit)(host:T→ℕ)(m K N N':ℕ)
    (c:∀i,Verse (R.family.labels.level (l i)))
    (X:∀i,CutsP (hol G) (Q i).ans (Q i).path (own i) C C C C)
    (tests:∀t,Fin (arity t+1)→ℝ)(depth ε:T→ℝ),
    WilsonPositionProgramTrialHomeFaces.Filed R W l d admit kind own c α Z B m K N X →
    (∀t,V.anchor ≤ host t) → (∀t,host t ≤ m) → m ≤ K → K ≤ N → (∀t,0 ≤ ε t) →
    ∀t,Outcome (Q ∘ leg t) L R.metals.O (fun i=>home (Q (leg t i)) (X (leg t i))) m K N N' (host t) e u (tests t) (depth t) (ε t) →
    ∀(F:Wilt (Q ∘ leg t))(y:ℝ)(o:CellR),Bough (Q ∘ leg t) F y (depth t) (tests t) →
    ∀(order:ℕ)(g:ℝ),order ≤ e → |g| ≤ 1 → ∀x:Fin 0 → YForest G,
    ‖WilsonIndependentMatchedPhysicalReportedSample.value L R.metals.O N m (host t) order g x
      (cruises L R.metals.O N (capP (Q ∘ leg t)) K (host t) (ordinary (Q:=Q ∘ leg t) (v:=fun i=>own (leg t i)) L (fun i=>X (leg t i)) F m K y o)-
       stopped L R.metals.O (Q ∘ leg t) F (fun i=>home (Q (leg t i)) (X (leg t i))) m K N' (host t) y o)‖ ≤
      WilsonIndependentMatchedPhysicalReportedCash.price (Q:=Q ∘ leg t) (v:=fun i=>own (leg t i)) V (fun i=>X (leg t i)) low b out (host t) m K order
       (primary t) (mid t) (last t) (depth t) g (ticket.buy (Compar R.family.S (zz L) (host t) m)) (tests t)+
      WilsonIndependentMatchedPhysicalReportedClock.bill order (ticket.buy (Compar R.family.S (zz L) (host t) m)) (ε t)

omit [Fintype T] in
theorem appointed (R:Run G)(W:Initialize G)(l d:I→ℕ)(admit:∀i,l i<d i)(kind:I→Bool)
    (own:∀i,Rails (l i) k u e)(arity:T→ℕ)(leg:∀t,Fin (arity t+1)→I)
    (low b out:ℕ)(width:low+b≤u)(stage:∀t,(arity t+1)*k≤out)
    (spread:∀t,1 ≤ (b:ℝ)-((∑s,l (leg t s):ℕ):ℝ)-((arity t+1:ℕ):ℝ)/4):
    ∃(primary:∀t,Fin (arity t+1)→Credit)(mid last:∀t,(Fin (arity t+1)→Bool)→Credit),
    ∀(V:Realm G (e+1) C)(ticket:Credit),WilsonIndependentSpoutMasterClockFees.Paid R V.anchor e ticket →
    V.draws=R.family.path.levels → V.paid=R.metals.O →
    (∀s ≤ out,Dormitory V s low C) → SpringD V out low b C →
    Entered R W l d admit kind own arity leg V ticket low b out primary mid last:=by
  let Q:=deck (G:=G) l d admit
  let L:=R.family.path.levels
  have purchase t:=WilsonIndependentMatchedPhysicalReportedCash.released (hol G) (Q ∘ leg t)
    (fun i=>own (leg t i)) low b out width (stage t) (spread t)
  choose primary mid last all using purchase
  refine ⟨primary,mid,last,?_⟩
  intro V ticket financial levels ratio dorm spring
  dsimp only [Entered]
  intro α Z B host m K N N' c X tests depth ε filed awake older born live eps t outcome F y o shape order g cut small x
  have register i:= (filed (leg t i)).1
  have stamp₀:stamp V (fun i=>X (leg t i)) m K N:=by
    intro i
    obtain ⟨ll,oo,mm,kk,nn,_⟩:=register i
    exact ⟨ll.trans levels.symm,oo.trans ratio.symm,mm,kk,nn⟩
  have ward i:On (l (leg t i)) (X (leg t i)).pt:=by
    let a:=leg t i
    obtain ⟨_,_,_,_,_,_,source,_⟩:=register i
    obtain ⟨_,_,funded⟩:=WilsonIndependentMatchedFiledIncome.named R W (kind a) (l a) (admit a)
      (le_refl (l a)) e u
    rw [source]
    exact (funded (c a)).1
  have cutPaid:Outcome (Q ∘ leg t) V.draws V.paid (fun i=>home (Q (leg t i)) (X (leg t i))) m K N N' (host t)
      e low (tests t) (depth t) (ε t):=by
    rw [levels,ratio]
    intro F y o shape
    have got:=outcome F y o shape
    exact ⟨fun j r hj=>(got.1 j r hj).slice zero_le_one (by omega),got.2⟩
  have result:=all t R financial V (fun i=>X (leg t i)) (host t) m K N N' (tests t) (depth t) (ε t)
    stamp₀ levels ratio (awake t) (awake t) (older t) born live spring dorm ward (eps t) cutPaid F y o shape order g cut small x
  simpa only [Q,Function.comp_apply,levels,ratio] using result

end YM.Integration.WilsonIndependentMatchedReportedEnrolled
