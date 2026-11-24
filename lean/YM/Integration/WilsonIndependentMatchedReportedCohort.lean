import YM.Integration.WilsonIndependentMatchedReportedEnrolled
import YM.Integration.WilsonIndependentSpoutMasterClockFees
/-! Original physical shoulder for one cohort of funded homes on the normalized two-vacuum comparison. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedReportedCohort
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
open WilsonIndependentMatchedReportedEnrolled (Entered)
open WilsonIndependentMatchedBufferCohort (Booked)

def Paid (R:Run G)(W:Initialize G)(l d:I→ℕ)(admit:∀i,l i<d i)(kind:I→Bool)
    (own:∀i,Rails (l i) k u e)(arity:T→ℕ)(leg:∀t,Fin (arity t+1)→I)
    (α:∀i,Alma (R.family.labels.level (l i))→ℝ)(Z B:I→Credit)(cash rate:T→Credit)(floor:ℕ)(V:Realm G (e+1) C)(ticket:Credit)(low b out:ℕ)
    (primary:∀t,Fin (arity t+1)→Credit)(mid last:∀t,(Fin (arity t+1)→Bool)→Credit):Prop:=
  let Q:=deck (G:=G) l d admit
  let L:=R.family.path.levels
  ∀m K,floor ≤ m → m ≤ K → ∀(host:T→ℕ)(tests:∀t,Fin (arity t+1)→ℝ)(wage:I→ℝ)(depth ε:T→ℝ),
  (∀t,floor ≤ host t) → (∀t,host t ≤ m) → 1≤zz L m → (∀t,Compar L.S (zz L) (host t) m ≤ depth t) →
  (∀t,0<ε t) →
  let incomes i:=|chargeAt L (Q i) e (B i) (Z i) m K| *wage i
  let bills t:=price (cash t) (rate t) (zz L) m (depth t) (tests t) (incomes ∘ leg t)
  let w:=demand bills ε
  let upper:=first L.S K w
  K≤upper ∧ L.S.scale upper-L.S.scale K≤distance w+
      (if upper=K then 0 else Real.log (L.S.block (upper-1)).val) ∧
  ∀N N',upper ≤ N → upper ≤ N' →
  ∀c:∀i,Verse (R.family.labels.level (l i)),(∀i,charge e (c i) (α i) ≤ wage i) →
  ∃X:∀i,CutsP (hol G) (Q i).ans (Q i).path (own i) C C C C,
    WilsonPositionProgramTrialHomeFaces.Filed R W l d admit kind own c α Z B m K N X ∧
    ∀t,Pictured R W kind l d admit c own X (leg t) ∧ Outcome (Q ∘ leg t) L R.metals.O (fun i=>home (Q (leg t i)) (X (leg t i)))
      m K N N' (host t) e u (tests t) (depth t) (ε t) ∧
      ∀(F:Wilt (Q ∘ leg t))(y:ℝ)(o:CellR),Bough (Q ∘ leg t) F y (depth t) (tests t) →
      ∀(order:ℕ)(g:ℝ),order ≤ e → |g| ≤ 1 → ∀x:Fin 0 → YForest G,
      ‖WilsonIndependentMatchedPhysicalReportedSample.value L R.metals.O N m (host t) order g x
        (cruises L R.metals.O N (capP (Q ∘ leg t)) K (host t) (ordinary (Q:=Q ∘ leg t) (v:=fun i=>own (leg t i)) L (fun i=>X (leg t i)) F m K y o)-
         stopped L R.metals.O (Q ∘ leg t) F (fun i=>home (Q (leg t i)) (X (leg t i))) m K N' (host t) y o)‖ ≤
        WilsonIndependentMatchedPhysicalReportedCash.price (Q:=Q ∘ leg t) (v:=fun i=>own (leg t i)) V (fun i=>X (leg t i)) low b out (host t) m K order
          (primary t) (mid t) (last t) (depth t) g (ticket.buy (Compar R.family.S (zz L) (host t) m)) (tests t)+
          WilsonIndependentMatchedPhysicalReportedClock.bill order (ticket.buy (Compar R.family.S (zz L) (host t) m)) (ε t)

theorem withdrawal (R:Run G)(W:Initialize G)(l d:I→ℕ)(admit:∀i,l i<d i)(kind:I→Bool)
    (own:∀i,Rails (l i) k u e)(arity:T→ℕ)(leg:∀t,Fin (arity t+1)→I)
    (α:∀i,Alma (R.family.labels.level (l i))→ℝ)(Z B:I→Credit)(cash rate:T→Credit)(floor:ℕ)
    (V:Realm G (e+1) C)(ticket:Credit)(low b out:ℕ)(primary:∀t,Fin (arity t+1)→Credit)
    (mid last:∀t,(Fin (arity t+1)→Bool)→Credit)
    (anchor:V.anchor=floor)(original:Booked R W l d admit kind own arity leg α Z B cash rate floor)
    (ear:Entered R W l d admit kind own arity leg V ticket low b out primary mid last):
    Paid R W l d admit kind own arity leg α Z B cash rate floor V ticket low b out primary mid last:=by
  intro m K mature mk host tests wage depth ε awake older warm room eps inc bills wait U
  obtain ⟨keep,gap,bought⟩:=original m K mature mk host tests wage depth ε awake older warm room eps
  refine ⟨keep,gap,?_⟩
  intro N N' hN hN' c enough
  obtain ⟨X,filed,all⟩:=bought N N' hN hN' c enough
  refine ⟨X,filed,fun t=>⟨(all t).1,(all t).2,?_⟩⟩
  exact ear α Z B host m K N N' c X tests depth ε filed (fun s=>anchor.trans_le (awake s)) older mk
    (keep.trans hN) (fun s=>(eps s).le) t (all t).2

theorem original (R:Run G)(W:Initialize G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)
    (funded:FundedMarkedCoverRows.prices v R.kit)(fit:h<D)(rails:Rails h k u e)
    (l d:I→ℕ)(admit:∀i,l i<d i)(kind:I→Bool)(own:∀i,Rails (l i) k u e)
    (arity:T→ℕ)(leg:∀t,Fin (arity t+1)→I)
    (cap:∀t,capP (deck (G:=G) (l ∘ leg t) (d ∘ leg t) (fun i=>admit (leg t i)))≤k)
    (low b out:ℕ)(width:low+b≤u)(stage:∀t,(arity t+1)*k≤out)
    (spread:∀t,1 ≤ (b:ℝ)-((∑s,l (leg t s):ℕ):ℝ)-((arity t+1:ℕ):ℝ)/4)
    (ceiling:out≤b)(licence:Rails 0 out low e):
    ∃α:∀i,Alma (R.family.labels.level (l i))→ℝ,(∀i s,0≤α i s) ∧
    ∃(Z B:I→Credit)(cash rate:T→Credit)(primary:∀t,Fin (arity t+1)→Credit)
      (mid last:∀t,(Fin (arity t+1)→Bool)→Credit)(ticket:Credit),∀ᶠ floor:ℕ in atTop,
    ∃V:Realm G (e+1) C,V.draws=R.family.path.levels ∧ V.paid=R.metals.O ∧ V.y=zz R.family.path.levels ∧ V.anchor=floor ∧
      Paid R W l d admit kind own arity leg α Z B cash rate floor V ticket low b out primary mid last:=by
  obtain ⟨α,nn,Z,B,cash,rate,origin⟩:=WilsonIndependentMatchedBufferCohort.original R W simple v funded fit rails
    l d admit kind own arity leg cap
  obtain ⟨primary,mid,last,ears⟩:=WilsonIndependentMatchedReportedEnrolled.appointed R W l d admit kind own arity leg
    low b out width stage spread
  let l₁:Fin 1 → ℕ:=fun _=>h
  let d₁:Fin 1 → ℕ:=fun _=>D
  have one:capP (deck (G:=G) l₁ d₁ (fun _=>fit)) ≤ k:=by
    simpa [capP,asp,deck,BayV,l₁,d₁] using rails.hk
  obtain ⟨ticket,reset⟩:=WilsonIndependentSpoutMasterClockFees.original R simple v funded fit rails l₁ d₁ (fun _=>fit) one
  refine ⟨α,nn,Z,B,cash,rate,primary,mid,last,ticket,?_⟩
  filter_upwards [reset,origin,WilsonIndependentMatchedPhysicalCourt.original R simple v funded out low e b licence ceiling]
    with floor fees booked seat
  obtain ⟨V,levels,ratio,clock,anchor,dorm,spring⟩:=seat
  exact ⟨V,levels,ratio,clock,anchor,withdrawal R W l d admit kind own arity leg α Z B cash rate floor V ticket low b out
    primary mid last anchor booked (ears V ticket (by simpa only [anchor] using fees) levels ratio dorm spring)⟩

end YM.Integration.WilsonIndependentMatchedReportedCohort
