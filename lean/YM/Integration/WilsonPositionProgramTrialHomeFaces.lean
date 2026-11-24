import YM.Integration.WilsonPositionProgramTrialHomeRoster

/-! All named subwords retain one cutoff-dependent deposited vector per original leg. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialHomeFaces
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

def Outcome {a:ℕ}(Q:Fin (a+1)→SealR G)(L:Levels G)(O:ChartRatio G)(b:Herit Q)
    (m K N N' host e u:ℕ)(B:Fin (a+1)→ℝ)(Z ε:ℝ):Prop:=
  ∀(F:Wilt Q)(y:ℝ)(o:CellR),Bough Q F y Z B →
    let A:=stopped L O Q F b m K N host y o
    let A':=stopped L O Q F b m K N' host y o
    (∀r t,r≤e → Fruit 0 1 u (A.2 r t-A'.2 r t) ε) ∧
    ∀r,r≤e → ∀t:Fin 0→YForest G,‖A.2 r 0 t-A'.2 r 0 t‖≤ε

def Filed (R:Run G)(W:Initialize G)(l d:I→ℕ)(admit:∀i,l i<d i)(kind:I→Bool)
    (own:∀i,Rails (l i) k u e)(c:∀i,Verse (R.family.labels.level (l i)))
    (α:∀i,Alma (R.family.labels.level (l i))→ℝ)(Z B:I→Credit)(m K N:ℕ)
    (X:∀i,CutsP (hol G) ((deck (G:=G) l d admit) i).ans ((deck (G:=G) l d admit) i).path (own i) C C C C):
    Prop:=∀i,
    let Q:=(deck (G:=G) l d admit) i
    let X':=X i
    Seated R Q (own i) m K N (Shrine (plate (sectionAt R W (kind i) (l i)) (admit i)) (c i))
        (charge e (c i) (α i)) X' ∧
    X'.pt=centralL R.family.path.levels R.metals.O N m K Q
      (PermuteLens R.family.path.levels R.metals.O Q N m (home Q X'))+X'.springP X'.i ∧
    mass Q e (home Q X') ≤ |chargeAt R.family.path.levels Q e (B i) (Z i) m K| *charge e (c i) (α i)

def Booked (R:Run G)(W:Initialize G)(l d:I→ℕ)(admit:∀i,l i<d i)(kind:I→Bool)
    (own:∀i,Rails (l i) k u e)(arity:T→ℕ)(leg:∀t,Fin (arity t+1)→I)
    (α:∀i,Alma (R.family.labels.level (l i))→ℝ)(Z B:I→Credit)(floor:ℕ):Prop:=
  let Q:=deck (G:=G) l d admit
  let L:=R.family.path.levels
  ∀m K,floor ≤ m → m ≤ K → ∀(host:T→ℕ)(tests:∀t,Fin (arity t+1)→ℝ)(wage:I→ℝ)(depth ε:T→ℝ),
  (∀t,floor ≤ host t) → (∀t,host t ≤ m) → 1≤zz L m → (∀t,Compar L.S (zz L) (host t) m ≤ depth t) →
  (∀t,0<ε t) → ∃upper:ℕ,K ≤ upper ∧ ∀N N',upper ≤ N → upper ≤ N' →
  ∀c:∀i,Verse (R.family.labels.level (l i)),(∀i,charge e (c i) (α i) ≤ wage i) →
  ∃X:∀i,CutsP (hol G) (Q i).ans (Q i).path (own i) C C C C,
    Filed R W l d admit kind own c α Z B m K N X ∧
    ∀t,Outcome (Q ∘ leg t) L R.metals.O (fun i=>home (Q (leg t i)) (X (leg t i)))
      m K N N' (host t) e u (tests t) (depth t) (ε t)

theorem original (R:Run G)(W:Initialize G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)
    (funded:FundedMarkedCoverRows.prices v R.kit)(fit:h<D)(rails:Rails h k u e)
    (l d:I→ℕ)(admit:∀i,l i<d i)(kind:I→Bool)(own:∀i,Rails (l i) k u e)
    (arity:T→ℕ)(leg:∀t,Fin (arity t+1)→I)
    (cap:∀t,capP (deck (G:=G) (l ∘ leg t) (d ∘ leg t) (fun i=>admit (leg t i)))≤k):
    ∃α:∀i,Alma (R.family.labels.level (l i))→ℝ,(∀i s,0≤α i s) ∧
    ∃Z B:I→Credit,∀ᶠ floor:ℕ in atTop,Booked R W l d admit kind own arity leg α Z B floor:=by
  let Q:=deck (G:=G) l d admit
  have cash i:=WilsonPositionProgramTrialStationHome.original R W simple v funded (admit i) (own i)
    (l i) (kind i) (admit i) (own i).hk
  choose α nn Z B enrolled using cash
  have rates t:=WilsonPositionProgramTrialBufferedHome.original R simple v funded fit rails
    (l ∘ leg t) (d ∘ leg t) (fun i=>admit (leg t i)) (cap t)
  refine ⟨α,nn,Z,B,?_⟩
  filter_upwards [Filter.eventually_all.2 enrolled,Filter.eventually_all.2 rates] with floor source vacuum
  intro m K mature mk host tests wage depth ε low high warm room small
  let inc i:=|chargeAt R.family.path.levels (Q i) e (B i) (Z i) m K| *wage i
  have offered t:=
    vacuum t m K (host t) (low t) (high t) mk (tests t) (inc ∘ leg t) (depth t) (ε t) warm (room t) (small t)
  choose cutoff clears compare using offered
  let top:=max K (univ.sup cutoff)
  have late t:cutoff t ≤ top:=(le_sup (f:=cutoff) (mem_univ t)).trans (le_max_right _ _)
  refine ⟨top,le_max_left _ _,?_⟩
  intro N N' active fresh c paid
  have purchased i:=source i m K N mature mk ((le_max_left K _).trans active) (c i) 1
  choose X seats readings charges using purchased
  have mounted:Filed R W l d admit kind own c α Z B m K N X:=by
    intro i
    have val:=charges i 1
    have nonneg:0≤charge e (c i) (α i):=Finset.sum_nonneg fun s _=>
      WilsonIndependentMatchedFiledIncome.nonneg (nn i s) _ _
    refine ⟨by simpa only [one_smul,abs_one,one_mul,deck,BayV,WilsonPositionProgramTrialNativeHome.reporter]
        using seats i,?_,?_⟩
    · obtain ⟨lv,ch,m₀,k₀,n₀,_⟩:=seats i
      have raw:=WilsonPositionProgramTrialAccrued.source (Q i) (X i)
      rw [lv,ch,n₀,m₀,k₀] at raw
      exact raw
    · simp only [WilsonPositionProgramTrialHomeDose.scaled,one_smul,abs_one,one_mul] at val
      exact val.trans (mul_le_mul_of_nonneg_right (le_abs_self _) nonneg)
  refine ⟨X,mounted,?_⟩
  intro t F y o shape
  apply compare t N N' (fun i=>home (Q (leg t i)) (X (leg t i))) F y o
    ((late t).trans active) ((late t).trans fresh) shape
  intro i
  exact (mounted (leg t i)).2.2.trans (mul_le_mul_of_nonneg_left (paid (leg t i)) (abs_nonneg _))

end YM.Integration.WilsonPositionProgramTrialHomeFaces
end
