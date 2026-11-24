import YM.Integration.WilsonIndependentMatchedBufferGate
import YM.Integration.WilsonIndependentMatchedBufferSalary
import YM.Integration.WilsonIndependentMatchedOpeningSubfaces
/-! File every arm once and choose the quantitative vacuum buffer before the two UV cutoffs. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedBufferCohort
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
def Booked (R:Run G)(W:Initialize G)(l d:I→ℕ)(admit:∀i,l i<d i)(kind:I→Bool)
    (own:∀i,Rails (l i) k u e)(arity:T→ℕ)(leg:∀t,Fin (arity t+1)→I)
    (α:∀i,Alma (R.family.labels.level (l i))→ℝ)(Z B:I→Credit)(cash rate:T→Credit)(floor:ℕ):Prop:=
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
      m K N N' (host t) e u (tests t) (depth t) (ε t)

theorem original (R:Run G)(W:Initialize G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)
    (funded:FundedMarkedCoverRows.prices v R.kit)(fit:h<D)(rails:Rails h k u e)
    (l d:I→ℕ)(admit:∀i,l i<d i)(kind:I→Bool)(own:∀i,Rails (l i) k u e)
    (arity:T→ℕ)(leg:∀t,Fin (arity t+1)→I)
    (cap:∀t,capP (deck (G:=G) (l ∘ leg t) (d ∘ leg t) (fun i=>admit (leg t i)))≤k):
    ∃α:∀i,Alma (R.family.labels.level (l i))→ℝ,(∀i s,0≤α i s) ∧
    ∃(Z B:I→Credit)(cash rate:T→Credit),∀ᶠ floor:ℕ in atTop,Booked R W l d admit kind own arity leg α Z B cash rate floor:=by
  let Q:=deck (G:=G) l d admit
  let L:=R.family.path.levels
  have cash i:=WilsonPositionProgramTrialStationHome.original R W simple v funded (admit i) (own i)
    (l i) (kind i) (admit i) (own i).hk
  choose α nn Z B enrolled using cash
  have leases t:=WilsonIndependentMatchedBufferedVacuum.original R simple v funded fit rails
    (l ∘ leg t) (d ∘ leg t) (fun i=>admit (leg t i)) (cap t)
  choose Cpay rate compare using leases
  refine ⟨α,nn,Z,B,Cpay,rate,?_⟩
  filter_upwards [Filter.eventually_all.2 enrolled,Filter.eventually_all.2 compare] with floor source signed
  intro m K mature mk host tests wage depth ε low high warm room small inc bills w U
  have keep:K≤U:=(WilsonIndependentMatchedBufferGate.purchased L.S K w).1
  refine ⟨keep,WilsonIndependentMatchedBufferGate.overshoot L.S K w,?_⟩
  intro N N' active fresh c paid
  have purchased i:=source i m K N mature mk (keep.trans active) (c i) 1
  choose X seats readings charges using purchased
  have mounted:WilsonPositionProgramTrialHomeFaces.Filed R W l d admit kind own c α Z B m K N X:=by
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
  intro t
  refine ⟨WilsonIndependentMatchedOpeningSubfaces.pinned R W kind l d admit c own X α Z B mounted (leg t),?_⟩
  apply WilsonIndependentMatchedBufferSalary.receives (signed t) m K U N N' (host t) (tests t)
    (inc ∘ leg t) (depth t) (ε t) _ (low t) (high t) mk keep active fresh warm (room t)
  · intro i
    exact (mounted (leg t i)).2.2.trans (mul_le_mul_of_nonneg_left (paid (leg t i)) (abs_nonneg _))
  · exact WilsonIndependentMatchedBufferGate.earned L.S K bills ε small m mk t

end YM.Integration.WilsonIndependentMatchedBufferCohort
end
