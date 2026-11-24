import YM.Integration.WilsonPositionProgramTrialHomeFaces

/-! All named arms occupy one family of original cutoff sections before
geometry. Repeated, permuted, and deleted names use those same sections. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOriginalGeneralRosterHomeRooms
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

open WilsonPositionProgramTrialHomeFaces (Filed)

theorem select {R:Run G}{W:Initialize G}{l d:I→ℕ}{admit:∀i,l i<d i}{kind:I→Bool}
    {own:∀i,Rails (l i) k u e}{c:∀i,Verse (R.family.labels.level (l i))}
    {α:∀i,Alma (R.family.labels.level (l i))→ℝ}{Z B:I→Credit}{m K N:ℕ}
    {X:∀i,CutsP (hol G) ((deck (G:=G) l d admit) i).ans ((deck (G:=G) l d admit) i).path (own i) C C C C}
    (dwells:Filed R W l d admit kind own c α Z B m K N X){b:ℕ}(leg:Fin (b+1)→I):
    Filed R W (l ∘ leg) (d ∘ leg) (fun i=>admit (leg i)) (kind ∘ leg) (fun i=>own (leg i))
      (fun i=>c (leg i)) (fun i=>α (leg i)) (Z ∘ leg) (B ∘ leg) m K N (fun i=>X (leg i)):=fun i=>dwells (leg i)

theorem original (R:Run G)(W:Initialize G)(simple:G.Simple)(ξ:ℕ→Gear G→ℝ)
    (funded:FundedMarkedCoverRows.prices ξ R.kit)(l d:I→ℕ)(admit:∀i,l i<d i)
    (kind:I→Bool)(own:∀i,Rails (l i) k u e):
    let Q:=deck (G:=G) l d admit
    ∃α:∀i,Alma (R.family.labels.level (l i))→ℝ,(∀i a,0≤α i a) ∧
    ∃Z B:I→Credit,∀ᶠfloor:ℕ in atTop,∀m K N,floor ≤ m → m ≤ K → K ≤ N → 
      ∀c:∀i,Verse (R.family.labels.level (l i)),∃X:∀i,CutsP (hol G) (Q i).ans (Q i).path (own i) C C C C,
        Filed R W l d admit kind own c α Z B m K N X:=by
  intro Q
  have prices i:=WilsonPositionProgramTrialStationHome.original R W simple ξ funded (admit i) (own i)
    (l i) (kind i) (admit i) (own i).hk
  choose α nn Z B offer using prices
  refine ⟨α,nn,Z,B,?_⟩
  filter_upwards [Filter.eventually_all.2 offer] with floor course
  intro m K N mature before live c
  have purchased i:=course i m K N mature before live (c i) 1
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
  exact ⟨X,mounted⟩

end YM.Integration.WilsonOriginalGeneralRosterHomeRooms
end
