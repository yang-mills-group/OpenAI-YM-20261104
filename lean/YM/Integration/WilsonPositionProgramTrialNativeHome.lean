import YM.Integration.WilsonPositionProgramTrialHomeDose
import YM.Integration.WilsonIndependentMatchedFiledIncome
import YM.Integration.WilsonMarkedIndependentNormalizedElection

/-! The actual covered R and W sections in one measured reporting frame. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialNativeHome
open Function Filter Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonPositionProgramTrialHomeDose (publicDose)
open WilsonIndependentMatchedFiledIncome (charge plate)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonOriginalPublicPlantedStableCredit (span)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k u e:ℕ}(R:Run G)(W:Initialize G)
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "C" => Credit.leanC

abbrev reporter (fit:h<D):SealR G:=⟨h,(primes G).F h,D,(primes G).T h,fit⟩

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (fit:h<D)(rails:Rails h k u e)(d:ℕ)(kind:Bool)(dim:d<D)(cap:d≤k):
    let Q:=reporter (G:=G) fit
    let T:=sectionAt R W kind d
    ∃α:Alma (R.family.labels.level d)→ℝ,(∀i,0≤α i) ∧ ∃Z B:Credit,
    ∀ᶠ j:ℕ in atTop,∀m K N,j ≤ m → m ≤ K → K ≤ N →
    ∀(c:Verse (R.family.labels.level d))(s:ℝ),
    ∃X:CutsP (hol G) Q.ans Q.path rails C C C C,
      X.ax=L ∧ X.tx=O ∧ X.m=m ∧ X.ceilC=K ∧ X.N=N ∧ X.vesselsC.y=zz L ∧
      X.pt=s • Shrine (plate T dim) c ∧ X.fuel=|s| * charge e c α ∧
      (∀a:ℝ,a • X.pt=centralL L O N m K Q (PermuteLens L O Q N m (publicDose Q X a))+
        a • X.springP X.i) ∧
      ∀(a:ℝ) t,t≤e → ∀i,‖coeff t (publicDose Q X a i)‖ ≤
        Fintype.card (Alma Q.F)*B.buy (zz L m)*
          ((Real.exp (span X X.i))^h*Z.buy X.Age*(|a| * (|s| * charge e c α))):=by
  intro Q T
  obtain ⟨α,nα,admitted⟩:=WilsonIndependentMatchedFiledIncome.named R W kind d dim cap e u
  obtain ⟨Z,zpay⟩:=WilsonPositionProgramTrialHomeDose.wage (hol G) Q rails C C C C
  obtain ⟨B,bpay⟩:=WilsonPositionProgramTrialFittedWick.original (hol G) Q e C C C
  refine ⟨α,nα,Z,B,?_⟩
  let labels:Fin 1→ℕ:=fun _=>h
  let dims:Fin 1→ℕ:=fun _=>D
  have count:capP (deck (G:=G) labels dims (fun _=>fit))≤k:=by
    simpa [capP,asp,deck,BayV,labels,dims] using rails.hk
  filter_upwards [WilsonMarkedIndependentNormalizedElection.original R simple v funded fit rails
    labels dims (fun _=>fit) count] with j sale
  obtain ⟨book,chair,levels,chart,clock,seat,agrees,_,_,frames,_⟩:=sale
  intro m K N early before live c s
  let P:=Shrine (plate T dim) c
  obtain ⟨legal,purse,all⟩:=admitted c
  have home:chair.L.V.anchor ≤ m:=seat ▸ early
  have epoch:m+(K-m)=K:=by omega
  let X:=WilsonIndependentMatchedKernelResidual.diagonal chair book agrees m (K-m) N home
    (by omega) (s • P) (legal.μ s) (|s| * charge e c α) (mul_nonneg (abs_nonneg _) purse)
    (fun t r ht=>(show Award (P.2 t r) _ (charge e c α) from all t r ht).μ s)
  have atK:X.ceilC=K:=epoch
  have A:X.ax=L:=levels
  have O':X.tx=O:=chart
  have input:X.fuel=|s| * charge e c α:=rfl
  let bidder: AheadT (hol G) chair.L.V C C Q C:=(frames 0).some
  have live':bidder.p.f.arch.V.anchor ≤ m:=bidder.p.tap ▸ home
  have wallet:∀i j,‖Wray X.ax X.tx Q.ans Q.path X.N X.m i j‖≤B.buy (zz L m):=by
    have quote:=(bpay bidder.p.f.arch bidder.stamps m N live' (before.trans live)).1
    change ∀i j,‖Wray chair.L.V.draws chair.L.V.paid Q.ans Q.path N m i j‖≤B.buy (zz L m)
    simpa only [Realm.cash,bidder.p.lands,bidder.p.modes,bidder.p.depths,clock] using quote
  refine ⟨X,A,O',rfl,atK,rfl,clock,rfl,input,?_,?_⟩
  · intro a
    have source:=(WilsonPositionProgramTrialHomeDose.original Q X a).2.2
    rw [A,O',atK] at source
    exact source
  · intro a t ht i
    simpa only [input] using zpay X a (B.buy (zz L m)) wallet t ht i

end YM.Integration.WilsonPositionProgramTrialNativeHome
end
