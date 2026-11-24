import YM.Integration.WilsonIndependentConditionedPairProbeSemester
import YM.Integration.WilsonIndependentMatchedFiledIncome

/-! The two input appointments accept actual paid finite-section fields at K, with the same unmarked N clock on either side of the independent cutoff comparison. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedPairProbeInput
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Mer.Patrol RG.Supply Next.Foundations WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Ticket
open PhysicalNext.Repeat.Legato XSpace.Rose XSpace.Cirrus XSpace
open WilsonIndependentConditionedPairProbeSemester (Home)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonIndependentMatchedNamedPair (sectionAt)
open scoped BigOperators Topology Classical
variable {G:Gauge}{e k u₀:ℕ}
local notation "C" => Credit.leanC

def plant {R:Run G}{Q:SealR G}{own:Rails Q.h k u₀ e}{j:ℕ}(port:Home R Q own j)
    (m K N:ℕ)(live:j ≤ m)(cut:m ≤ K)(vac:K ≤ N)(P:TowerS G Q.D)(sp:On k P)
    (A:ℝ)(nn:0 ≤ A)(root:∀i r,i ≤ e→Fruit 0 1 u₀ (P.2 i r) A):
    CutsP (hol G) Q.ans Q.path own C C C C where
  L:=port.source
  L':=port.origin
  he:=port.one
  m:=m
  i:=K-m
  b:=K
  N:=N
  M:=N
  ha:=port.anchor.le.trans live
  hc:=by omega
  hn:=vac
  hm:=vac
  pt:=P
  pt':=P
  sp:=sp
  sp':=sp
  fuel:=A
  hf:=nn
  toll i r hi:=YieldP.same (root i r hi) (trail_pos ..).le

theorem named (R:Run G)(W:Initialize G)(survey:Bool)(d D:ℕ)(path:d<D)(own:Rails d k u₀ e):
    let Q:=BayV (primes G) d D path
    let T:=sectionAt R W survey d
    ∃A:Alma (R.family.labels.level d)→ℝ,(∀i,0 ≤ A i) ∧
      ∀(j m K N:ℕ)(port:Home R Q own j),j ≤ m → m ≤ K → K ≤ N →
      ∀c:Verse (R.family.labels.level d),
        ∃X:CutsP (hol G) Q.ans Q.path own C C C C,
          X.L=port.source ∧ X.L'=port.origin ∧ X.ax=R.family.path.levels ∧ X.tx=R.metals.O ∧
          X.m=m ∧ X.ceilC=K ∧ X.N=N ∧ X.M=N ∧ X.b=K ∧
          X.pt=Shrine (plate T path) c ∧ X.pt'=X.pt ∧ X.fuel=charge e c A:=by
  intro Q T
  obtain ⟨A,positive,grant⟩:=WilsonIndependentMatchedFiledIncome.named R W survey d path own.hk e u₀
  refine ⟨A,positive,?_⟩
  intro j m K N port live cut vac c
  obtain ⟨sp,hn,roots⟩:=grant c
  let X:=plant port m K N live cut vac _ sp _ hn roots
  exact ⟨X,rfl,rfl,port.levels,port.reset,rfl,Nat.add_sub_of_le cut,rfl,rfl,rfl,rfl,rfl,rfl⟩

end YM.Integration.WilsonIndependentConditionedPairProbeInput
