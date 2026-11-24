import YM.Integration.WilsonIndependentSpoutMasterReport

/-! Both inverse clocks on the normalized measurement share a cutoff rate on the actual optical interval. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutMasterUpperClocks
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Source Source.Drops Labels
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentSpoutMasterReport (report)
open WilsonIndependentSpoutScalarLedger (ground)
open scoped Classical BigOperators Topology
variable {G:Gauge}{n h D k u e:ℕ}

def Paid (R:Run G)(j e:ℕ)(C:Credit):Prop:=
  let A:=R.family.path.levels
  ∀(v m U N M i b:ℕ),j ≤ v → v ≤ m → m ≤ U → U ≤ N → U ≤ M → i ≤ e → b ≤ e →
    twain (C.buy (Compar A.S (zz A) v m)) (trailC A.S m U)
      (PowerSeries.coeff i ((relativeC A R.metals.O N v (m-v))^b))
      (PowerSeries.coeff i ((relativeC A R.metals.O M v (m-v))^b))

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (p:h<D)(rails:Rails h k u e)(l d:Fin (n+1)→ℕ)(admit:∀i,l i<d i)(cap:capP (deck (G:=G) l d admit)≤k):
    ∃C:Credit,∀ᶠ j:ℕ in atTop,Paid R j e C:=by
  let S:SectionData ((primes G).F h):=(primes G).T h
  obtain ⟨C,clock⟩:=SeasonC e (hol G) S p Credit.leanC Credit.leanC Credit.leanC
  refine ⟨C,?_⟩
  filter_upwards [WilsonMarkedIndependentNormalizedElection.original R simple v funded p rails l d admit cap] with j joint
  obtain ⟨W,Y,levels,ratio,y,anchor,agrees,_⟩:=joint
  intro v m U N M i b awake vm mU UN UM ie be
  let I:WindowS G (e+1) Credit.leanC:=
    ⟨Y.L.V,v,m-v,N,M,U,by simpa only [anchor] using awake,by omega,UN,UM⟩
  let B:CourseS (hol G) S p e Credit.leanC Credit.leanC Credit.leanC:=⟨W,I,by rw [agrees]⟩
  have grant:=clock B i b ie be
  change twain (C.buy (I.Age)) (I.cab)
    (PowerSeries.coeff i ((relativeC W.arch.V.draws W.arch.V.paid N v (m-v))^b))
    (PowerSeries.coeff i ((relativeC W.arch.V.draws W.arch.V.paid M v (m-v))^b)) at grant
  dsimp only [I,WindowS.Age,WindowS.cab,Realm.tempC] at grant
  rw [agrees,levels,ratio,y,show v+(m-v)=m by omega] at grant
  exact grant

end YM.Integration.WilsonIndependentSpoutMasterUpperClocks
end
