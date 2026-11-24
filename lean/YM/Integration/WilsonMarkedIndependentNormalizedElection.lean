import YM.Integration.FundedMarkedCoverRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentNormalizedElection
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open scoped Topology BigOperators Classical
variable {G:Gauge}{a h D k u e:ℕ}(R:Run G)

abbrev deck (h d:Fin (a+1)→ℕ)(p:∀i,h i<d i):Fin (a+1)→SealR G:=
  fun i=>BayV (primes G) (h i) (d i) (p i)

def normalized (L:Levels G)(O:ChartRatio G)(Q:Fin (a+1)→SealR G)(X:Herit Q)(m N:ℕ):Herit Q:=
  fun i=>PermuteLens L O (Q i) N m (X i)

theorem source (h:ℕ):(primes G).T h=R.family.localSection h:=rfl


theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (p:h<D)(rails:Rails h k u e)(l d:Fin (a+1)→ℕ)(admit:∀i,l i<d i)
    (cap:capP (deck (G:=G) l d admit)≤k):
    let Q:=deck (G:=G) l d admit
    let S:SectionData ((primes G).F h):=(primes G).T h
    ∀ᶠ j:ℕ in atTop, ∃(W:ChorusLine (hol G) S p e Credit.leanC Credit.leanC Credit.leanC)
      (Y:Torch (hol G) S p rails Credit.leanC Credit.leanC Credit.leanC),
      Y.L.V.draws=R.family.path.levels ∧ Y.L.V.paid=R.metals.O ∧ Y.L.V.y=zz R.family.path.levels ∧
      Y.L.V.anchor=j ∧ W.arch=Y.L ∧ Dormitory Y.L.V (capP Q) u Credit.leanC ∧
      SpringD Y.L.V (capP Q) u (capP Q+2) Credit.leanC ∧
      FramesR (hol G) Y.L.V Credit.leanC Credit.leanC Q Credit.leanC ∧ HorizonP (hol G) Y.L.V Credit.leanC Credit.leanC Q:=by
  intro Q S
  obtain ⟨chartEq,floor,_,fees,_⟩:=funded
  have awards:=reported (hol G) (primes G) floor fees
  filter_upwards [PortsTogether simple (chart_ok G) R.alloy.B.valid awards tendsto_id p rails Q (fun _=>rfl) cap] with j filed
  obtain ⟨W,Y,levels,ratio,calendar,start,_,agree,dorm,spring,frames,ready⟩:=filed
  refine ⟨W,Y,agree ▸ levels,?_,agree ▸ calendar,agree ▸ start,agree,dorm,spring,frames,ready⟩
  exact agree ▸ ratio.trans chartEq.symm

end YM.Integration.WilsonMarkedIndependentNormalizedElection
end
