import YM.Integration.WilsonOlderFreshHybridClock
import YM.Integration.WilsonPositionProgramNormalizedMaster

/-! Hear the nonbare K-planted programme on its earlier weak date, with every
rank entering the original normalized transfer and one charge for all its first joins. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOlderFreshHybridOneLaw
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open scoped Topology BigOperators Classical
variable {G : Gauge} {a h D k u e : ℕ}

open WilsonOriginalPublicTwoTopJoined (Hearing)
open WilsonMarkedIndependentNormalizedElection (deck normalized)


theorem bounded (G:Gauge)(k e u:ℕ)(E W:Credit):
    ∃V:Credit,∀(S:Realm G (e+1) E), Dormitory S k u W →
      ∀(b K N:ℕ)(η:ℕ→ℝ)(Z A δ:ℝ),Escort S b K η → PadRank S b K Z → K ≤ N →
      ∀(X Y:Era G ℝ),Fringed k e u (η K) A δ X Y →
        Fringed k e u (η b) (V.buy Z*A) δ
          (cruises S.draws S.paid N k K b X) (cruises S.draws S.paid N k K b Y):=by
  obtain ⟨V,trial⟩:=bulkCert G k e u E W
  refine ⟨V,?_⟩
  intro S dorm b K N η Z A δ esc ran kn X Y earned
  have dif := earned.inkV.sub earned.pen
  have law := cruisePlus S.draws esc.lane S.hG S.green kn earned.inkV earned.pen
  have pay:Saturation e 0 u (X-Y).2 (η K) (A*δ):=fun i hi r _ => (earned.heapS i r hi).toll
  refine ⟨cruising S.draws S.hG S.green esc.lane kn earned.inkV,
    cruising S.draws S.hG S.green esc.lane kn earned.pen,earned.crest,?_⟩
  intro i r hi
  have test:=trial i hi r S dorm b K η N Z esc ran kn
  refine ⟨test X A earned.inkV earned.nn earned.f_l.2,
    test Y A earned.pen earned.nn earned.f_r.2,?_⟩
  have diff:=test (X-Y) (A*δ) dif (mul_nonneg earned.nn earned.crest) pay
  rw [law,←mul_assoc] at diff
  exact diff

def Regauged (Q:Fin (a+1)→SealR G)(L:Levels G)(O:ChartRatio G)(clock:ℕ→ℝ)
    (j e u:ℕ)(V:Credit):Prop:=
  ∀(b m K N:ℕ),j ≤ b → b ≤ m → m ≤ K → K ≤ N → ∀(Z A δ:ℝ),Compar L.S clock b K ≤ Z →
    ∀(X:Herit Q)(F:Wilt Q)(y:ℝ)(o:CellR)(P:Era G ℝ),
    let W:=normalized L O Q X m N
    Fringed (capP Q) e u 1 A δ P (Ashore Q L O F W m K N y o) →
    Fringed (capP Q) e u 1 (V.buy Z*A) δ (cruises L O N (capP Q) K b P)
      (cruises L O N (capP Q) m b (loadK L O F W m K N y o))

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (big:h<D)(rails:Rails h k u e)(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)
    (cap:capP (deck (G:=G) l d fit)  ≤  k):
    let Q:=deck (G:=G) l d fit
    let L:=R.family.path.levels
    ∃V:Credit,∀ᶠj:ℕ in atTop,Regauged Q L R.metals.O (zz L) j e u V:=by
  intro Q L
  obtain ⟨V,use⟩:=bounded G (capP Q) e u Credit.leanC Credit.leanC
  refine ⟨V,?_⟩
  filter_upwards [WilsonMarkedIndependentNormalizedElection.original R simple v funded big rails l d fit cap]
    with j elected
  obtain ⟨T,Y,lv,rt,ck,date,_,dorm,_,_,_⟩:=elected
  let S:=Y.L.V
  have useR:Regauged Q S.draws S.paid S.y S.anchor e u V:=by
    intro b m K N jb bm mk kn Z A δ geo X F y o P W signed
    have base:=PadRank.frugal S jb (bm.trans mk)
    have pad:PadRank S b K Z:=⟨fun i a h=>(base.year i a h).trans geo,base.lengthS.trans geo⟩
    have heard:=use S dorm b K N (fun _=>1) Z A δ (oldGuard jb (bm.trans mk)) pad kn _ _ signed
    rwa [←cruisesMore S.draws S.paid _ bm mk]
  simpa only [S,lv,rt,ck,date] using useR

end YM.Integration.WilsonOlderFreshHybridOneLaw
