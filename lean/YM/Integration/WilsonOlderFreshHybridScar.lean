import YM.Integration.WilsonOriginalPublicTwoTopJoined
import YM.Integration.WilsonPositionProgramNormalizedMaster

/-! Hear the nonbare K-planted programme on its earlier weak date, with every
rank entering the original normalized transfer and one charge for all its first joins. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOlderFreshHybridScar
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

def Stopped (Q:Fin (a+1)→SealR G)(L:Levels G)(O:ChartRatio G)(clock:ℕ→ℝ)
    (j e u:ℕ)(C V wallet:Credit):Prop:=
  ∀(b m K N:ℕ)(X:Herit Q)(F:Wilt Q)(B:Fin (a+1)→ℝ)(Z y:ℝ)(o:CellR),
    j ≤ b → b ≤ m → m ≤ K → K ≤ N → Compar L.S clock b m ≤ Z → Bough Q F y Z B →
    let W:=normalized L O Q X m N
    let T:=∏i,B i*(wallet.buy (clock m)*WilsonPositionProgramNormalizedMaster.fee X e i)
    let δ:=trailC L.S m K
    Fringed (capP Q) e u 1 (V.buy Z*(2*(C.buy Z*T))) δ
      (locale o (LodeStar L O F W m b N y))
      (cruises L O N (capP Q) m b (loadK L O F W m K N y o))

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (big:h<D)(rails:Rails h k u e)(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)
    (cap:capP (deck (G:=G) l d fit) ≤ k):
    let Q:=deck (G:=G) l d fit
    let L:=R.family.path.levels
    ∃C V wallet:Credit,∀ᶠj:ℕ in atTop,Stopped Q L R.metals.O (zz L) j e u C V wallet:=by
  intro Q L
  obtain ⟨C,C',wallet,sale⟩:=WilsonOriginalPublicTwoTopJoined.original R simple v funded big rails l d fit cap
  obtain ⟨V,stop⟩:=waveSeen G (capP Q) e u Credit.leanC Credit.leanC
  refine ⟨C,V,wallet,?_⟩
  filter_upwards [sale,WilsonMarkedIndependentNormalizedElection.original R simple v funded big rails l d fit cap]
    with j priced elected
  obtain ⟨T,Y,lv,rt,ck,date,_,dorm,_,_,frames⟩:=elected
  let S:=Y.L.V
  have hear:Hearing Q S.draws S.paid S.y S.anchor e u C C' wallet:=by
    change Hearing Q Y.L.V.draws Y.L.V.paid Y.L.V.y Y.L.V.anchor e u C C' wallet
    simpa only [lv,rt,ck,date] using priced
  have receive:Stopped Q S.draws S.paid S.y S.anchor e u C V wallet:=by
    intro b m K N X F B Z y o hb bm mK KN room shape W T δ
    have open':S.anchor ≤ m:=hb.trans bm
    have dates:=PadRank.frugal S hb bm
    have pad:PadRank S b m Z:=⟨fun i hi hj=>(dates.year i hi hj).trans room,dates.lengthS.trans room⟩
    have normal:=hear m K N X F B Z y o open' mK KN (pad.year _ bm le_rfl) shape
    rw [capsizing frames F W o open' bm (mK.trans KN)]
    exact stop S dorm b m (fun _=>1) K N N _ δ Z (oldGuard hb bm) pad mK KN KN le_rfl _ _ normal.2.1
  change Stopped Q Y.L.V.draws Y.L.V.paid Y.L.V.y Y.L.V.anchor e u C V wallet at receive
  simpa only [lv,rt,ck,date] using receive
end YM.Integration.WilsonOlderFreshHybridScar
end
