import YM.Integration.WilsonIndependentMatchedRestartVacuum

/-! Both programmes plant their complete normalized fields at K. One cold
programme inherits its old vacuum from N, while the other's vacuum begins
at that same K. The reporting vector is common to their distinct lifts. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentMatchedBufferedVacuum
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonPositionProgramNormalizedMaster (fee)
open scoped Topology BigOperators Classical
variable {G:Gauge}{a h D k u e:ℕ}

open WilsonIndependentMatchedRestartVacuum (reading)

/-- Fully stopped ordinary reading. Each of the two legs of this comparison
uses its own complete vacuum prior and its own compensated section. -/
def stopped (L:Levels G)(O:ChartRatio G)(Q:Fin (a+1)→SealR G)(F:Wilt Q)
    (b:Herit Q)(m K N stop:ℕ)(y:ℝ)(o:CellR):=
  cruises L O N (capP Q) m stop (reading L O Q F b m K N y o)

def Receipt (Q:Fin (a+1)→SealR G)(L:Levels G)(O:ChartRatio G)(clock:ℕ→ℝ)
    (j e u:ℕ)(C wallet:Credit):Prop:=
  ∀m K upper N N' stop:ℕ,∀(b:Herit Q)(F:Wilt Q)(B:Fin (a+1)→ℝ)(Z y:ℝ)(o:CellR),
    j ≤ stop → stop ≤ m → m ≤ K → K ≤ upper → upper ≤ N → upper ≤ N' →
    Compar L.S clock stop m ≤ Z → Bough Q F y Z B →
    Fringed (capP Q) e u 1 (C.buy Z*∏i,B i*(wallet.buy (clock m)*fee b e i))
      (trailC L.S m upper) (stopped L O Q F b m K N stop y o) (stopped L O Q F b m K N' stop y o)

theorem appointed (H:Hol G)(Q:Fin (a+1)→SealR G)(E W V W' L:Credit)(e u:ℕ):
    ∃C wallet:Credit,∀(A:Realm G (e+1) E),FramesR H A W V Q L → HorizonP H A W V Q →
      SpringD A (capP Q) u (capP Q+2) W' → Dormitory A (capP Q) u L →
      Receipt Q A.draws A.paid A.y A.anchor e u C wallet:=by
  obtain ⟨C,contract⟩:=topDay H Q E W V W' L e u
  obtain ⟨S,stay⟩:=waveSeen G (capP Q) e u E L
  obtain ⟨wallet,fields⟩:=steering H Q e E W V L
  refine ⟨S.prodC C,wallet,?_⟩
  intro A frames ready spring dorm m K upper N N' stop b F B Z y o awake older base buffer fine fine' room shape
  have phase:=PadRank.frugal A awake older
  have pad:PadRank A stop m Z:=⟨fun i hi hj=>(phase.year i hi hj).trans room,phase.lengthS.trans room⟩
  have bound:=fields A frames m (awake.trans older) (fee b e) (fun _=>b)
    (WilsonPositionProgramNormalizedMaster.shipped b e A.draws.S m)
  have charged:=contract A ready spring dorm m K upper N N' F (normalized A.draws A.paid Q b m N)
    (normalized A.draws A.paid Q b m N') (fun i=>wallet.buy (A.y m)*fee b e i) B
    Z y (trailC A.draws.S m upper) o (awake.trans older) base (base.trans buffer) fine fine'
    (pad.year m older le_rfl) shape le_rfl (bound N N' upper (base.trans buffer) fine fine')
  simp only [min_eq_left (buffer.trans fine),min_eq_left (buffer.trans fine')] at charged
  have received:=stay A dorm stop m _ upper N N' _ _ Z (oldGuard awake older) pad (base.trans buffer) fine fine' le_rfl _ _ charged
  simpa only [stopped,WilsonIndependentMatchedRestartVacuum.reading,Credit.products,mul_assoc] using received

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (p:h<D)(rails:Rails h k u e)(l d:Fin (a+1)→ℕ)(admit:∀i,l i<d i)
    (cap:capP (deck (G:=G) l d admit) ≤ k):
    let Q:=deck (G:=G) l d admit
    let L:=R.family.path.levels
    ∃C wallet:Credit,∀ᶠ j:ℕ in atTop,Receipt Q L R.metals.O (zz L) j e u C wallet:=by
  intro Q L
  obtain ⟨C,wallet,run⟩:=appointed (hol G) Q Credit.leanC Credit.leanC Credit.leanC Credit.leanC Credit.leanC e u
  refine ⟨C,wallet,?_⟩
  filter_upwards [WilsonMarkedIndependentNormalizedElection.original R simple v funded p rails l d admit cap] with j issued
  obtain ⟨W,Y,levels,ratio,clock,date,_,dorm,spring,frames,ready⟩:=issued
  have earned:=run Y.L.V frames ready spring dorm
  rwa [levels,ratio,clock,date] at earned

end YM.Integration.WilsonIndependentMatchedBufferedVacuum
