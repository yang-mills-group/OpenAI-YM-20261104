import YM.Integration.WilsonPositionProgramOrderedPinReturn

/-! Both programmes plant their complete normalized fields at K. One cold
programme inherits its old vacuum from N, while the other's vacuum begins
at that same K. The reporting vector is common to their distinct lifts. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentMatchedRestartVacuum
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

def reading (L:Levels G)(O:ChartRatio G)(Q:Fin (a+1)→SealR G)(F:Wilt Q)
    (b:Herit Q)(m K N:ℕ)(y:ℝ)(o:CellR):=
  loadK L O F (normalized L O Q b m N) m K N y o

def Receipt (Q:Fin (a+1)→SealR G)(L:Levels G)(O:ChartRatio G)(clock:ℕ→ℝ)
    (j e u:ℕ)(C wallet:Credit):Prop:=
  ∀m K N:ℕ,∀(b:Herit Q)(F:Wilt Q)(B:Fin (a+1)→ℝ)(Z y:ℝ)(o:CellR),
    j ≤ m → m ≤ K → K ≤ N → clock m ≤ Z → Bough Q F y Z B →
    Fringed (capP Q) e u 1 (C.buy Z*∏i,B i*(wallet.buy (clock m)*fee b e i))
      (trailC L.S m K) (reading L O Q F b m K N y o) (reading L O Q F b m K K y o)

/-- Eligible independent courses may differ beyond the common report. The
inequality itself uses exactly the two original histories of the selected course. -/
theorem appointed (H:Hol G)(Q:Fin (a+1)→SealR G)(E W V W' L:Credit)(e u:ℕ):
    ∃C wallet:Credit,∀(A:Realm G (e+1) E),FramesR H A W V Q L → HorizonP H A W V Q →
      SpringD A (capP Q) u (capP Q+2) W' → Dormitory A (capP Q) u L →
      Receipt Q A.draws A.paid A.y A.anchor e u C wallet:=by
  obtain ⟨C,contract⟩:=topDay H Q E W V W' L e u
  obtain ⟨wallet,fields⟩:=steering H Q e E W V L
  refine ⟨C,wallet,?_⟩
  intro A frames ready spring dorm m K N b F B Z y o awake base fine room shape
  have bound:=fields A frames m awake (fee b e) (fun _=>b)
    (WilsonPositionProgramNormalizedMaster.shipped b e A.draws.S m)
  have charged:=contract A ready spring dorm m K K N K F (normalized A.draws A.paid Q b m N)
    (normalized A.draws A.paid Q b m K) (fun i=>wallet.buy (A.y m)*fee b e i) B
    Z y (trailC A.draws.S m K) o awake base base fine le_rfl room shape le_rfl
    (bound N K K base fine le_rfl)
  simpa only [min_eq_left fine,min_self,reading] using charged

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (p:h<D)(rails:Rails h k u e)(l d:Fin (a+1)→ℕ)(admit:∀i,l i<d i)
    (cap:capP (deck (G:=G) l d admit)≤k):
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

end YM.Integration.WilsonIndependentMatchedRestartVacuum
