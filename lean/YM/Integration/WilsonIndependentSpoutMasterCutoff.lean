import YM.Integration.WilsonIndependentSpoutNormalizedMaster
import YM.Integration.WilsonIndependentMatchedInheritedComparison
/-! The regulated error between the complete funded master at the buffer and its fresh K-top on the original course. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutMasterCutoff
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


open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonIndependentSpoutScalarLedger (ground)
open WilsonIndependentMatchedInheritedComparison (scalar)
open WilsonIndependentSpoutPhysicalClock (station)

def rent (C wallet:Credit)(clock:ℕ→ℝ)(Q:Fin (a+1)→SealR G)(b:Herit Q)
    (e m:ℕ)(y:ℝ)(B:Fin (a+1)→ℝ):ℝ:=C.buy y*∏i,B i*(wallet.buy (clock m)*fee b e i)

variable (R:Run G)(l d:Fin (a+1)→ℕ)(admit:∀i,l i<d i)
local notation "Q₀" => deck (G:=G) l d admit
local notation "L₀" => R.family.path.levels

def Earned (j e u:ℕ)(C wallet:Credit):Prop:=
  ∀(m K N' host:ℕ)(b:Herit Q₀)(F:Wilt Q₀)(B:Fin (a+1)→ℝ)(Z y:ℝ)(o:CellR),
    j ≤ host → host ≤ m → m ≤ K → K ≤ N' → Compar (L₀).S (zz L₀) host m ≤ Z →
    Bough Q₀ F y Z B →
    let old:=stopped L₀ R.metals.O Q₀ F b m K N' host y o
    let fresh:=stopped L₀ R.metals.O Q₀ F b m K K host y o
    let bill:=rent C wallet (zz L₀) Q₀ b e m Z B
    Fringed (capP Q₀) e u 1 bill (trailC (L₀).S m K) old fresh ∧
    ∀q ≤ e,‖PowerSeries.coeff q (ground old)-PowerSeries.coeff q (ground fresh)‖ ≤ bill*trailC (L₀).S m K

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (p:h<D)(rails:Rails h k u e)(cap:capP Q₀ ≤ k):
    ∃C wallet:Credit,∀ᶠ j:ℕ in atTop,Earned R l d admit j e u C wallet:=by
  obtain ⟨C,wallet,paid⟩:=WilsonIndependentMatchedBufferedVacuum.original R simple v funded p rails l d admit cap
  refine ⟨C,wallet,?_⟩
  filter_upwards [paid] with j issued
  intro m K N' host b F B Z y o awake older base buffered optical fit
  have joint:=issued m K K N' K host b F B Z y o awake older base le_rfl buffered le_rfl optical fit
  refine ⟨joint,fun q hq=>?_⟩
  simpa only [ground,WilsonOlderFreshSoftSocketKinetic.reading,PowerSeries.coeff_mk,rent] using scalar joint q hq Fin.elim0
end YM.Integration.WilsonIndependentSpoutMasterCutoff
end
