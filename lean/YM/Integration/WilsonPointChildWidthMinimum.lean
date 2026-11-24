import YM.Integration.WilsonPointChildWidthPortfolio

/-! A canonical real price for a whole funded roster. It is chosen from
    its signed rooted tensor before any quantitative calendar is invoked. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildWidthMinimum
open YM FormalBulk08 Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Dove Sierra
open PhysicalNext.Repeat.Legato Next.Foundations Borough
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open WilsonPointChildNormalizedWidth WilsonPointChildWidthPortfolio
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{d D:ℕ}(o:Loc G 1)(F:Frame G d)(Y:Plaza F D)(b:ℝ)(E:ℕ)

def rents:Set ℝ:={c|1≤c ∧ Wallet o F Y b E c}
def price:ℝ:=1+sInf (rents o F Y b E)

theorem paid (existsFee:∃c:ℝ,Wallet o F Y b E c):
    1≤price o F Y b E ∧ Wallet o F Y b E (price o F Y b E) ∧
    ∀c:ℝ, Wallet o F Y b E c→price o F Y b E≤1+max 1 c:=by
  let S:=rents o F Y b E
  obtain ⟨c,hs⟩:=existsFee
  have non:S.Nonempty:=⟨max 1 c,le_max_left ..,mono hs (le_max_right ..)⟩
  have bd:BddBelow S:=⟨1,fun z h=>h.1⟩
  have lb:1≤ sInf S:=le_csInf non (fun z h=>h.1)
  have near:sInf S<1+sInf S:=by linarith
  obtain ⟨v,hv,val⟩:=exists_lt_of_csInf_lt non near
  refine ⟨by change 1≤1+sInf S;linarith,mono hv.2 val.le,?_⟩
  intro z wallet
  have hz:max 1 z∈S:=⟨le_max_left ..,mono wallet (le_max_right ..)⟩
  exact add_le_add_right (csInf_le bd hz) 1

end YM.Integration.WilsonPointChildWidthMinimum
