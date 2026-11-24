import YM.Integration.WilsonIndependentSpoutMasterClockFees

/-! The actual original course authorizes every compact basis product at either vacuum opening. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutMasterAppointments
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Source Source.Drops Labels
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentSpoutMasterArms (arm)
open WilsonIndependentSpoutMasterCutoff (Earned)
open WilsonIndependentSpoutMasterClockFees (Paid)
open scoped Classical BigOperators Topology
variable {G:Gauge}{n h D k u e:ℕ}
variable (R:Run G)(l d:Fin (n+1)→ℕ)(admit:∀i,l i<d i)
local notation "Q₀" => deck (G:=G) l d admit
local notation "L₀" => R.family.path.levels

def Grants (j:ℕ):Prop:=∀i (φ:Rarity (Q₀ i).D)(b:(Q₀ i).Rider)(m K N:ℕ)(y:ℝ)(o:CellR),
  j ≤ K → K ≤ N → Auth (Q₀ i).h (arm L₀ R.metals.O (Q₀ i) φ b m K N y o)

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (p:h<D)(rails:Rails h k u e)(cap:capP Q₀ ≤ k):
    ∃C W B:Credit,∀ᶠ j:ℕ in atTop, Earned R l d admit j e u C W ∧ Paid R j e B ∧ Grants R l d admit j:=by
  obtain ⟨C,W,earn⟩:=WilsonIndependentSpoutMasterCutoff.original R l d admit simple v funded p rails cap
  obtain ⟨B,payment⟩:=WilsonIndependentSpoutMasterClockFees.original R simple v funded p rails l d admit cap
  refine ⟨C,W,B,?_⟩
  filter_upwards [earn,payment,WilsonMarkedIndependentNormalizedElection.original R simple v funded p rails l d admit cap] with j shown funds joint
  refine ⟨shown,funds,?_⟩
  obtain ⟨_,Y,levels,ratio,_,anchor,_,_,_,frames,_⟩:=joint
  intro i φ b m K N y o awake top
  let Z:=(frames i).some.p
  have receipt:=WilsonIndependentSpoutMasterArms.licensed (Q₀ i) Z.f.arch φ b m K N
    (by simpa only [Z.tap,anchor] using awake) top y o
  rwa [Z.lands,Z.modes,levels,ratio] at receipt
end YM.Integration.WilsonIndependentSpoutMasterAppointments
end
