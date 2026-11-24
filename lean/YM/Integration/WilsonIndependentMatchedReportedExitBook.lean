import YM.Integration.WilsonIndependentMatchedReportedExitWindow
/-! Every structural normalized-pivot return on the same original
construction, chosen for a finite actual proper-face roster in advance. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedReportedExitBook
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentSpoutMasterAppointments (Grants)
open WilsonIndependentSpoutMasterCutoff (Earned)
open scoped BigOperators Classical
variable {G:Gauge}{n e u k h D:ℕ}{T:Type*}[Fintype T]
local notation "I" => Fin (n+1)

def Licensed (R:Run G)(l d:I→ℕ)(admit:∀i,l i<d i)(size:T→ℕ)(leg:∀s,Fin (size s+1)→I)
    (floor e u:ℕ)(C W:T→Credit):Prop:=
  ∀s,Earned R (l ∘ leg s) (d ∘ leg s) (fun i=>admit (leg s i)) floor e u (C s) (W s) ∧
     Grants R (l ∘ leg s) (d ∘ leg s) (fun i=>admit (leg s i)) floor

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(income:FundedMarkedCoverRows.prices v R.kit)
    (p:h<D)(rails:Rails h k u e)(l d:I→ℕ)(admit:∀i,l i<d i)(size:T→ℕ)(leg:∀s,Fin (size s+1)→I)
    (cap:∀s,capP (deck (G:=G) (l ∘ leg s) (d ∘ leg s) (fun i=>admit (leg s i))) ≤ k):
    ∃(C W:T→Credit)(E:Credit),∀ᶠ floor:ℕ in atTop,
    Licensed R l d admit size leg floor e u C W ∧ WilsonIndependentSpoutMasterUpperClocks.Paid R floor e E:=by
  have earn s:=WilsonIndependentSpoutMasterAppointments.original R (l ∘ leg s) (d ∘ leg s)
    (fun i=>admit (leg s i)) simple v income p rails (cap s)
  choose C W _ sale using earn
  let l₁:Fin 1 → ℕ:=fun _=>h
  let d₁:Fin 1 → ℕ:=fun _=>D
  have one:capP (deck (G:=G) l₁ d₁ (fun _=>p)) ≤ k:=by
    simpa [capP,asp,deck,BayV,l₁,d₁] using rails.hk
  obtain ⟨E,clock⟩:=WilsonIndependentSpoutMasterUpperClocks.original R simple v income p rails l₁ d₁ (fun _=>p) one
  refine ⟨C,W,E,?_⟩
  filter_upwards [Filter.eventually_all.2 sale,clock] with floor receipts here
  exact ⟨fun s=>⟨(receipts s).1,(receipts s).2.2⟩,here⟩

end YM.Integration.WilsonIndependentMatchedReportedExitBook
