import YM.Integration.WilsonIndependentSpoutMasterObserved
/-! The reported cutoff change from the very same normalized N-born vector
on a buffered vacuum to the fresh K vacuum, with U selected before all data. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedReportedExitWindow
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonIndependentSpoutMasterAppointments (Grants)
open WilsonIndependentSpoutMasterCutoff (Earned)
open WilsonIndependentSpoutMasterClockFees (Paid)
open WilsonPositionProgramNormalizedMaster (fee)
open WilsonIndependentSpoutMasterObserved (observed cutoff)
open scoped BigOperators Classical
variable {G:Gauge}{n e u:ℕ}(R:Run G)(l d:Fin (n+1)→ℕ)(admit:∀i,l i<d i)
local notation "Q" => deck (G:=G) l d admit
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O

theorem triangle (a b c:ℂ):‖a-c‖ ≤ ‖a-b‖+‖b-c‖:=by
  rw [show a-c=(a-b)+(b-c) by abel]
  exact norm_add_le ..

theorem before (simple:G.Simple){j:ℕ}{C W T D:Credit}(sale:Earned R l d admit j e u C W)
    (clocks:Paid R j e T)(fields:Grants R l d admit j)(drift:WilsonIndependentSpoutMasterUpperClocks.Paid R j e D)
    (v m K q:ℕ)(counts cap:Fin (n+1)→ℝ)(Z ε:ℝ)(active:j ≤ v)(older:v ≤ m)(mk:m ≤ K)
    (optic:Compar (L).S (zz L) v m ≤ Z)(order:q ≤ e)(pos:0<ε):
    ∀ᶠ U:ℕ in atTop,K ≤ U ∧ ∀(N M:ℕ)(b:Herit Q)(F:Wilt Q)(y:ℝ)(o:CellR),U ≤ N → U ≤ M →
    (∀i,fee b e i ≤ cap i) → Bough Q F y Z counts → ∀g:ℝ,|g| ≤ 1 →
    ‖observed L O N m v q g (stopped L O Q F b m K M v y o)-
      observed L O K m v q g (stopped L O Q F b m K K v y o)‖ ≤
      ε+cutoff R l d admit C W T v m K q g Z counts b:=by
  filter_upwards [WilsonIndependentSpoutMasterBufferedWindow.paid R l d admit sale drift v m K counts cap Z
    active older mk optic q order ε pos] with U selected
  refine ⟨selected.1,?_⟩
  intro N M b F y o un um budget healthy g small
  let Y:=stopped L O Q F b m K M v y o
  have clock:=selected.2 N M b F y o un um budget healthy g small
  have edge:=WilsonIndependentSpoutMasterCash.original R l d admit simple sale clocks fields v m K M
    b F counts Z y o active older mk (selected.1.trans um) optic healthy q order g small
  apply (triangle _ (observed L O M m v q g Y) _).trans
  apply add_le_add
  · unfold WilsonIndependentSpoutMasterObserved.observed
    rw [←WilsonIndependentSpoutMasterObserved.cash_sub]
    exact clock
  · unfold WilsonIndependentSpoutMasterObserved.observed
    rw [←WilsonIndependentSpoutMasterObserved.cash_sub]
    exact edge

end YM.Integration.WilsonIndependentMatchedReportedExitWindow
