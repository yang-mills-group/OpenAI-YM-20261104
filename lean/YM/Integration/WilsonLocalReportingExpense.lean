import YM.Integration.WilsonLocalTerminalChartRate
import YM.Integration.WilsonReportingForestMovingCount
import YM.Integration.WilsonReportingForestAngles

/-! The actual registered angle and bond-count purchases pay every signed
local vacuum Taylor expense, before the cutoff period and the forest. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalReportingExpense
open Function Filter Finset Set Lattice Wilson Tree RG RG16 MSbar.Heath Precision PertExtension OPE.Therm
open Pert.Asymptotics PhysicalNext.Repeat.Legato WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots
open WilsonReportingRegisteredAction WilsonPhysicalLocalPlaquetteForest WilsonReportingForestBlocks
open WilsonPhysicalLocalPlaquetteReserve WilsonLocalConditionalResidue
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I]

def admitted (J:Voice G) (d:I→ℕ) (m per:ℕ) (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio)
    (v:({i:T.Free|i∉moving T (incident R T d o)}:Set T.Free)→G.El) (g:ℝ) (X:↥(moving T (incident R T d o))→G.Color) :=
  ‖g•X‖ ≤ J.r ∧ WilsonLocalConditionalResidue.position T (incident R T d o) v g X ∈ cold R m per d o

theorem original (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (J:Voice G) (clear:Clear G J) (d:I→ℕ) (p:ℕ) {H W δ ε:ℝ}
    (hH:0 ≤ H) (hW:0 ≤ W) (hd:0 < δ) (he:0 < ε) :
    ∀ᶠ m:ℕ in atTop,∀N,m < N→∀per (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio),
    let E:=moving T (incident R T d o)
    let g:=regulatorRun R.family N per (m+1)
    ∀(v:({i:T.Free|i∉E}:Set T.Free)→G.El) (X Y:↥E→G.Color),
    admitted R J d m per o T v g X→admitted R J d m per o T v g Y→
    (∀i,g*‖X i‖ ≤ δ ∧ g*‖Y i‖ ≤ δ) ∧ expense p H W g X Y ≤ ε*g^p := by
  let F:=depthCap R d
  let K:=(2*J.C)*tariff (F+4)
  have j0:0 ≤ J.C := zero_le_one.trans clear.cost
  have t0:0 ≤ tariff (F+4) := by unfold tariff;positivity
  have k0:0 ≤ K := mul_nonneg (by positivity) t0
  have z0:0 ≤ countFee R d := by unfold countFee;positivity
  filter_upwards [physical_angles R simple slow J clear d,moving_count R simple slow d,
    WilsonRegisteredChartTaylorRate.logarithmic R simple slow F,
    WilsonLocalTerminalChartRate.paid R simple p 4 20 H W (countFee R d) K hH hW z0 k0 hd he] with
    m angles counted price sold N live per o T
  dsimp only;intro v X Y hx hy
  let g:=regulatorRun R.family N per (m+1)
  let E:=moving T (incident R T d o)
  let L:=(R.family.path.levels.clock.op m per).ratio.count.val
  let b:=R.family.path.levels.clock.hatBeta (m+1)
  have gp:0 < g := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson live))
  have ready (Z:↥E→G.Color) (good:admitted R J d m per o T v g Z) (e:↥E) :
      g*‖Z e‖ ≤ K*Real.log b^20*(Real.sqrt b)⁻¹ := by
    obtain ⟨i,cap⟩:=angles N live per o T v Z good.1 good.2 e
    have depth_:depth R (d i)+3 ≤ F := Finset.le_sup (f:=fun i=>depth R (d i)+3) (Finset.mem_univ i)
    have enough:extent (depth R (d i)+3) L ≤ extent F L := by unfold extent;omega
    have budget:=price per (extent (depth R (d i)+3) L) enough
    calc
      _=‖Z e‖*g:=mul_comm ..
      _≤(2*J.C)*(area (extent (depth R (d i)+3) L) L*cool R.family.path.levels (m+1)):=(le_div_iff₀ gp).mp cap
      _≤(2*J.C)*(tariff (F+4)*Real.log b^20*(Real.sqrt b)⁻¹) :=mul_le_mul_of_nonneg_left budget (by positivity)
      _=_:=by dsimp [K];ring
  exact sold N per (Nat.succ_le_of_lt live) (↥E) X Y
    (by simpa only [Fintype.card_coe] using counted per o T)
    (fun e=>⟨ready X hx e,ready Y hy e⟩)

end YM.Integration.WilsonLocalReportingExpense
