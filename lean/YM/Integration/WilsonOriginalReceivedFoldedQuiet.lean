import YM.Integration.WilsonOriginalReceivedPaidFolded

/-! The original, funded Wilson push against its own published cover row. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalReceivedFoldedPost
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open scoped Classical BigOperators Topology

section Measured
variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m ≤ i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) {V : Type} [Fintype V] [DecidableEq V]
  {X : V → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical)
  (x : Wallet actors) (A : Stationary.Link G (R.family.side i per))

local notation "gf" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "sheet" => R.family.path.levels.clock.op i per
local notation "angle" => Stationary.arm G (R.family.side i per) 1 A
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "width" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)
local notation "capital" => (fig).produce (sheet).ratio.count * P.cost
local notation "fee" => Ω^P.op.count * Earn.Earnings.hitPrice fig G
  (sheet).ratio.count (Ψ (i+1)).p (Ψ i).p (Ω⁻¹*P.cost) (Ω⁻¹*P.rent)
  (Burn.young (R.alloy.B.a.clock.hatBeta (i+1)) k) (Coat.gStep (Ψ (i+1)).beta)
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors P.model order P.voter
local notation "writer" => Air.craft student (fun a=>((student) a).paint x) grades (π i)
  (AllOrder.Floe.Step.tape (Burn.horizon k+2))
local notation "folded" => WilsonCoherentMayerWindingGrades.panel order (gf:ℂ)
  (fun d=>Air.discharge writer d angle)
local notation "placed" => P.passport.coarser (sheet).ratio

include course cut in
/-- The empty coefficient of the measured normalized source log and of its cover
polynomial vanishes, retaining the genuine Wilson vacuum in the normalization. -/
theorem quiet (simple : G.Simple)
    (opened : WilsonCoherentMayerRosterWindingRun.firstDate R simple ≤ i+1) (v : V)
    (clear : flags (Ψ i).p.threshold (Integral.sample gf angle)=∅) :
    let W := Integral.sample gf angle
    let read := Order.logTo (Fintype.card V) ((((Ψ i).eval W:ℂ)⁻¹) •
      LocalComparison.actualPush R.family N per i (physical x) W)
    (read-folded).part (Stock.census V).quiet=0 := by
  rw [←P.represented x]
  intro W read
  let F := Classical.choice (Tree.select (sheet).ratio (sheet).patch.odd_side)
  let tag : (sheet).Choices := Classical.choice inferInstance
  have small := P.affordable.trans (inv_le_one_of_one_le₀ P.issued.Waffle.cool)
  have field := (WilsonFirstReceivedOriginalNodalIncome.original R hk D Q π Γ Ψ course
    books hi cut P.op P.lesson ahead actors P.model P.w grades order shelf P.voter P.cost P.salary x F tag A
    pieces P.input P.rent P.output P.issued small simple opened P.issued.earning.positive W clear
    ((Stock.census V).fire v) v (Finset.mem_singleton_self v)).1
  have sums := P.issued.tuition.sums (by linarith only [(Ψ i).p.exponent_pos]) P.issued.earning.positive x W
  have residual := Lamps.quiet_of_hasSum x W sums
  have vacuum : (Integral.markedLog gf W writer).part (Stock.census V).quiet=0 := Multi.part_lit_quiet ..
  have realQuiet : read.part (Stock.census V).quiet=0 := calc
    _ = (Integral.markedLog gf W writer + P.output.old.log x W).part (Stock.census V).quiet :=
      congrArg (fun a : Poly (Stock.census V)=>a.part (Stock.census V).quiet) field
    _ = 0 := by rw [Poly.part_plus,vacuum,residual,add_zero]
  have priceQuiet : (folded).part (Stock.census V).quiet=0 := by
    unfold WilsonCoherentMayerWindingGrades.panel
    rw [Poly.part_sum]
    apply Finset.sum_eq_zero
    intro z _
    rw [Poly.part_smul,show (Air.discharge writer z angle).part (Stock.census V).quiet=0 from Multi.part_lit_quiet ..,mul_zero]
  change read.part (Stock.census V).quiet-(folded).part (Stock.census V).quiet=0
  rw [realQuiet,priceQuiet,sub_zero]

end Measured
end YM.Integration.WilsonOriginalReceivedFoldedPost
