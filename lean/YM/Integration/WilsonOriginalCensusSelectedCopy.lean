import YM.Integration.WilsonOriginalReceivedCopiedCover
import YM.Integration.WilsonOriginalRetainedStamp
import YM.Integration.WilsonOriginalCoverCoefficient

/-! On each true occupied mode the stamped upper pupil is the measured return of its own
copied finite Wilson contraction. The auxiliary forest and tag may be selected on each side. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalCensusSelectedCopy
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


local notation "tape" => AllOrder.Floe.Step.tape (Burn.horizon k+2)
local notation "cash" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter

open Comparison.RG02 QuadraticLocal.Rebirth FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame
variable (x:Affinity.Wallet actors)(grid:Side)(tiles:(R.family.side i per).val∣grid.val)
variable (trees:∀b:Covers R.family.path.levels.S i grid,Forest (R.family.path.levels.clock.op i b.val).ratio)(tags:∀b:Covers R.family.path.levels.S i grid,(R.family.path.levels.clock.op i b.val).Choices)
local notation "colors" => fun b:Covers R.family.path.levels.S i grid=>copyColor (tiled R tiles b) P.model grades
  (fun v=>(P.model v).paint x) (π (i+1)) tape
local notation "starts" => Oak.grade0 R hk D Q π Γ hi P.lesson
local notation "restamped" => Mutation.stamp student (Γ i) starts (Burn.horizon k+2) order

include course trees tags in
theorem entered (e:ℕ)(kept:e≤order)(Y:Stationary.Link G grid):
    WilsonOriginalCoverCoefficient.read R cut order grid (colors) trees tags e Y=peek tiles student grades (π (i+1)) tape x e Y:=by
  have issued:=WilsonOriginalReceivedCopiedCover.published R hk D Q π Γ Ψ course books hi cut ahead
    actors pieces grades order shelf seats physical P
  apply WilsonOriginalCoverCoefficient.identified
  exact WilsonOriginalCopiedContraction.named (R:=R) (h:=cut) (p:=order) (M:=P.model) (Y:=student)
    (published:=issued) (t:=x) (grid:=grid) (multiple:=tiles) (inputs:=(colors)) (matched:=fun _=>rfl) (F:=trees) (tag:=tags) (A:=Y) (e:=e) (he:=kept)

include course trees tags in
theorem original (pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (fits:order≤Burn.horizon k+1)(narrow:shelf≤R.alloy.B.a.clock.J i)
    (r:ℕ)(through:r≤order)(s:Multi.Hot (Stock.census V))(e:ℕ)(kept:e≤r)(Y:Stationary.Link G grid):
    (peek tiles restamped grades (π i) tape x e Y).part s.val=
    Adjacent.born (fun a z=>(WilsonOriginalCoverCoefficient.read R cut order grid (colors) trees tags a z).part s.val)
      ((Rebirth.caliber (Γ i) starts).back (Burn.horizon k+2)) 0 r e Y:=by
  apply WilsonOriginalRetainedStamp.original (R:=R) (hk:=hk) (course:=course) (cut:=cut)
    (pass:=pass) (month:=month) (fits:=fits) (narrow:=narrow) (issued:=P.issued.earning)
    (x:=x) (h:=tiles) (small:=through) (kept:=kept) (s:=s) (z:=Y)
  intro a included Z
  exact entered R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades order shelf seats
    physical P x grid tiles trees tags a (included.trans through) Z

end Measured
end YM.Integration.WilsonOriginalCensusSelectedCopy
end
