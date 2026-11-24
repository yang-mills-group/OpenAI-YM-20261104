import YM.Integration.WilsonOriginalReceivedCopiedCover
import YM.Integration.WilsonOriginalCoverCoefficient
import YM.Integration.WilsonOriginalCopiedHistory
import YM.Integration.WilsonThermometerPositionFilmBank
/-! The same actually issued pupil is read on the chronological forest and predictor on every auxiliary copy. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFilmForest
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open FVA1Physical.TwoReset QuadraticLocal.Sunrise RegulatorIR.FVAAlt2
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


variable (x:Wallet actors) (grid:Side) (mult:(R.family.side i per).val∣grid.val)
local notation "input" b:max=> copyColor (tiled R mult b) P.model grades (fun h=>(P.model h).paint x) (π (i+1)) tape
local notation "op₀" b:max=> R.family.path.levels.clock.op i (b).val
local notation "page" => Covers R.family.path.levels.S i grid

include course in
theorem filed (F:(b:page)→Forest (op₀ b).ratio) (tag:(b:page)→(op₀ b).Choices)
    (a:Stationary.Link G grid) (e:ℕ) (held:e≤order) :
    WilsonOriginalCoverCoefficient.read R cut order grid (fun b=>input b) F tag e a=
      peek mult student grades (π (i+1)) tape x e a := by
  have paid:=WilsonOriginalReceivedCopiedCover.published R hk D Q π Γ Ψ course books hi cut ahead actors pieces
    grades order shelf seats physical P
  apply WilsonOriginalCoverCoefficient.identified
  exact WilsonOriginalCopiedContraction.named (R:=R) (h:=cut) (p:=order) (M:=P.model)
    (Y:=student) (published:=paid) (t:=x) (grid:=grid) (multiple:=mult)
    (inputs:=fun b=>input b) (matched:=fun _=>rfl) (F:=F) (tag:=tag) (A:=a) (e:=e) (he:=held)

include course in
theorem original (a:Stationary.Link G grid) (e:ℕ) (held:e≤order) :
    WilsonOriginalCopiedHistory.block R cut order
        (fun _ m=>copyColor m P.model grades (fun h=>(P.model h).paint x) (π (i+1)) tape)
        grid mult e a=
      WilsonOriginalCoverCoefficient.read R cut order grid (fun b=>input b)
        (fun b=>RegulatorIR.Halo.bios (op₀ b)) (fun b=>RegulatorIR.Geometry.directive (op₀ b)) e a := by
  exact (filed R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades order shelf seats physical P
    x grid mult (WilsonOriginalCopiedHistory.forest R i grid) (WilsonOriginalCopiedHistory.tag R i grid) a e held).trans
    (filed R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades order shelf seats physical P
      x grid mult _ _ a e held).symm

end Measured
end YM.Integration.WilsonThermometerPositionFilmForest
