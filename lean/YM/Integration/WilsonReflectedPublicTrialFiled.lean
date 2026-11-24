import YM.Integration.WilsonReflectedPublicTrialExchange
import YM.Integration.WilsonOriginalAlternativeTrialHard
import YM.Integration.WilsonOriginalAlternativeTrialHomes

/-! The actually reached finite-origin guarded school. The former lamps and
all of their forced coefficients are the issued output of the same Post. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicTrialFiled
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open Work.G08 WilsonPositionProgramOriginalBlockedTrial WilsonAddressedRestartedColumn WilsonOriginalNullCorridor
open WilsonMeasuredCoefficientTransport
open WilsonMeasuredPublicEntranceCheapOrder WilsonMeasuredPublicEntranceCheapField
open scoped Classical BigOperators

open WilsonReflectedFundedHearing RG05Readout RG05Readout.Address
variable {G:Gauge}(R:Run G){m f b N per k:ℕ}(hk:Burn.horizon k+2≤R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
  (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀j,RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ→ℕ}(books:Mentor.Offices.Books D R.rolls Q φ)(mf:m≤f)(ahead:Mentor.Forecast D R.rolls Q φ books)
  {V:Type}[Fintype V][DecidableEq V](d:V→ℕ)(order shelf seats:ℕ)
  (A:(i:V)→Arm R (d i) N per f (b+1))(room:f≤b)(high:b+1≤N)(dose:V→ℂ)

local notation "actors" => WilsonOriginalAlternativeFiniteSource.disks (V:=V)
local notation "pieces" => WilsonOriginalAlternativeFiniteSource.sectors (V:=V)
local notation "J_" => Stock.census V
local notation "in_" => room.trans (Nat.le_succ b)
local notation "roots_" => WilsonReflectedPublicTrialRoster.root R d A in_
local notation "coords_" => WilsonReflectedPublicTrialRoster.weight R d A
local notation "dose_" => WilsonReflectedPublicTrialRoster.factor R (b+1) d dose
local notation "top_" => WilsonOriginalAlternativeTrialSource.source R d N per (b+1) roots_ coords_ dose_
local notation "returned_" => WilsonReceivedCloseHistory.history (N:=N) R actors top_ f room

variable (L:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead
  (WilsonOriginalAlternativeFiniteSource.disks (V:=V)) (WilsonOriginalAlternativeFiniteSource.sectors (V:=V))
  d order shelf seats f mf (WilsonReceivedCloseHistory.history (N:=N) R
    (WilsonOriginalAlternativeFiniteSource.disks (V:=V))
    (WilsonOriginalAlternativeTrialSource.source R d N per (b+1)
      (WilsonReflectedPublicTrialRoster.root R d A (room.trans (Nat.le_succ b)))
      (WilsonReflectedPublicTrialRoster.weight R d A)
      (WilsonReflectedPublicTrialRoster.factor R (b+1) d dose)) f room))
local notation "trueP" => R.family.path.rep N per f
local notation "W_" => Ψ f
local notation "homes" => (L.passport.coarser (R.family.path.levels.clock.op f per).ratio).origin
local notation "fire_" => WilsonOriginalAlternativeFiniteSource.fired (V:=V)
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books mf L.op L.lesson ahead actors L.model order L.voter
local notation "board" => Tint.Patrol.report student L.output (Coat.gStep (Ψ (f+1)).beta)
local notation "h_" => fun v=>WilsonMeasuredSingletonForce.row (n:=R.family.side f per) (F:=R.family.labels.level (d v)) L.output.hard fire_ v
local notation "κ_" => LocalComparison.forcedDivisor R.family f
local notation "coupling_" => R.alloy.B.a.clock.hatBeta (f+1)
local notation "report_" i:max => fun U=>((board).E.log fire_ U).part ((J_).fire i)

include course high in
theorem original (way:WayStation R.kit)(q:ℕ)(active:q+6*seats≤R.alloy.B.a.clock.J f)
    (located:∀v,homes v=(A v).o)
    (row:V→RG05Readout.Address.Three G (R.family.side f per))(wallet head savings:V→ℝ)
    (X E:(i:V) → Coefficient (R.family.labels.level (d i)) (R.family.side f per))
    (owned:∀v,WilsonReflectedPublicGuardedColumns.Joined R (A v) in_ high (dose v)
      (row v) (wallet v) (head v) (savings v) (X v) (E v)):
    (∀v,(h_ v).Format (A v).o R.family.params (W_) ∧
      (h_ v).remBound (A v).o (W_) κ_ ((L.w v)⁻¹*coupling_^(-(q:ℝ))) ∧
      (h_ v).x=0 ∧ (h_ v).regular=0 ∧ ∀a U,(h_ v).forced a U=(L.output.hard.hard fire_ a U).part ((J_).fire v)) ∧
    ∀vs:List V,∀U,
      let a:=fun v=>regular R d trueP (fun i=>(A i).o) X v U
      let b:=fun v=>(report_ v) U
      let e:=fun v=>regular R d trueP (fun i=>(A i).o) E v U
      let debt:=fun v=>account (X v) trueP U-account (h_ v) (W_) U-account (E v) trueP U
      ((trueP).eval U:ℂ)*((vs.map a).prod-(vs.map b).prod)=
        ((trueP).eval U:ℂ)*route a (fun v=>a v-e v) e vs-route b (fun v=>a v-e v) debt vs:=by
  have old:=fun v=>WilsonOriginalAlternativeTrialHard.original R hk D Q π Γ Ψ course books mf ahead
    d order shelf seats roots_ coords_ dose_ room high L way q active v
  refine ⟨fun v=>⟨(located v) ▸ (old v).1,(located v) ▸ (old v).2.1,(old v).2.2.1,(old v).2.2.2.1,(old v).2.2.2.2.1⟩,?_⟩
  have same:(W_).eval=(trueP).eval:=(course.1.walk f mf ((room.trans (Nat.le_succ b)).trans high)).view
  exact WilsonReflectedPublicTrialExchange.original R d A in_ high dose row wallet head savings X E h_ (W_)
    (fun v=>report_ v) same owned (fun v=>⟨(old v).2.2.1,(old v).2.2.2.1⟩)
    (fun v U=>by rw [←located v];exact ((old v).2.2.2.2.2 U).1)

end YM.Integration.WilsonReflectedPublicTrialFiled
end
