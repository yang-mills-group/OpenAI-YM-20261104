import YM.Integration.WilsonMeasuredRankedBooked

/-! Choose the receiving post on the same original signed course, then
issue the full priced singleton defect on that one post for every input
wallet and marked site. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredRankedAdvance
open Push.AbsoluteSums Next.Foundations
open Filter Labels Source Planned.GuardedAtom Push.Local
open WilsonOriginalReceivedChain
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Stationary Comparison.RG02 Comparison.RG02.Order Further.PhysicalPeriodLimitF933 Laurent
open RG16 Pert.Asymptotics WilsonMeasuredRankedResidual
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {m j N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (floor : m ≤ j)
  (physical : Wallet actors → Config G (R.family.side ((j+1)+1) per) → Poly (Stock.census V))

  (P : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1)
    (floor.trans (Nat.le_succ j)) physical)

local notation "earlier" => (fun x : Wallet actors => LocalComparison.actualPush R.family N per (j+1) (physical x))
local notation "elected" => Oak.expenseReal R hk D Q π Γ books (floor.trans (Nat.le_succ j)) P.op P.lesson ahead order shelf
local notation "g" => Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta

local notation "stud" => Oak.student (n:=per) R hk D Q π Γ books (floor.trans (Nat.le_succ j)) P.op P.lesson ahead actors P.model order P.voter
local notation "origin" => Oak.grade0 R hk D Q π Γ (floor.trans (Nat.le_succ j)) P.lesson
local notation "recorded" => Mutation.stamp stud (Γ (j+1)) origin (Burn.horizon k+2) order
local notation "inherited" => Mutation.grow stud (Γ (j+1)) origin (Burn.horizon k+2) order
  (Coat.gStep (Ψ ((j+1)+1)).beta) (Coat.gStep (Ψ (j+1)).beta) (Ψ (j+1)) P.output

variable (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (path:PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ) (cut:j+1<N)
    (pass:Pass D Q R.alloy R.kit) (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (fits:order≤Burn.horizon k+1) (narrow:shelf≤R.alloy.B.a.clock.J (j+1))
    (fieldRank:ℕ)
local notation "F₀" => R.family.labels.level fieldRank
local notation "S₀" => R.family.localSection fieldRank
local notation "Y₀" => R.family.params
local notation "rp" => Ψ (j+1)
local notation "κ" => LocalComparison.forcedDivisor R.family (j+1)
local notation "gm" => Pert.Asymptotics.regulatorRun R.family N per m
local notation "born" => fun (x:Wallet actors) (U:Config G (R.family.side ((j+1)+1) per)) =>
  ((Ψ ((j+1)+1)).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut P.model (Coat.gStep (Ψ ((j+1)+1)).beta) x U)
local notation "roots" => (P.passport.coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin
include course path cut pass month fits narrow in
theorem original
    (M₀:WilsonMeasuredRankedMenu.Menu R fieldRank) (office:M₀.onset≤j+1) (way : WayStation R.kit) (simple : G.Simple)
    (slow : ∀ n, ((R.family.S.block n).val:ℝ) ≤ Real.log (Lambda R.family.path.levels n))
    (prepared : WilsonReportLampForecast.Ready R.family.path.levels)
    (fixed : (R.family.path.levels.budget (j+1)).supportExponent ≤ 100)
    (date : R.t fieldRank ≤ j+1) (late : WilsonCenteredCaptureClock.first R simple ≤ j+1)
    (grossDate : WilsonReceivedSourceGross.opening R simple ≤ j+1)
    (fareDate : WilsonOlderSignedOneMarkPhysicalFare.opening R simple slow prepared ≤ j+1)
    (scroll : VowsR.LawScroll G φ) (chamber : VowsR.Chamber scroll R.kit D Q books)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (warm : Spill.Raffle.Warm G D R.alloy.delay φ)
    (top : Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
    (load : seats ≤ Burn.horizon k+2) (packed : order+shelf ≤ Burn.horizon k+2)
    (d : ℕ) (space : Sycamore.Boot.need d
      (⟨order,seats,shelf,load,fits,packed⟩ : Syl.School k) ≤ R.alloy.B.a.clock.J ((j+1)+1))
    (q : ℕ) (ready : q+1+6 ≤ R.alloy.B.a.clock.J (j+1)) (deep : 2*(q+4+1)+8 ≤ order)
    (aged : q+4+4 ≤ 3*k+2) {ε : ℝ} (ep : 0 < ε)
    (opened : WilsonFirstReceivedEarnedFee.opening R simple P.op.count (q+4) order k deep aged
      (tolerance_pos R fieldRank q (WilsonMeasuredRankedMenu.fee_positive R fieldRank M₀ ep)) ≤ j+1)
    (recalled : WilsonCoherentMayerMutationIntake.firstDate R simple order (show (0:ℝ)<1 by norm_num)
      le_rfl (tolerance_pos R fieldRank q (WilsonMeasuredRankedMenu.fee_positive R fieldRank M₀ ep)) ≤ j+1)
    (masks : WilsonOlderSignedOneMarkBooked.opening R simple (order+shelf+2) q 102
      (show 0 < WilsonMeasuredRankedMenu.fee R fieldRank M₀ ε/6 from div_pos (WilsonMeasuredRankedMenu.fee_positive R fieldRank M₀ ep) (by norm_num)) ≤ j+1)
    (soft : WilsonOlderSignedOneMarkCurrency.opening R simple q (WilsonMeasuredRankedMenu.fee_positive R fieldRank M₀ ep) ≤ j+1)
    (lower:shelf≤R.alloy.B.a.clock.J j)
    (booked:WilsonReceivedMeasuredStampPrice.opening R simple q order k (by omega : 2*q+8≤order)
      (by omega : q+3≤3*k+2) ep ≤ j+1)
    (test:Wallet actors) {τ:ℝ} (τp:0<τ) (τsmall:τ≤1) :
    ∃ L:Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats j floor earlier,
      Filed R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor physical P L ∧
      (∃ h C E:ℝ, 1≤h ∧ C≤budgetR R (j+1) ∧ E≤P.rent+ε*g^q ∧
        (∀ v,L.w v=P.w v/(elected^6*h)) ∧ L.cost=h⁻¹*C ∧ L.rent=max (h⁻¹*E) τ) ∧
      ∀ (x:Wallet actors) (v:V),
        let u:=(Stock.census V).fire v
        let y:=roots v
        ∃ (A:Coefficient F₀ (R.family.side (j+1) per)) (b:ℝ), A.Format y Y₀ rp ∧ A.remBound y rp κ b ∧
          (∀ U,A.density y S₀ rp U=(LocalComparison.actualPush R.family N per (j+1) (born x) U).part u-
            ((rp).eval U:ℂ)*(Spill.Foundry.uncut L.model (Coat.gStep (rp).beta) x U).part u) ∧
          P.w v*(b+(F₀).coeffSize A.x)≤ε*gm^q := by
  obtain ⟨h,C,E,_,one,ec,ee,issue⟩:=WilsonOriginalReceivedChain.next_filed R hk D Q π Γ Ψ books
    ahead actors pieces grades order shelf seats floor physical P course path cut pass scroll chamber month
    hospital fits lower load packed simple q (by omega) (by omega) ep booked test
  obtain ⟨L,_,weights,stocks,rent,_,_,file⟩:=issue τ τp τsmall
  refine ⟨L,file,⟨h,C,E,one,ec,ee,weights,stocks,rent⟩,?_⟩
  intro x v
  exact WilsonMeasuredRankedBooked.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
    floor physical P L file course cut pass month fits narrow x fieldRank M₀ office way simple slow prepared fixed
    date late grossDate fareDate scroll chamber hospital warm top load packed d space q ready deep aged ep opened
    recalled masks soft v

end YM.Integration.WilsonMeasuredRankedAdvance
