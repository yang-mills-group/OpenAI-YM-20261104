import YM.Integration.WilsonMeasuredRankedAdvance
import YM.Integration.WilsonOlderFreshGraphHostTarget

/-! One signed advance of the independently registered singleton on its own
physical course. The chosen upper and lower posts retain the original field,
support, regular and forced wallets. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredLandedAdvance
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
  (school : Syl.School k) (floor : m ≤ j)
  (actors : Unit → Set ℂ) {inputRank : ℕ}
  {passport : Earn.Passport (R.family.side ((j+1)+1) per) Unit}
  {entries : Type} (model : entries → Row passport (Stock.census Unit) G (Wallet actors))
local notation "pieces" => (fun _ : Unit => (⊥ : Submodule ℝ ℂ))
local notation "grades" => (fun _ : Unit => inputRank)
local notation "upper" => (floor.trans (Nat.le_succ j))
local notation "rp" => Ψ (j+1)
local notation "bare" => Ψ ((j+1)+1)
local notation "head" => fun (x:Wallet actors) (U:Config G (R.family.side ((j+1)+1) per)) =>
  ((bare).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut model (Coat.gStep (bare).beta) x U)
local notation "earlier" => (fun x:Wallet actors => LocalComparison.actualPush R.family N per (j+1) (head x))
local notation "upperPost" => Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q π Γ Ψ books ahead
  actors pieces grades school.order school.horizon school.pieces (j+1) upper (head)
local notation "lowerPost" => Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q π Γ Ψ books ahead
  actors pieces grades school.order school.horizon school.pieces j floor earlier
local notation "g" => Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta
local notation "gm" => Pert.Asymptotics.regulatorRun R.family N per m
local notation "y" => (passport.coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin ()
local notation "u" => (Stock.census Unit).fire ()
local notation "κ" => LocalComparison.forcedDivisor R.family (j+1)
variable (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (path:PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ) (cut:j+1<N)
    (pass:Pass D Q R.alloy R.kit) (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (narrow:school.horizon≤R.alloy.B.a.clock.J (j+1))
    (fieldRank:ℕ)
local notation "F₀" => R.family.labels.level fieldRank
local notation "S₀" => R.family.localSection fieldRank
local notation "Y₀" => R.family.params

include course path cut pass month narrow in
theorem original {τ c w:ℝ} {high:ℕ}
    (land:WilsonOlderFreshGraphHostTarget.Landed (d:=inputRank) (N:=N)
      R hk D Q π Γ Ψ books upper school ahead actors model τ c w high)
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
    (q : ℕ) (ready : q+1+6 ≤ R.alloy.B.a.clock.J (j+1)) (deep : 2*(q+4+1)+8 ≤ school.order)
    (aged : q+4+4 ≤ 3*k+2) {ε : ℝ} (ep : 0 < ε)
    (opened : WilsonFirstReceivedEarnedFee.opening R simple school.pieces (q+4) school.order k deep aged
      (tolerance_pos R fieldRank q (WilsonMeasuredRankedMenu.fee_positive R fieldRank M₀ ep)) ≤ j+1)
    (recalled : WilsonCoherentMayerMutationIntake.firstDate R simple school.order (show (0:ℝ)<1 by norm_num)
      le_rfl (tolerance_pos R fieldRank q (WilsonMeasuredRankedMenu.fee_positive R fieldRank M₀ ep)) ≤ j+1)
    (masks : WilsonOlderSignedOneMarkBooked.opening R simple (school.order+school.horizon+2) q 102
      (show 0 < WilsonMeasuredRankedMenu.fee R fieldRank M₀ ε/6 from div_pos (WilsonMeasuredRankedMenu.fee_positive R fieldRank M₀ ep) (by norm_num)) ≤ j+1)
    (soft : WilsonOlderSignedOneMarkCurrency.opening R simple q (WilsonMeasuredRankedMenu.fee_positive R fieldRank M₀ ep) ≤ j+1)
    (space:Sycamore.Boot.need high school≤R.alloy.B.a.clock.J ((j+1)+1))
    (lower:school.horizon≤R.alloy.B.a.clock.J j)
    (booked:WilsonReceivedMeasuredStampPrice.opening R simple q school.order k
      (by omega : 2*q+8 ≤ school.order) (by omega : q+3≤3*k+2) ep ≤ j+1)
    (test:Wallet actors) {next:ℝ} (pos:0<next) (small:next≤1) :
    ∃ (H:upperPost) (L:lowerPost),
      H.passport=passport ∧ H.modelIndex=entries ∧ HEq H.model model ∧
      H.w=(fun _=>w) ∧ H.cost=c ∧ H.rent=τ ∧
      (∀ (a:ℝ) (B:ℕ),H.input.old.Paid (fun _=>w) B a 0) ∧
      H.input.hard.Paid (fun _=>w) (bare).p.B (bare).p.supportExponent
        (LocalComparison.forcedDivisor R.family ((j+1)+1)*(R.alloy.B.a.clock.hatBeta ((j+1)+1))^(-(high:ℝ))) ∧
      Filed R hk D Q π Γ Ψ books ahead actors pieces grades
        school.order school.horizon school.pieces floor (head) H L ∧
      (∃ h C E:ℝ,1≤h ∧ C≤budgetR R (j+1) ∧ E≤τ+ε*g^q ∧
        (∀ v,L.w v=w/((Oak.expenseReal R hk D Q π Γ books upper H.op H.lesson
          ahead school.order school.horizon)^6*h)) ∧ L.cost=h⁻¹*C ∧ L.rent=max (h⁻¹*E) next) ∧
      ∀ x:Wallet actors,∃ (A:Coefficient F₀ (R.family.side (j+1) per)) (b:ℝ),
        A.Format y Y₀ rp ∧ A.remBound y rp κ b ∧
        (∀ U,A.density y S₀ rp U=(earlier x U).part u-
          ((rp).eval U:ℂ)*(Spill.Foundry.uncut L.model (Coat.gStep (rp).beta) x U).part u) ∧
        w*(b+(F₀).coeffSize A.x)≤ε*gm^q := by
  obtain ⟨H,hp,hw,hc,hr,hi,hm,regular,forced⟩:=land
  have load : school.pieces ≤ Burn.horizon k+2 := by
    obtain ⟨_,_,_,h,_,_⟩:=school
    exact h
  have fits : school.order ≤ Burn.horizon k+1 := by
    obtain ⟨_,_,_,_,h,_⟩:=school
    exact h
  have packed : school.order+school.horizon ≤ Burn.horizon k+2 := by
    obtain ⟨_,_,_,_,_,h⟩:=school
    exact h
  have activated : WilsonFirstReceivedEarnedFee.opening R simple H.op.count (q+4) school.order k deep aged
      (tolerance_pos R fieldRank q (WilsonMeasuredRankedMenu.fee_positive R fieldRank M₀ ep)) ≤ j+1 := by
    simpa [H.capacity] using opened
  obtain ⟨L,filing,earn,all⟩:=WilsonMeasuredRankedAdvance.original R hk D Q π Γ Ψ books ahead
    actors pieces grades school.order school.horizon school.pieces floor (head) H course path cut pass month
    fits narrow fieldRank M₀ office way simple slow prepared fixed date late grossDate fareDate scroll chamber
    hospital warm top load packed high space q ready deep aged ep activated recalled masks soft lower booked
    test pos small
  refine ⟨H,L,hp,hi,hm,hw,hc,hr,regular,forced,filing,?_,?_⟩
  · simpa only [hr,hw] using earn
  · intro x
    have same:=WilsonOlderFreshWordReversion.same H.model model hp hi hm
    simpa only [same,hp,hw] using all x ()

end YM.Integration.WilsonMeasuredLandedAdvance
