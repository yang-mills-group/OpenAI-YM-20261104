import YM.Integration.WilsonMeasuredRankedPrimaryBudget

/-! A funded true one-step conditional source error on the measured Wilson
course, simultaneously in its stored primary, regular and genuine hard norms. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredRankedStore
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
open WilsonMeasuredRankedResidual
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

variable (L : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats j floor
  (fun x : Wallet actors => LocalComparison.actualPush R.family N per (j+1) (physical x)))
  (file : Filed R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor physical P L)
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ) (cut : j+1 < N)
  (pass : Pass D Q R.alloy R.kit) (month : Scholar.Month R.rolls D Q R.alloy.delay)
  (fits : order ≤ Burn.horizon k+1) (narrow : shelf ≤ R.alloy.B.a.clock.J (j+1)) (x : Wallet actors)

local notation "hi" => (floor.trans (Nat.le_succ j))
local notation "depth" => (Burn.horizon k+2)
local notation "tape₀" => AllOrder.Floe.Step.tape depth
local notation "bankNow" => Air.craft L.model (fun v=>(L.model v).paint x) grades (π (j+1)) tape₀
local notation "priorBank" => Air.craft P.model (fun v=>(P.model v).paint x) grades (π ((j+1)+1)) tape₀
local notation "upperBank" => Air.craft stud (fun v=>((stud) v).paint x) grades (π (j+1)) tape₀
local notation "stampedBank" => Air.craft recorded (fun v=>((recorded) v).paint x) grades (π (j+1)) tape₀
local notation "gu" => Coat.gStep (Ψ ((j+1)+1)).beta
local notation "gl" => Coat.gStep (Ψ (j+1)).beta
local notation "older" => R.family.path.rep N per (j+1)
local notation "reverted" => Mutation.mend stud (Ψ (j+1)).p (Γ (j+1)) origin depth order gu gl
local notation "α" => (Ψ (j+1)).p.supportExponent+1+1

local notation "βh" => R.alloy.B.a.clock.hatBeta ((j+1)+1)
local notation "rp" => Ψ (j+1)
local notation "allowance" => R.alloy.B.a.clock.forcedAllowance (j+1)
local notation "κ" => LocalComparison.forcedDivisor R.family (j+1)
local notation "roots" => (P.passport.coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "allFee" => (Spill.allOver (rp).p)^(order+shelf+1)

local notation "born" => (fun (x : Wallet actors) (U : Config G (R.family.side ((j+1)+1) per)) =>
  ((Ψ ((j+1)+1)).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut P.model gu x U))
local notation "weights" => Stoop.radius P.w (elected^6)
local notation "pushFace" => LocalComparison.actualPush R.family N per (j+1) (born x)


open Pert.Asymptotics RG16 WilsonOlderSignedOneMarkPaid WilsonOlderSignedOneMarkTariff
open WilsonCenteredFiledAtoms
local notation "gm" => regulatorRun R.family N per m
local notation "Y₀" => R.family.params
variable (fieldRank : ℕ)
local notation "F₀" => R.family.labels.level fieldRank
local notation "S₀" => R.family.localSection fieldRank
local notation "base" => 2*Real.exp 102*(1+2*charge Y₀ S₀)
local notation "μ₀" => (R.family.path.levels.params (j+1)).columns

local notation "fixedP" => R.alloy.B.a.budget (j+1)
local notation "width" => Next.Foundations.price G (max (fixedP).order (fixedP).power)
local notation "wx" => WilsonMeasuredRankedPrimaryBudget.wrap F₀ Y₀

include file course cut pass month fits narrow in
theorem original
    (way : WayStation R.kit) (simple : G.Simple)
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
      (tolerance_pos R fieldRank q ep) ≤ j+1)
    (recalled : WilsonCoherentMayerMutationIntake.firstDate R simple order (show (0:ℝ)<1 by norm_num)
      le_rfl (tolerance_pos R fieldRank q ep) ≤ j+1)
    (masks : WilsonOlderSignedOneMarkBooked.opening R simple (order+shelf+2) q 102
      (show 0 < ε/6 by positivity) ≤ j+1)
    (soft : WilsonOlderSignedOneMarkCurrency.opening R simple q ep ≤ j+1) (v : V) {K:ℝ} (kp:0≤K)
    (h₁:WilsonMeasuredPrimaryTariff.allowance fixedP Y₀ S₀ (roots v) width≤K*R.alloy.B.a.clock.hatBeta (j+1))
    (h₂:WilsonMeasuredPrimaryTariff.cost fixedP Y₀ S₀ (roots v) width≤K*R.alloy.B.a.clock.hatBeta (j+1)) :
    let s:=(Stock.census V).fire v
    let y:=roots v
    let tariff:=(1+wx)*(6*K*(2:ℝ)^q)*tolerance R fieldRank q ε+wx*ε
    ∃ (A:Coefficient F₀ (R.family.side (j+1) per)) (b:ℝ), A.Format y Y₀ rp ∧ A.remBound y rp κ b ∧
      (∀ U,A.density y S₀ rp U=(pushFace U).part s-((rp).eval U:ℂ)*(Spill.Foundry.uncut L.model gl x U).part s) ∧
      P.w v*b≤ε*gm^q ∧ P.w v*(F₀).coeffSize A.x≤tariff*gm^q := by
  intro s y tariff
  letI : Nonempty V:=⟨v⟩
  obtain ⟨A,b,shape,paid,stored,tab⟩:=WilsonMeasuredRankedResidual.original R hk D Q π Γ Ψ books ahead
    actors pieces grades order shelf seats floor physical P L file course cut pass month fits narrow x fieldRank way
    simple slow prepared fixed date late grossDate fareDate scroll chamber hospital warm top load packed d space
    q ready deep aged ep opened recalled masks soft v
  have tab₀:P.w v*b≤ε*gm^q:=by simpa only [Poly.solo_toll] using tab
  refine ⟨A,b,shape,paid,stored,tab₀,?_⟩
  let δ:=tolerance R fieldRank q ε
  let e:=δ*g^(q+4)
  let τ:=min 1 (e/(8*elected^P.op.count))
  let E:=(8*elected^P.op.count)*τ+e
  let Δ:=δ*g^((order:ℝ)+1-1)*P.cost
  let z:=R.alloy.B.a.clock.hatBeta (j+1)
  have dp:0<δ:=tolerance_pos R fieldRank q ep
  have eo:0<elected:=P.issued.Waffle.paysAbove
  obtain ⟨gp,mp,rel,small⟩:=WilsonOlderSignedOneMarkCurrency.measured R simple hi cut q ep soft
  have gf:0<g:=gp
  have mf:0<gm:=mp
  have rel₀:g≤2*gm:=rel
  have cool:g≤1:=small.trans (min_le_left _ _)
  have epos:0<e:=mul_pos dp (pow_pos gf _)
  have wage:0<8*elected^P.op.count:=mul_pos (by norm_num) (pow_pos eo _)
  have th:0<τ:=lt_min zero_lt_one (div_pos epos wage)
  have bill:=WilsonMeasuredRankedFiledPrimary.original R hk D Q π Γ Ψ books ahead actors pieces grades order
    shelf seats floor physical P L file course cut pass month fits narrow x simple (q+4) d fieldRank dp
    (show (0:ℝ)<1 by norm_num) le_rfl th (min_le_left _ _) deep aged opened recalled scroll chamber hospital
    warm top load packed space date v A shape paid stored
  have native:=(course.1.walk (j+1) hi cut.le).truep.point
  have bn:0≤b:=by obtain ⟨a₁,a₂,h₁,h₂,amt,-⟩:=paid;linarith only [h₁,h₂,amt]
  have stock:0≤P.cost:=Push.AbsoluteSums.budget_nonneg (P.salary.suggests 0)
  have afford:P.cost≤1:=P.affordable.trans (inv_le_one_of_one_le₀ P.issued.Waffle.cool)
  have all:E+Δ≤3*e:=by
    have tapped:(8*elected^P.op.count)*τ≤e:=
      (mul_comm _ _).trans_le ((le_div_iff₀ wage).mp (min_le_right _ _))
    have agedSeries:g^order≤g^(q+4):=pow_le_pow_of_le_one gf.le cool (by omega)
    have other:Δ≤e:=by
      dsimp only [Δ,e];rw [add_sub_cancel_right,Real.rpow_natCast]
      calc
        _ ≤ δ*g^order*1:=mul_le_mul_of_nonneg_left afford (mul_nonneg dp.le (pow_nonneg gf.le _))
        _ ≤ _:=by rw [mul_one];exact mul_le_mul_of_nonneg_left agedSeries dp.le
    dsimp only [E];linarith only [tapped,other]
  have realCost:0≤E+Δ:=by dsimp [E,Δ];positivity
  have zp:0<z:=zero_lt_one.trans (R.alloy.B.a.fits.delayed (j+1))
  have c₀:0≤WilsonMeasuredRankedGerm.wrapCost F₀ Y₀:=WilsonMeasuredRankedGerm.wrapCost_nonneg ..
  have w₀:0≤wx:=mul_nonneg c₀ (Real.exp_pos _).le
  have booked:=WilsonMeasuredRankedPrimaryBudget.scalar (rp).p Y₀ S₀ y
    (Next.Foundations.price G (max (rp).p.order (rp).p.power)) (θ:=P.w v) (E:=E+Δ) (b:=b)
    (net:=(F₀).coeffSize A.x) (f:=K*z) (P.issued.earning.positive v) realCost bn
    (by rw [native];exact fixed) (by simpa only [native] using h₁) (by simpa only [native] using h₂)
    (mul_nonneg kp zp.le) bill
  have cover:z*g^2≤2:=(WilsonMeasuredRankedPrimaryBudget.native R simple cut per).2
  have gsq:g^2≤1:=pow_le_one₀ gf.le cool
  have head:K*z*(E+Δ)≤6*K*(2:ℝ)^q*δ*gm^q:=calc
    _ ≤ K*z*(3*e):=mul_le_mul_of_nonneg_left all (mul_nonneg kp zp.le)
    _ = (z*g^2)*(g^2)*(3*K*δ)*g^q:=by dsimp only [e];rw [pow_add];ring
    _ ≤ 2*1*(3*K*δ)*(2*gm)^q:=by gcongr
    _ = _:=by rw [mul_pow];ring
  calc
    _ ≤ (1+wx)*(K*z)*(E+Δ)+wx*(P.w v*b):=booked
    _ ≤ (1+wx)*(6*K*(2:ℝ)^q*δ*gm^q)+wx*(ε*gm^q):=by
      rw [mul_assoc (1+wx)]
      gcongr
    _ = _:=by dsimp only [tariff,δ];ring

end YM.Integration.WilsonMeasuredRankedStore
