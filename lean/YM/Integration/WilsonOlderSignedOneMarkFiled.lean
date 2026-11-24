import YM.Integration.WilsonOlderSignedOneMarkPaid
import YM.Integration.WilsonOlderSignedOneMarkJoinedFare
import YM.Integration.WilsonOlderFreshPaidUnit
import YM.Integration.WilsonOlderFreshRestampHard

/-! A complete signed one-source edge between the two actual files of an
older Wilson course, including the change of the measured kinetic coordinate
and both original mask fees. -/

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderSignedOneMarkFiled
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
local notation "F₀" => R.family.labels.level 0
local notation "S₀" => R.family.localSection 0
local notation "base" => 2*Real.exp 102*(1+2*charge Y₀ S₀)
local notation "sectionCost" => testPrice F₀
local notation "μ₀" => (R.family.path.levels.params (j+1)).columns

def tolerance {G : Gauge} (R : Run G) (q : ℕ) (ε : ℝ) := min 1 (intake R q ε/3)

theorem tolerance_pos {G:Gauge} (R:Run G) (q:ℕ) {ε:ℝ} (ep : 0 < ε) : 0 < tolerance R q ε :=
  lt_min one_pos (div_pos (intake_pos R q ep) (by norm_num))

private theorem tolerance_bill {G:Gauge} (R:Run G) (q:ℕ) {ε:ℝ} :
    expense R*(3*tolerance R q ε)*(2:ℝ)^q ≤ ε/3 := by
  have cap : 3*tolerance R q ε ≤ intake R q ε := by
    linarith only [show tolerance R q ε ≤ intake R q ε/3 from min_le_right _ _]
  calc
    _ ≤ expense R*intake R q ε*(2:ℝ)^q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left cap (positive R).le) (by positivity)
    _ = _ := by unfold intake;field_simp [(positive R).ne']

include file course cut pass month fits narrow in
theorem original
    (way : WayStation R.kit) (simple : G.Simple)
    (slow : ∀ n, ((R.family.S.block n).val:ℝ) ≤ Real.log (Lambda R.family.path.levels n))
    (prepared : WilsonReportLampForecast.Ready R.family.path.levels)
    (fixed : (R.family.path.levels.budget (j+1)).supportExponent ≤ 100)
    (date : R.t 0 ≤ j+1) (late : WilsonCenteredCaptureClock.first R simple ≤ j+1)
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
      (tolerance_pos R q ep) ≤ j+1)
    (recalled : WilsonCoherentMayerMutationIntake.firstDate R simple order (show (0:ℝ)<1 by norm_num)
      le_rfl (tolerance_pos R q ep) ≤ j+1)
    (masks : WilsonOlderSignedOneMarkBooked.opening R simple (order+shelf+2) q 102
      (show 0 < ε/6 by positivity) ≤ j+1)
    (soft : WilsonOlderSignedOneMarkCurrency.opening R simple q ep ≤ j+1) (v : V) :
    let s:=(Stock.census V).fire v
    let y:=roots v
    ∃ (A : Coefficient F₀ (R.family.side (j+1) per)) (b : ℝ), A.Format y Y₀ rp ∧
      A.remBound y rp κ b ∧ (∀ U, A.density y S₀ rp U=(pushFace U).part s-
        ((rp).eval U:ℂ)*(Spill.Foundry.uncut L.model gl x U).part s) ∧
      Poly.toll P.w s*((F₀).coeffSize A.x+b) ≤ ε*gm^q := by
  intro s y
  let Z : Support (R.family.side (j+1) per) := {y}
  let δ:=tolerance R q ε
  let e:=δ*g^(q+4)
  let τ:=min 1 (e/(8*elected^P.op.count))
  let recon:=δ*g^((order:ℝ)+1-1)*P.cost
  let E:=(8*elected^P.op.count)*τ+e
  let tab:=Poly.toll P.w s
  let regular (f:ℝ):= WilsonOlderSignedSingletonFare.fare (rp).p S₀ Y₀ weights s 1 Z 0
    ((elected^6)⁻¹*f) (βh^(-((q+1+6:ℕ):ℝ))*κ) κ allowance μ₀
  let mark (f:ℝ):=WilsonOlderSignedOneMarkMasks.fare (rp).p Z allowance tab f κ
  let er:=WilsonOlderFreshReversionStore.price (rp).p S₀ Y₀ Z 0 μ₀ allowance κ tab recon (allFee*recon)
  have budget:=(course.1.walk (j+1) hi cut.le).truep.point
  have reader:=(WilsonCapturedPrimarySection.original R date rp budget).1
  have here:y∈Z:=Finset.mem_singleton_self _
  have near: separation y y ≤ 0 := (YM.Lattice.separation_self y).le
  have dp : 0 < δ:=tolerance_pos R q ep
  obtain ⟨tuned,A,shape,bound,field,primary⟩:=WilsonOlderFreshPaidUnit.original R hk D Q π Γ Ψ books
    ahead actors pieces grades order shelf seats floor physical P L file course cut pass month fits narrow x
    way simple late (q+4) (q+1+6) ready deep aged dp (show (0:ℝ) < 1 by norm_num) le_rfl
    opened recalled scroll chamber hospital warm top load packed d space v Z y here here 0 near S₀ Y₀ reader
  obtain ⟨gp,mp,relative,small⟩:=WilsonOlderSignedOneMarkCurrency.measured R simple hi cut q ep soft
  have gp' : 0 < g := gp
  have cool : g ≤ 1:=small.trans (min_le_left _ _)
  have stock:=Push.AbsoluteSums.budget_nonneg (P.salary.suggests 0)
  have affordable : P.cost ≤ 1 := P.affordable.trans (inv_le_one_of_one_le₀ P.issued.Waffle.cool)
  have price : recon ≤ e:= by
    dsimp only [recon,e]
    rw [add_sub_cancel_right,Real.rpow_natCast]
    calc
      _ ≤ δ*g^order*1 := mul_le_mul_of_nonneg_left affordable (mul_nonneg dp.le (pow_nonneg gp'.le _))
      _ ≤ _ := by rw [mul_one];exact mul_le_mul_of_nonneg_left
                    (pow_le_pow_of_le_one gp'.le cool (show q+4≤order by omega)) dp.le
  have en : 0 ≤ e:=mul_nonneg dp.le (pow_nonneg gp'.le _)
  have rn : 0 ≤ recon:=mul_nonneg (mul_nonneg dp.le (Real.rpow_nonneg gp'.le _)) stock
  have incomePos : 0 < 8*elected^P.op.count:=mul_pos (by norm_num) (pow_pos P.issued.Waffle.paysAbove _)
  have τn : 0 ≤ τ:=le_min zero_le_one (div_nonneg en incomePos.le)
  have upper : E+recon ≤ 3*e:=by dsimp only [E];linarith only [tuned,price]
  have whole : 0 ≤ E+recon:=add_nonneg (add_nonneg (mul_nonneg incomePos.le τn) en) rn
  have regularPrice : tab*regular (E+recon) ≤ base*(g⁻¹)^4*(E+recon)+2*Real.exp 102*(2*g^2)^(q+1) :=
    WilsonOlderSignedOneMarkPhysicalFare.original R hk D Q π Γ Ψ course books hi cut ahead actors pieces
      grades order shelf seats physical P simple slow prepared fixed grossDate fareDate pass hospital narrow
      (P.capacity.trans_le load) v (E+recon) whole (q+1)
  have allowancePos:=Push.Local.allowance_pos R.alloy.B.a.clock (j+1)
  have zcost : (rp).p.supportExponent ≤ 100:=by rw [budget];exact fixed
  have masksPrice := WilsonOlderFreshRestampHard.weighted R hk D Q π Γ Ψ course books hi cut ahead
    actors pieces grades order shelf seats physical P simple grossDate pass hospital narrow
    (P.capacity.trans_le load) s Z q 102 (root (rp).p zcost y) (show 0 < ε/6 by positivity)
    masks (show (1:ℝ) ≤ 1 from le_rfl) dp.le (min_le_left _ _) cool allowancePos.le (Real.sqrt_nonneg _)
  have joined : tab*((regular E+mark (allFee*elected))+er)=tab*regular (E+recon)+
      tab*(mark (allFee*elected)+mark (allFee*recon)) :=
    WilsonOlderSignedOneMarkJoinedFare.original (rp).p S₀ Y₀ P.w v Z (P.issued.earning.positive v)
      (pow_pos P.issued.Waffle.paysAbove _)
  have hn:0 ≤ sectionCost := zero_le_one.trans (probe_budget F₀).choose_spec.choose_spec.1
  have bn:0 ≤ base := by unfold charge;positivity
  have scalar : tab*(F₀).coeffSize A.x ≤ sectionCost*(3*e) :=
    primary.trans (mul_le_mul_of_nonneg_left (by linarith only [price] : 2*e+recon ≤ 3*e) hn)
  have remainder : tab*((regular E+mark (allFee*elected))+er) ≤
      base*(g⁻¹)^4*(3*e)+2*Real.exp 102*(2*g^2)^(q+1)+2*(ε/6)*gm^q := by
    rw [joined]
    exact add_le_add (regularPrice.trans (add_le_add
      (mul_le_mul_of_nonneg_left upper (mul_nonneg bn (pow_nonneg (inv_nonneg.mpr gp'.le) _))) le_rfl)) masksPrice
  refine ⟨A,_,shape,bound,field,?_⟩
  have all := WilsonOlderSignedOneMarkCurrency.paid q gp' mp (show 0≤3*δ by positivity)
    (show (0:ℝ)≤0 from le_rfl) hn bn relative small (tolerance_bill R q)
  calc
    _ = tab*(F₀).coeffSize A.x+tab*((regular E+mark (allFee*elected))+er):= mul_add .. 
    _ ≤ _ := add_le_add scalar remainder
    _ = (sectionCost+base*(g⁻¹)^4)*(0+(3*δ)*g^(q+4))+2*Real.exp 102*(2*g^2)^(q+1)+(ε/3)*gm^q := by
      dsimp only [e];ring
    _ ≤ _ := all.trans_eq (by ring)

end YM.Integration.WilsonOlderSignedOneMarkFiled
