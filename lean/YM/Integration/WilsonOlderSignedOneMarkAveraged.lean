import YM.Integration.WilsonOlderSignedOneMarkCourse
import YM.Integration.WilsonOlderSignedOneMarkAdmitted
import YM.Integration.ActualNormalizedPush
import YM.Integration.WilsonOlderFreshWordReversion

/-! The filed older row in the genuine conditional Wilson scalar telescope. -/

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderSignedOneMarkAveraged
open MeasureTheory
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

private theorem heard {G : Gauge} {S : Type} [Fintype S] [DecidableEq S] {K : Census S}
    (C : Family G) (N per i : ℕ) (s : K.Mode) (f : Config G (C.side (i+1) per) → Poly K)
    (live : Integrable (fun U=>((C.path.rep N per (i+1)).eval U:ℂ) • f U) (prior G _))
    (W : Config G (C.side i per)) :
    actualAverage C (N:=N) (fun U=>(f U).part s) W=(((C.path.rep N per i).eval W:ℂ))⁻¹*
      (LocalComparison.actualPush C N per i (fun U=>((C.path.rep N per (i+1)).eval U:ℂ) • f U) W).part s := by
  let g:=fun U=>((C.path.rep N per (i+1)).eval U:ℂ) • f U
  let L:=(Poly.get s).restrictScalars ℝ
  have proj : (LocalComparison.actualPush C N per i g W).part s =
      (C.path.levels.clock.op i per).push (C.path.β N per (i+1)) (fun U=>L (g U)) W := by
    unfold LocalComparison.actualPush StepData.push
    have h:=L.integral_comp_comm (StepData.push_slice (C.path.levels.transition_mass i per (C.path.β N per (i+1))) W g live)
    simp_rw [L.map_smul] at h
    exact h.symm
  have coords : (fun U=>L (g U))=(fun U=>(C.path.rep N per (i+1)).eval U • (f U).part s) := by
    funext U
    change ((C.path.rep N per (i+1)).eval U:ℂ)*(f U).part s= _
    rw [Complex.real_smul]
  change _ = _ * (LocalComparison.actualPush C N per i g W).part s
  rw [actualAverage_push,proj,coords,Complex.real_smul,Complex.ofReal_inv]

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


include file course cut pass month fits in
theorem original
    (way : WayStation R.kit) (simple : G.Simple)
    (slow : ∀ n, ((R.family.S.block n).val:ℝ) ≤ Real.log (Lambda R.family.path.levels n))
    (prepared : WilsonReportLampForecast.Ready R.family.path.levels)
    (scroll : VowsR.LawScroll G φ) (chamber : VowsR.Chamber scroll R.kit D Q books)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (warm : Spill.Raffle.Warm G D R.alloy.delay φ)
    (top : Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
    (load : seats ≤ Burn.horizon k+2) (packed : order+shelf ≤ Burn.horizon k+2)
    (d q : ℕ) (deep : 2*(q+4+1)+8 ≤ order) (aged : q+4+4 ≤ 3*k+2)
    {ε : ℝ} (ep : 0 < ε) (v : V)
    (funded : WilsonOlderSignedOneMarkCalendar.Date R simple slow prepared
      (⟨order,seats,shelf,load,fits,packed⟩:Syl.School k) q d deep aged ep (j+1)) :
    let s:=(Stock.census V).fire v
    let y:=roots v
    ∃ (A : Coefficient F₀ (R.family.side (j+1) per)) (b : ℝ), A.Format y Y₀ rp ∧
      A.remBound y rp κ b ∧ (∀ U,
        actualAverage R.family (N:=N) (fun T=>(Spill.Foundry.uncut P.model gu x T).part s) U -
          (Spill.Foundry.uncut L.model gl x U).part s=((rp).eval U:ℂ)⁻¹*A.density y S₀ rp U) ∧
      Poly.toll P.w s*((F₀).coeffSize A.x+b) ≤ ε*gm^q := by
  obtain ⟨A,b,format,rem,represented,price⟩:=WilsonOlderSignedOneMarkCourse.original R hk D Q π Γ Ψ
    books ahead actors pieces grades order shelf seats floor physical P L file course cut pass month fits x
    way simple slow prepared scroll chamber hospital warm top load packed d q deep aged ep v funded
  refine ⟨A,b,format,rem,fun U=>?_,price⟩
  let s:=(Stock.census V).fire v
  let f:=fun T=>Poly.pass (Spill.Foundry.uncut P.model gu x T)
  have upper : (Ψ ((j+1)+1)).eval=(R.family.path.rep N per ((j+1)+1)).eval :=
    (course.1.walk ((j+1)+1) ((hi).trans (Nat.le_succ _)) cut).view
  have lower : (Ψ (j+1)).eval=(R.family.path.rep N per (j+1)).eval :=
    (course.1.walk (j+1) hi cut.le).view
  have paid:=WilsonOlderSignedOneMarkAdmitted.original R hk D Q π Γ Ψ course books ahead actors
    pieces grades order shelf seats hi physical P cut scroll chamber warm top fits load packed d funded.space x
  have live : Integrable (fun T=>((R.family.path.rep N per ((j+1)+1)).eval T:ℂ) • f T) (prior G _) := by
    simpa only [←upper] using paid
  have avg:=heard R.family N per (j+1) s f live U
  rw [←upper,←lower] at avg
  have pos : ((rp).eval U:ℂ) ≠ 0 := by
    rw [lower]
    exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson cut.le U).ne'
  have source : (fun T=>(f T).part s)=(fun T=>(Spill.Foundry.uncut P.model gu x T).part s) := by
    funext T
    exact MergeProof.Accent.whisper _ _ (WilsonOlderFreshWordReversion.quiet P.model x gu T) v
  rw [source] at avg
  rw [avg,represented U,mul_sub,←mul_assoc,inv_mul_cancel₀ pos,one_mul]

end YM.Integration.WilsonOlderSignedOneMarkAveraged
