import YM.Integration.WilsonOlderFreshFiledStep

/-! A full freshly planted adjacent Wilson push, using both actual deployed group fields of one independently filed history. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshPaidEdge
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

include file course cut pass month fits narrow in
theorem original (way : WayStation R.kit) (simple : G.Simple)
    (late : WilsonCenteredCaptureClock.first R simple ≤ j+1) (p q : ℕ) (ready : q≤R.alloy.B.a.clock.J (j+1))
    (deep : 2*(p+1)+8≤order) (aged : p+4≤3*k+2) {ε η : ℝ} (ep : 0<ε) (positive : 0<η) (unit : η≤1)
    (opened : WilsonFirstReceivedEarnedFee.opening R simple P.op.count p order k deep aged ep≤j+1)
    (recalled : WilsonCoherentMayerMutationIntake.firstDate R simple order positive unit ep≤j+1)
    (scroll : VowsR.LawScroll G φ) (chamber : VowsR.Chamber scroll R.kit D Q books)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (warm : Spill.Raffle.Warm G D R.alloy.delay φ)
    (top : Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
    (load : seats≤Burn.horizon k+2) (packed : order+shelf≤Burn.horizon k+2)
    (freshDepth : ℕ) (space : Sycamore.Boot.need freshDepth (⟨order,seats,shelf,load,fits,packed⟩ : Syl.School k)
      ≤R.alloy.B.a.clock.J ((j+1)+1))
    (v : V) (Z : Support (R.family.side (j+1) per)) (y : Site (R.family.side (j+1) per))
    (center : y∈Z) (member : roots v∈Z) (rad : ℕ) (near : separation (roots v) y≤rad)
    {d : ℕ} {F : Frame G d} (S : SectionData F) (Y : Hol G) {μ : ℝ}
    (reader : Readable Y S (rp).p (R.family.side (j+1) per) μ) :
    let τ:=min 1 ((ε*g^p)/(8*elected^P.op.count))
    let s:=(Stock.census V).fire v
    let unmasked:=WilsonOlderSignedSingletonFare.fare (rp).p S Y weights s 1 Z rad
      ((elected^6)⁻¹*((8*elected^P.op.count)*τ+ε*g^p)) (βh^(-(q:ℝ))*κ) κ allowance μ
    let outputMask:=WilsonOlderSignedOneMarkMasks.fare (rp).p Z allowance (Poly.toll P.w s) (allFee*elected) κ
    let recon:=ε*g^((order:ℝ)+1-η)*P.cost
    let balance:=WilsonOlderFreshReversionStore.price (rp).p S Y Z rad μ allowance κ (Poly.toll P.w s) recon (allFee*recon)
    (8*elected^P.op.count)*τ≤ε*g^p ∧
    WilsonCenteredFiledAtoms.Store rp S Y y κ ((unmasked+outputMask)+balance)
      (fun U=>(pushFace U).part s-((rp).eval U:ℂ)*(Spill.Foundry.uncut L.model gl x U).part s) := by
  intro τ s unmasked outputMask recon balance
  obtain ⟨tuned,A,fmt,due,row⟩:=WilsonOlderFreshPlant.original R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades
    order shelf seats physical P way simple late p q ready deep aged ep opened scroll chamber hospital
    warm top fits load packed freshDepth space x v Z y center member rad near S Y reader
  have first : WilsonCenteredFiledAtoms.Store rp S Y y κ (unmasked+outputMask)
      (fun U=>(pushFace U).part s-((rp).eval U:ℂ)*(Integral.markedLog g U upperBank).part s) :=
    ⟨A,fmt,due,row⟩
  have second:=WilsonOlderFreshFiledStep.balance R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
    floor physical P L file course cut pass month fits narrow x hospital load simple positive unit ep recalled
    late v Z y center member rad near S Y reader
  have actual:=(course.1.walk (j+1) hi cut.le).truep
  obtain ⟨div,_,_⟩:=(eventually_atTop.mp (WilsonCenteredCaptureClock.original R simple)).choose_spec (j+1) late
  obtain ⟨B,fit,price,field⟩:=WilsonCenteredFiledAtoms.add actual.valid div first second
  refine ⟨tuned,B,fit,price,fun U=>(field U).trans ?_⟩
  change ((pushFace U).part s-((rp).eval U:ℂ)*(Integral.markedLog g U upperBank).part s)+
    ((rp).eval U:ℂ)*((Integral.markedLog g U upperBank).part s-(Spill.Foundry.uncut L.model gl x U).part s)=_
  ring

end YM.Integration.WilsonOlderFreshPaidEdge
