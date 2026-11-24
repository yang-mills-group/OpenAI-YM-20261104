import YM.Integration.WilsonOlderFreshPaidEdge
import YM.Integration.WilsonOlderFreshScalar

/-! The entire horizon-zero coordinate of the two-date signed return, including marked constants. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshPaidUnit
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

include file course cut pass month fits narrow in
theorem flatChange (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (load : seats≤Burn.horizon k+2) (simple : G.Simple) {η ε : ℝ} (positive : 0<η) (unit : η≤1) (ep : 0<ε)
    (recalled : WilsonCoherentMayerMutationIntake.firstDate R simple order positive unit ep≤j+1) (v : V) :
    let s := (Stock.census V).fire v
    let U : Config G (R.family.side (j+1) per) := 1
    Poly.toll P.w s*‖(Integral.markedLog g U upperBank).part s-(Spill.Foundry.uncut L.model gl x U).part s‖ ≤
      ε*g^((order:ℝ)+1-η)*P.cost := by
  intro s U
  have debt:=WilsonOlderFreshFiledWord.masked R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
    floor physical P course cut pass month fits narrow hospital load simple positive unit ep recalled
  have width : 0≤α := by linarith [(rp).p.exponent_pos]
  have healthy:=WilsonFirstReceivedGalleryRegular.occupied reverted debt.1 width P.issued.earning.positive x U s v
    (mem_singleton_self _)
  have whole : ((reverted).log x U)=WilsonRootedKioskOccupiedSlip.bare reverted x U := by
    unfold Lamps.log WilsonRootedKioskOccupiedSlip.bare
    apply tsum_congr
    intro z
    change Poly.send _ ((reverted).light x z U)=Poly.send _ ((reverted).nominal x z U)
    congr 1
    unfold Lamps.light
    split
    · rfl
    exact masked_eq _ _ _ _ (one_healthy _ _ (rp).p.threshold_pos.le)
  have f:=WilsonOlderFreshFiledWord.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
    floor physical P L file course cut x U
  have equal : WilsonRootedKioskOccupiedSlip.bare reverted x U =
      Integral.markedLog g U upperBank-Integral.markedLog (Coat.gStep (older).beta) U bankNow := f.2.2.2.tsum_eq
  have tested : ((reverted).log x U).part s =
      (Integral.markedLog g U upperBank).part s-(Spill.Foundry.uncut L.model gl x U).part s :=
    (congrArg (fun z : Poly (Stock.census V)=>z.part s) (whole.trans equal)).trans
      (congrArg (fun z : Poly (Stock.census V)=>(Integral.markedLog g U upperBank).part s-z.part s) f.2.1.symm)
  exact (congrArg (fun z : ℂ=>Poly.toll P.w s*‖z‖) tested.symm).trans_le healthy

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
    {F : Frame G 0} (S : SectionData F) (Y : Hol G) {μ : ℝ}
    (reader : Readable Y S (rp).p (R.family.side (j+1) per) μ) :
    let τ:=min 1 ((ε*g^p)/(8*elected^P.op.count))
    let s:=(Stock.census V).fire v
    let unmasked:=WilsonOlderSignedSingletonFare.fare (rp).p S Y weights s 1 Z rad
      ((elected^6)⁻¹*((8*elected^P.op.count)*τ+ε*g^p)) (βh^(-(q:ℝ))*κ) κ allowance μ
    let outputMask:=WilsonOlderSignedOneMarkMasks.fare (rp).p Z allowance (Poly.toll P.w s) (allFee*elected) κ
    let recon:=ε*g^((order:ℝ)+1-η)*P.cost
    let balance:=WilsonOlderFreshReversionStore.price (rp).p S Y Z rad μ allowance κ (Poly.toll P.w s) recon (allFee*recon)
    (8*elected^P.op.count)*τ≤ε*g^p ∧
    ∃ A : Coefficient F (R.family.side (j+1) per), A.Format y Y rp ∧
      A.remBound y rp κ ((unmasked+outputMask)+balance) ∧ (∀ U, A.density y S rp U =
        (pushFace U).part s-((rp).eval U:ℂ)*(Spill.Foundry.uncut L.model gl x U).part s) ∧
      Poly.toll P.w s*F.coeffSize A.x ≤ testPrice F*(2*(ε*g^p)+recon) := by
  intro τ s unmasked outputMask recon balance
  obtain ⟨tuned,A,fmt,fee,field⟩:=WilsonOlderFreshPaidEdge.original R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats floor physical P L file course cut pass month fits narrow x way simple late p q ready deep aged
    ep positive unit opened recalled scroll chamber hospital warm top load packed freshDepth space v Z y center member
    rad near S Y reader
  let U : Config G (R.family.side (j+1) per):=1
  let t:ℂ:=(rp).eval U
  let first:ℂ:=t⁻¹*((pushFace U).part s-t*(Integral.markedLog g U upperBank).part s)
  let last:ℂ:=(Integral.markedLog g U upperBank).part s-(Spill.Foundry.uncut L.model gl x U).part s
  have hi₁ : Poly.toll P.w s*‖first‖≤2*(ε*g^p):=
    WilsonOlderFreshScalar.flat R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades order shelf seats
      physical P simple p deep aged ep opened scroll chamber hospital warm top fits load packed freshDepth space x v
  have hi₂ : Poly.toll P.w s*‖last‖≤recon:=
    flatChange R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor physical P L file course
      cut pass month fits narrow x hospital load simple positive unit ep recalled v
  let pay:=Poly.toll P.w s
  have hp : 0≤pay := (Poly.worth P.issued.earning.positive s).le
  have sum : pay*‖first+last‖ ≤ 2*(ε*g^p)+recon :=
    (mul_le_mul_of_nonneg_left (norm_add_le _ _) hp).trans ((mul_add pay _ _).trans_le (add_le_add hi₁ hi₂))
  have read (pr : Probe G 0) : runProbe F pr A.x=first+last := by
    have zero : pr.2.val=0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ pr.2.isLt)
    have seen:=WilsonCenteredDetectorUnit.flatProbe A fmt reader.sound pr zero
    calc
      _ = t⁻¹*A.density y S rp U := seen
      _ = t⁻¹*((pushFace U).part s-t*(Spill.Foundry.uncut L.model gl x U).part s) := congrArg (fun z=>t⁻¹*z) (field U)
      _ = _ := by
        have live : t≠0 := Complex.ofReal_ne_zero.mpr WilsonCenteredCaptureUnit.physicalDenominator.ne'
        dsimp only [first,last]
        field_simp [live]
        ring
  have size : F.coeffSize A.x≤testPrice F*‖first+last‖ :=
    (probe_budget F).choose_spec.choose_spec.2 A.x _ (norm_nonneg _) (fun pr _=>(congrArg norm (read pr)).le)
  refine ⟨tuned,A,fmt,fee,field,?_⟩
  calc
    _ ≤ pay*(testPrice F*‖first+last‖) := mul_le_mul_of_nonneg_left size hp
    _ = testPrice F*(pay*‖first+last‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left sum (zero_le_one.trans (probe_budget F).choose_spec.choose_spec.1)

end YM.Integration.WilsonOlderFreshPaidUnit
