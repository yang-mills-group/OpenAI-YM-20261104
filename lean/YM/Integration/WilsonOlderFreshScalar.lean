import YM.Integration.WilsonOlderFreshIssuedIntake
import YM.Integration.WilsonOlderSignedOneMarkScalar

/-! The signed unit at the center of the freshly planted physical source is paid at its original mark radius. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshScalar
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

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

local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "lamps" => (rendered student (Ψ i).p oldG)
local notation "gauge" => (Tint.Patrol.report student P.output oldG)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "width" => ((Ψ i).p.supportExponent+1+1)

local notation "weights" => Stoop.radius P.w (Ω^6)
local notation "homes" => (P.passport.coarser (sheet).ratio).origin
local notation "debt" => (⟨P.output.old,P.output.hard⟩ :
  Gallery (Wallet actors) P.outputIndex homes (Ψ i) (Stock.census V))
local notation "βhat" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "gf" => Coat.gStep (R.family.path.rep N per (i+1)).beta

local notation "fresh" => (fun (x : Wallet actors) (U : Config G (R.family.side (i+1) per)) =>
  ((Ψ (i+1)).eval U : ℂ) • Poly.pass (Spill.Foundry.uncut P.model oldG x U))

include course cut in
theorem flat (simple : G.Simple) (p : ℕ) (deep : 2*(p+1)+8 ≤ order)
    (aged : p+4 ≤ 3*k+2) {ε : ℝ} (ep : 0<ε)
    (opened : WilsonFirstReceivedEarnedFee.opening R simple P.op.count p order k deep aged ep ≤ i)
    (scroll : VowsR.LawScroll G φ) (chamber : VowsR.Chamber scroll R.kit D Q books)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (warm : Spill.Raffle.Warm G D R.alloy.delay φ)
    (top : Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
    (fits : order ≤ Burn.horizon k+1) (load : seats ≤ Burn.horizon k+2)
    (packed : order+shelf ≤ Burn.horizon k+2)
    (depth : ℕ) (space : Sycamore.Boot.need depth (⟨order,seats,shelf,load,fits,packed⟩ : Syl.School k)
      ≤ R.alloy.B.a.clock.J (i+1))
    (x : Wallet actors) (v : V) :
    let s := (Stock.census V).fire v
    let U : Config G (R.family.side i per) := 1
    let t : ℂ := (Ψ i).eval U
    let raw := Integral.markedLog gf U (Air.craft student (fun b=>(student b).paint x) grades (π i)
      (AllOrder.Floe.Step.tape (Burn.horizon k+2)))
    Poly.toll P.w s*‖t⁻¹*((LocalComparison.actualPush R.family N per i (fresh x) U).part s-t*raw.part s)‖
      ≤ 2*(ε*gf^p) := by
  intro s U t raw
  let τ:=min 1 ((ε*gf^p)/(8*Ω^P.op.count))
  have gp : 0<gf := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  have budget : 0<Ω := zero_lt_one.trans_le P.issued.Waffle.cool
  have mult : 0<8*Ω^P.op.count := mul_pos (by norm_num) (pow_pos budget _)
  have positive : 0<τ := lt_min zero_lt_one (div_pos (mul_pos ep (pow_pos gp _)) mult)
  have one : τ≤1 := min_le_left ..
  have tuned : (8*Ω^P.op.count)*τ≤ε*gf^p := (mul_comm _ _).trans_le ((le_div_iff₀ mult).mp (min_le_right ..))
  obtain ⟨L,op,lesson,_,_,_,w,_,rent,_,_,_,printed⟩ :=
    WilsonOlderFreshIssuedIntake.original R hk D Q π Γ Ψ course books ahead actors pieces grades
      order shelf seats hi physical P simple cut scroll chamber hospital warm top fits load packed
      depth space x τ positive one
  have heard:=WilsonOlderSignedOneMarkScalar.flat R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades
    order shelf seats fresh L simple p deep aged ep (by simpa only [op] using opened) x v
  have read:=heard.2
  let calcRaw := fun z : Poly (Stock.census V) => Poly.toll L.w s*
    ‖t⁻¹*((LocalComparison.actualPush R.family N per i (fresh x) U).part s-t*z.part s)‖
  have sized := (congrArg calcRaw (printed gf x U).symm).trans_le read
  change Poly.toll L.w s*_ ≤ _ at sized
  rw [w,op,lesson,rent] at sized
  exact sized.trans (by linarith)
end YM.Integration.WilsonOlderFreshScalar
