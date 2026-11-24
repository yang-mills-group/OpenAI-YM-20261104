import YM.Integration.WilsonOlderSignedOneMarkPhysicalFare

/-! The original school expense and one-source return price on any fixed physical section. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredRankedFare
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

open Pert.Asymptotics RG16 WilsonOlderSignedOneMarkTariff
local notation "η₀" => R.alloy.B.a.clock.forcedAllowance i
local notation "y" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "μ₀" => (R.family.path.levels.params i).columns
variable (fieldRank : ℕ)
local notation "stencil" => R.family.localSection fieldRank
local notation "Y₀" => R.family.params
local notation "base" => 2*Real.exp 102*(1+2*charge Y₀ stencil)
local notation "c" => (Stock.census V)
local notation "origin" a:max => ((P.passport.coarser (sheet).ratio).origin a)

include course cut in
theorem salary
    (pass : Pass D Q R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (shelved : shelf ≤ R.alloy.B.a.clock.J i) (load : P.op.count ≤ Burn.horizon k+2) :
    Ω ≤ y ^ (Beaming.grain (R.alloy.B.a.clock.J i)) := by
  let iWalk:=course.1.walk i hi cut.le
  let jWalk:=course.1.walk (i+1) (Nat.le_succ_of_le hi) cut
  let paidWalk:=(WilsonMovingMentorIncomingSlots.original R course hi cut).2.2.choose
  letI : Countable P.modelIndex:=P.modelCount
  have band : (Ψ (i+1)).beta∈Shoot.band R.alloy.B.a (i+1) := jWalk.beta ▸
    (R.makes.wilson.represents N per (i+1) cut).band
  have wallet:=Mentor.Cruise.Semester.tight D R.rolls Q R.alloy R.kit φ books pass P.op
    (Oak.era R hk D Q π Γ hi P.op P.lesson) (R.alloy.B.a.S.oneStep i per).exact_size P.model order
    P.voter ahead jWalk.truep.point paidWalk iWalk.truep.point hospital load shelf shelved band
  exact wallet.1.trans (min_le_right ..)

include course cut in
private theorem expense (simple : G.Simple) (late : WilsonReceivedSourceGross.opening R simple ≤ i)
    (pass : Pass D Q R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (shelved : shelf ≤ R.alloy.B.a.clock.J i) (load : P.op.count ≤ Burn.horizon k+2) :
    Ω ≤ y := by
  have window := (eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose_spec i late
  have grain : Beaming.grain (R.alloy.B.a.clock.J i) ≤ 1 := by
    unfold Beaming.grain
    exact (div_le_one (by positivity)).mpr (by linarith only [Nat.cast_nonneg (α:=ℝ) (R.alloy.B.a.clock.J i)])
  exact (salary R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades order shelf seats physical P
    pass hospital shelved load).trans
    ((Real.rpow_le_rpow_of_exponent_le (window.1.trans window.2.1) grain).trans_eq (Real.rpow_one _))

private theorem shed {z t g β : ℝ} (zp : 0<z) (tp : 0≤t) (wage : t≤z)
    (unit : g^2*β=1) (band : β≤2*z) (q : ℕ) :
    t^6*z^(-((q+6:ℕ):ℝ)) ≤ (2*g^2)^q := by
  have inv : z⁻¹≤2*g^2 := (inv_le_iff_one_le_mul₀ zp).2 (by
    nlinarith only [unit,mul_le_mul_of_nonneg_left band (sq_nonneg g)])
  calc
    _ ≤ z^6*z^(-((q+6:ℕ):ℝ)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ tp wage _) (Real.rpow_nonneg zp.le _)
    _ = (z⁻¹)^q := by
      rw [Real.rpow_neg zp.le,Real.rpow_natCast,pow_add,mul_inv,inv_pow];field_simp
    _ ≤ _ := pow_le_pow_left₀ (inv_nonneg.mpr zp.le) inv q

include course cut in
theorem original (simple : G.Simple)
    (slow : ∀ m, ((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (prepared : WilsonReportLampForecast.Ready R.family.path.levels)
    (fixed : (R.family.path.levels.budget i).supportExponent≤100)
    (late : WilsonReceivedSourceGross.opening R simple ≤ i)
    (atDate : WilsonOlderSignedOneMarkPhysicalFare.opening R simple slow prepared ≤ i)
    (pass : Pass D Q R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (shelved : shelf ≤ R.alloy.B.a.clock.J i) (load : P.op.count ≤ Burn.horizon k+2)
    (v : V) (e : ℝ) (he : 0≤e) (q : ℕ) :
    let s:=(c).fire v
    Poly.toll P.w s*WilsonOlderSignedSingletonFare.fare (Ψ i).p stencil Y₀ weights s 1 {origin v} 0
      ((Ω^6)⁻¹*e) (y^(-((q+6:ℕ):ℝ))*κ) κ η₀ μ₀ ≤
        base*(gf⁻¹)^4*e+2*Real.exp 102*(2*gf^2)^q := by
  intro s
  obtain ⟨hx,_,motion,columns,kp,_,hn,room,reserve⟩:=
    (eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow prepared)).choose_spec i atDate N per cut
  have budget:=(course.1.walk i hi cut.le).truep.point
  have support : (Ψ i).p.supportExponent ≤ 100 := by rw [budget]; exact fixed
  have moved : WilsonCenteredLampCapture.stage (Ψ i).p 0 ({()}:Finset Unit) ≤ 2*(gf⁻¹)^2 := by
    rw [budget]
    exact (WilsonCenteredCaptureGeometry.motion _ (Nat.zero_le _) _ (by simp)).trans motion
  have oy : 0< y:=lt_trans zero_lt_one (R.alloy.B.a.fits.delayed (i+1))
  let β:=(R.family.path.rep N per (i+1)).beta
  have bp : 0<β:=Overlay.beta_positive R.makes.wilson cut
  have unit : gf^2*β=1 := by
    change (Real.sqrt β)⁻¹^2*β=1
    rw [inv_pow,Real.sq_sqrt bp.le,inv_mul_cancel₀ bp.ne']
  have small:=shed oy (zero_le_one.trans P.issued.Waffle.cool) (expense R hk D Q π Γ Ψ course books hi cut
    ahead actors pieces grades order shelf seats physical P simple late pass hospital shelved load) unit
    (R.makes.wilson.represents N per (i+1) cut).band.2 q
  have reservePoint : hitWidth (Ψ i).p*η₀/κ≤1 := by rw [budget];exact reserve
  have roomPoint : hitWidth (Ψ i).p*η₀≤1 := by rw [budget]; exact room
  have price:=point (r:=Ω^6) (Ψ i).p stencil Y₀ P.w v (origin v) (P.issued.earning.positive v)
    (pow_pos P.issued.Waffle.paysAbove _) kp hx support (zero_le_one.trans (R.family.path.levels.params i).columns_ge)
    columns moved hn roomPoint reservePoint he (Real.rpow_nonneg oy.le (-((q+6:ℕ):ℝ)))
  exact price.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left small (show 0≤2*Real.exp 102 by positivity)))

end YM.Integration.WilsonMeasuredRankedFare
