import YM.Integration.WilsonMeasuredRankedFare

/-! The real earned expense of the same dated Wilson post, to any fixed
power, can be restored at a uniform subpower cost before either regulator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredSemesterSubpower
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

open Filter
theorem budget (r:ℕ) {δ:ℝ} (pos:0<δ) :
    ∀ᶠ t:ℕ in atTop, ∀ Ω₀:ℝ, 0≤Ω₀ →
      Ω₀≤(R.alloy.B.a.clock.hatBeta (t+1))^Beaming.grain (R.alloy.B.a.clock.J t) →
      Ω₀^r≤(R.alloy.B.a.clock.hatBeta (t+1))^δ := by
  let f:=fun i=>R.alloy.B.a.clock.J i+1
  have h:Tendsto f atTop atTop:=tendsto_atTop_mono (fun i=>Nat.le_succ (R.alloy.B.a.clock.J i)) R.alloy.B.a.fits.deep
  have thin:Tendsto (fun i:ℕ=>Beaming.grain (R.alloy.B.a.clock.J i)) atTop (nhds 0):=by
    convert (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp h) :
      Tendsto (fun i=>(↑(f i):ℝ)⁻¹) atTop (nhds 0)) using 1
    funext i
    simp [Beaming.grain,f,one_div]
  have prices:Tendsto (fun i:ℕ=>Beaming.grain (R.alloy.B.a.clock.J i)*(r:ℝ)) atTop (nhds 0):=by
    simpa only [zero_mul] using thin.mul_const (r:ℝ)
  filter_upwards [prices.eventually_le_const pos] with t small
  intro b bn low
  let z:=R.alloy.B.a.clock.hatBeta (t+1)
  have high:1≤z:=(R.alloy.B.a.fits.delayed (t+1)).le
  have z0:0≤z:=zero_le_one.trans high
  calc
    _ ≤ (z^Beaming.grain (R.alloy.B.a.clock.J t))^r:=pow_le_pow_left₀ bn low r
    _ = z^(Beaming.grain (R.alloy.B.a.clock.J t)*(r:ℝ)) :=(Real.rpow_mul_natCast z0 ..).symm
    _ ≤ _:=Real.rpow_le_rpow_of_exponent_le high small

def onset (r:ℕ) {δ:ℝ} (pos:0<δ) : ℕ := (eventually_atTop.mp (budget R r pos)).choose

include course cut in
theorem charged (r:ℕ) {δ:ℝ} (pos:0<δ) (live : onset R r pos ≤ i)
    (pass:Pass D Q R.alloy R.kit) (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (shelved:shelf≤R.alloy.B.a.clock.J i) (load:P.op.count≤Burn.horizon k+2) :
    Ω^r≤(R.alloy.B.a.clock.hatBeta (i+1))^δ :=
  (eventually_atTop.mp (budget R r pos)).choose_spec i live Ω P.issued.Waffle.paysAbove.le
    (WilsonMeasuredRankedFare.salary R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades order shelf
      seats physical P pass hospital shelved load)

end YM.Integration.WilsonMeasuredSemesterSubpower
