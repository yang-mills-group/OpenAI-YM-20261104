import YM.Integration.FVA1Physical.MixedResets.Joined
import YM.Integration.FVA1Physical.MixedResets.Lift
import YM.QuadraticLocal.Relative.Ribbon

/-!
# Price on the representation sent to the next step

At all costs including after the REAL coupling calibration. `Witness'`s proof
keeps `Vₜ` explicit but it is a Prop. Repaid to original radii even when
reserve-shrunk at input. These local bounds use no normalization from
measurements of the outgoing/incoming evaluated Mark magnitudes. Instead use
certificate on its actual decomposition and Earn analytic data. Do not use a
claim of per-occurrence contraction when overlapping; keep all models and error
slots in ONE Census. No mismatched logistics re-using a different birth ad hoc.
Return both input & output norm statements at restored w, including full force
on ALL the carriers. Simultaneous with a menu extending even to requests in
Lite full/unrooted format (previous CP5, applicable on the same registration).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.MixedResets
open Function Filter Finset Lattice RG RG.Supply Precision Wilson Marker
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Ker
open Push ConnectedActivityE6 Input Org PhysicalNext PhysicalNext.Repeat Legato
open Uniform Next.SectorChange ThroughLaunch Pane AbsoluteSums PriceCompiler
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open Kinetic.Port Progress.ClassicalKin Progress.ClassicalKin.Tent
open Pressure Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset
open Roost Legato Graces Extra.Iteration Extra.Histories
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open Comparison.RG02 Further.PhysicalPeriodLimitF933 Tree
open Oak
open scoped Topology BigOperators Classical

variable {G : Gauge} (R : Run G) {m n i k N : ℕ} (J : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ i, RG.Rep G (R.family.side i n))
  (conc : Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
  {φ : ℕ → ℕ} (clock : Offices.Books D R.rolls Q φ) (ahead : Mentor.Forecast D R.rolls Q φ clock)
  (hi : m ≤ i) (cut : i<N) (L : Lesson (N:=N) R J D Q π Γ hi)
set_option quotPrecheck false
local notation "σ" => R.alloy.B.a
local notation "I" => R.alloy.B.a.clock.J i
local notation "I'" => R.alloy.B.a.clock.J (i+1)
attribute [local irreducible] Till.Tilt.sundry
local notation "C" => R.alloy.B.a.budget i
local notation "Fμ" => R.alloy.B.a.budget (i+1)
local notation "Uu" => (Ψ (i+1))
local notation "P'" => (Ψ i)
local notation "Gm" => (Coat.gStep ((Ψ i).beta))
local notation "Wc" => (Time.quoteHard (σ) i (R.kit.book) (Ψ (i+1)).beta)
local notation "τ" => R.family.path.levels.clock.op i n
local notation "µ" => (τ).ratio
local notation "p₀" => (Burn.horizon k+2)
local notation "g" => Coat.gStep (Ψ (i+1)).beta
local notation "κ" => LocalComparison.forcedDivisor R.family i

open QuadraticLocal.Syl
variable {Θ : Type} [Fintype Θ] [DecidableEq Θ] {R₀ : Marker.Census Θ}
  {X : Θ → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℝ (X i)]
  (allow : ∀ i, Set (X i)) (kills : ∀ i, Submodule ℝ (X i))
  (w₀ : Θ → ℝ) (grades : Θ → ℕ) (school : School k) (e_E ηz : ℝ) (s : ℕ)
  (f : Pupil (Ψ (i+1)) R₀ (Affinity.Wallet allow)) (aheadP : ℝ)
local notation "w" => (Stoop.radius w₀ aheadP)
variable (e : Ribbon (φ:=φ) R D Ψ allow kills grades school Set.univ (Stoop.radius w₀ aheadP) e_E f)
  (hw : ∀ i, 0 < w₀ i) (ha : 1 ≤ aheadP)
local notation "A" => (Ψ (i+1)).p
local notation "B" => (Ψ i).p
local notation "Z" => (f.packet)
local notation "Xv" => (Affinity.Wallet allow)
local notation "support" => f.address
local notation "M" => ( f.painter )
local notation "p" => (school.order)
local notation "r" => ((p:ℝ)+1-ηz)
local notation "T" => (PriceCompiler.step_paid R.alloy.B.a i)
local notation "cap" => (School.room school T (J.trans (R.alloy.B.a.fits.mono hi)))
local notation "voter" => ( voters R J D Ψ (φ:=φ) hi allow kills w grades school 1 1 f (Ribbon.seed e))
local notation "charge" => (aheadP^school.pieces)
variable (F₁ : Tree.Forest (Route.step R i n).ratio) (Fp : Pupil (Ψ i) R₀ (Affinity.Wallet allow))
local notation "mapTo" Λ:max => ( Sycamore.pupil R J D Q π Γ Ψ clock hi allow kills w grades school 1 1 f (Ribbon.seed e) L ahead Λ )
local notation "portrait" => ( Tint.Patrol.picture Fp.painter Fp.packet )
set_option maxHeartbeats 840000
local notation "Ω" => Oak.expenseReal R J D Q π Γ clock hi cap L ahead p school.horizon
local notation "ticket" => ( Oak.rebate R J D Q π Γ hi cap L )
local notation "lag" => (Ω^(school.pieces+1))
local notation "fine" => (8* lag*e_E + 16 * ((2:ℝ)^ r * (Coat.gStep (Ψ (i+1)).beta)^ r))
local notation "Due" => (8* lag*e_E + 17 * ((2:ℝ)^ r * (Coat.gStep (Ψ (i+1)).beta)^ r))
local notation "paid" Y:max P:max a:max b:max => (Y).Paid w₀ (P).B ((P).supportExponent+a) b
open MeasureTheory
/-- `currency` is on the **signed connected** residual of the actual mutable
model report after taking it through a coupling reset. Local mixed estimate w.r.t.
requested e_E; does not require suppressing the unmarked residual further than its
`Appearance`. `at_work` etc preserve the entire mixed polynomial INCLUDING its
reported conditional denominator on any t. `optIn` also gives the *pre*-presentation
with qev gain on full e (here applied at attained rates) and authentic periodized-cover
spec governing both reads. Budget at true w (repaid through its **specific** charge
multiplier). `aid` optional — for comparing legacy inputs with currencies restored even
on the hard ledger if this theorem used at reduced radii by Learn. `aid` does not
supply or expect any cap on that restoration sufficient for next call; it merely
prices it. In Beat we carry a stronger, sharpened REGISTERED part along the path
already in the original w.
-/
structure InvoiceHistory : Prop where
  certificate : ∃ (J':Type) (_h : Countable J') (Vnew : Tint.Incoming ( f.address.coarser ((τ).ratio) ) (Ψ i) Xv J' R₀),
    Fp = mapTo Vnew ∧ LiveStep R J D Q π Γ Ψ clock ahead hi cut L cap f.address allow kills M Z w grades p school.horizon e_E 1 ηz s F₁ voter Vnew ∧
    Full (Ψ i) w₀ κ Vnew 2 (charge * fine) (charge * ((2*g)^(2*s)))
  wilson : Renderer Fp.painter (π i) (Step.tape p₀) grades p (Route.reexpress R N p₀ (π (i+1)) M p (Route.calibrator R D Q J π Γ hi L))
  at_work x : let Wout:=(Tint.Patrol.picture Fp.painter Fp.packet).density x
              let Y:=( Tint.Patrol.picture M Z ).density x
              let VAC:=(Route.step R i n).push (Ψ (i+1)).beta (Ψ (i+1)).eval
              Wout=(Route.step R i n).push (Ψ (i+1)).beta Y ∧
              ( ∀ K, 0 < VAC K ) ∧ ( Ψ i ).eval= VAC ∧ Integrable Y (prior G (R.family.side (i+1) n)) ∧
              Integrable Wout (prior G (R.family.side i n))
  optics : Fp.address=f.address.coarser (µ)
  custody : Earn.Tableau kills allow Fp.painter ∧ Affinity.Taut Fp.address.support allow kills Fp.packet.old ∧ Affinity.Crown Fp.address.support allow kills Fp.packet.hard
  currency : Full (Ψ i) w₀ κ Fp.packet 2 (charge * Due) (charge * ((2*g)^(2*s)))
  whole : (portrait).E.Paid w₀ (B).B ((B).supportExponent+2) (charge * (ticket * (Ω^2 * 1) + Due))
  aid : Z |>.old.Paid w₀ (A).B (A).supportExponent (charge * e_E) -- parentheses correction
  interim : Z |>.hard.Paid w₀ (A).B (A).supportExponent (charge * 1)

variable [Nonempty (Affinity.Wallet allow)]
include cut hi ha hw
set_option maxHeartbeats 980000
lemma accounting {J' : Type} [Countable J']
    (Vnew : Tint.Incoming ( f.address.coarser ((τ).ratio) ) (Ψ i) Xv J' R₀)
    (he : Fp = mapTo Vnew) (bill : LiveStep R J D Q π Γ Ψ clock ahead hi cut L cap f.address allow kills M Z w grades p school.horizon e_E 1 ηz s F₁ voter Vnew) :
    InvoiceHistory (i:=i) R J D Q π Γ Ψ clock ahead hi cut L allow kills w₀ grades school e_E ηz s f aheadP e F₁ Fp := by
  rw [he]; let t := mapTo Vnew
  let q := bill.post; let r₀ := bill.identification
  let g₀ := e.seed.total.quota
  refine ⟨⟨J',inferInstance,Vnew,rfl,bill, q.earned.retake w₀ g₀ hw ha⟩,
    q.wilson.2,fun x => ?_,rfl,q.custody, q.late.retake w₀ g₀ hw ha, Stoop.retake w₀ _ g₀ hw ha q.billing.2.2,
    Stoop.retake w₀ _ g₀ hw ha (pay_all _ e.clean), Stoop.budget w₀ g₀ _ hw ha e.seed.policy ⟩
  intro Wout y K
  exact ⟨( q.actual x ).2.2.trans ( q.actual x ).2.1,r₀.notZero.2,r₀.hvac.2.2,(q.actual x).1,(r₀.integ x).2.1⟩
end YM.Integration.FVA1Physical.MixedResets
