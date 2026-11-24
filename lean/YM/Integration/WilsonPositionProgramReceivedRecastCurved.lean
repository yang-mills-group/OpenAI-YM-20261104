import YM.Integration.WilsonPositionProgramReceivedRecastRay
import YM.Integration.WilsonPositionProgramCurvedMarkedSlot

/-! The complete occupied delta under the actual nonlinear fluctuation in the next enrolled Wilson block. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramReceivedRecastCurved
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Stationary Comparison.RG02 Comparison.RG02.Order Further.PhysicalPeriodLimitF933 Laurent
open scoped Classical BigOperators

open WilsonOriginalReceivedChain
open Exterior FVA1Physical.Wilson Comparison.RG02.Assembly
open Comparison.RG02.Adjacent Comparison.RG02.Valence Comparison.RG02.Symmetry Comparison.RG02.Moving.Path

open Push.AbsoluteSums

open WilsonPositionProgramReceivedMarkedPeriod

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
local notation "arm" => Stationary.arm G (R.family.side (j+1) per) 1
local notation "curriculum" => litP D R.alloy Q (hk.trans (R.alloy.B.a.fits.mono hi)) P.lesson.entry
local notation "back" => ((Rebirth.caliber ((curriculum).issue P.lesson.entry) ((curriculum).sustenance.due P.lesson.entry).1).back depth)


local notation "opK" => (RunFormalChain.fromRun R).step N (j+1) per cut
local notation "rebuilt" F:max tag:max => recastColors opK F tag priorBank grades order back bankNow
local notation "nside" => (R.family.side (j+1) per)
local notation "heat" => (Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta)
local notation "tariff" s:max => WilsonPositionProgramResetProbeWallet.total back order (resetDegree grades (s).val order)

local notation "lowerStep" => (R.family.path.levels.clock.op j per)

include file course cut pass month fits narrow in
theorem original (F:Forest (R.family.path.levels.clock.op (j+1) per).ratio)
    (tag:(R.family.path.levels.clock.op (j+1) per).Choices)(s:Multi.Hot (Stock.census V))
    (t:ℕ)(ht:t≤order)(q exponent:ℕ)(ε:ℝ)(he:0<ε)
    (large:threshold R D Q books (j+1) k q seats exponent ε he≤(nside).val)
    (E:Forest (lowerStep).ratio)(b:Bulk.SliceDir lowerStep E G):
    let J:=(bankNow).power s+t
    ((nside).val:ℝ)^exponent*Poly.toll P.w s.val*
        ‖jet (Bulk.markFn lowerStep E (rebuilt F tag) s) J (1,b)-jet (Bulk.markFn lowerStep E bankNow s) J (1,b)‖ ≤
      2*(2*WilsonPositionProgramCurvedAngularPrice.price G J (Burn.horizon k+4)+1)*
          ((ε*heat^q)*tariff s*(2+‖(arm).symm.toContinuousLinearMap‖)^(Burn.horizon k+4))*
            (1+‖b‖)^(J*(Burn.horizon k+4)) := by
  let γ:=((nside).val:ℝ)^exponent*Poly.toll P.w s.val
  let w:=(ε*heat^q)*tariff s*(2+‖(arm).symm.toContinuousLinearMap‖)^(Burn.horizon k+4)
  have npos:0<((nside).val:ℝ):=by exact_mod_cast (nside).property
  have hp:0<γ:=mul_pos (pow_pos npos _) (Poly.worth P.salary.positive s.val)
  have ew:0≤w:=by
    apply mul_nonneg _ (by positivity)
    exact mul_nonneg (mul_nonneg he.le (by unfold Coat.gStep; positivity))
      (WilsonPositionProgramResetProbeWallet.nonneg ..)
  have hW:=FVA1Physical.Wilson.recast_grade opK F tag priorBank grades order back bankNow (fun _=>rfl) s
  have legalLo : Legal tape₀ (π (j+1)) := by
    rw [L.lesson.ticket]
    exact AllOrder.Floe.Step.PlanV.audited R.rolls D _ _ _ L.lesson.entry
  have staff:=Air.license L.model (fun a=>(L.model a).paint x) grades L.w L.salary (Poetry.Agenda.stem ..)
    (fun a=>L.salary.honor a x)
  have hY:=((Air.standard L.model _ grades staff (π (j+1)) tape₀ legalLo).1).suppose_mark s
  have facing d (hd:d≤t) (u:fieldDir G nside 1):
      ‖(Air.discharge (rebuilt F tag) d u).part s.val-(Air.discharge bankNow d u).part s.val‖ ≤
        (w/γ)*(1+‖u‖)^(Burn.horizon k+4) := by
    have sale:=WilsonPositionProgramReceivedRecastRay.original R hk D Q π Γ Ψ books ahead actors pieces grades
      order shelf seats floor physical P L file course cut pass month fits narrow x F tag s d (hd.trans ht)
      q exponent ε he large u
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hp).2
    rw [mul_comm]
    exact sale
  have price:=WilsonPositionProgramCurvedMarkedSlot.original E (rebuilt F tag) bankNow s rfl hW hY t
    (Burn.horizon k+4) (w/γ) (div_nonneg ew hp.le) facing b
  let J:=(bankNow).power s+t
  let C:=2*(2*WilsonPositionProgramCurvedAngularPrice.price G J (Burn.horizon k+4)+1)
  change γ * ‖_‖ ≤ C*w*(1+‖b‖)^(J*(Burn.horizon k+4))
  calc
    _ ≤ γ*(C*((w/γ)*(1+‖b‖)^(J*(Burn.horizon k+4)))) := mul_le_mul_of_nonneg_left price hp.le
    _ = _ := by field_simp

end YM.Integration.WilsonPositionProgramReceivedRecastCurved
end
