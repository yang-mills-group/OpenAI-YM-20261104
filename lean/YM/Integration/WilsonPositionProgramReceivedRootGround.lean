import YM.Integration.WilsonPositionProgramReceivedOccupiedCaps
import YM.Integration.WilsonPositionProgramReceivedRecastDrivers
import YM.Integration.WilsonPositionProgramRecastInputInvoice

/-! Genuine normalized next-block log, with its full inherited Wilson cofactor and original quiet upon insertion. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramReceivedRootGround
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

open Next.SectorChange Next.Rank Comparison.RG02.Cumulants
open WilsonPositionProgramFiledGaussianChange
local notation "lowerK" => (RunFormalChain.fromRun R).step N j per (lt_trans (Nat.lt_succ_self j) cut)
local notation "upperStep" => (R.family.path.levels.clock.op (j+1) per)


open WilsonPositionProgramDatedDrivers WilsonPositionProgramDatedGaussianCaps
local notation "E" => RegulatorIR.Halo.bios lowerStep
local notation "v₀" => (order+shelf+1)
local notation "h₀" => (Burn.horizon k+4)
local notation "marks₀" => Stock.census V
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (j+1))
local notation "shared" => (fun v=>min (P.w v) (L.w v))
local notation "probes" => (fun s:(marks₀).Mode=>WilsonPositionProgramResetProbeWallet.total back order (resetDegree grades s order))
local notation "age₀" r:max => WilsonPositionProgramDatedGaussianCaps.power marks₀ grades r v₀ h₀
local notation "base₀" top:max => (WilsonPositionProgramDatedDrivers.salary (R:=marks₀) (r:=top) G grades σ₀ order shelf)
local notation "change₀" top:max => (movement (R:=marks₀) (r:=top) G grades h₀ probes)
local notation "high₀" A:max => WilsonPositionProgramMeasuredFieldShift.height G (R.family.side j per) (WilsonPositionProgramRecastInputInvoice.mean R j) ‖A‖


include file course cut pass month fits narrow in
theorem original (F:Forest (upperStep).ratio)(tag:(upperStep).Choices)(q exponent:ℕ)(ε:ℝ)(he:0<ε)
    (large:threshold R D Q books (j+1) k q seats exponent ε he≤(nside).val)
    (out:(lowerStep).Choices)(A:fieldDir G (R.family.side j per) 1)(s:(marks₀).Mode)(hs:s≠(marks₀).quiet):
    let d:=age₀ 0
    let c:=(ε*heat^q)/((nside).val:ℝ)^exponent
    let delta:=c*amount (change₀ 0) (high₀ A) d
    let B:=1+amount (base₀ 0) (high₀ A) d+delta
    Poly.toll shared s*‖(observe marks₀ 0 (logMarked (Bulk.Fk lowerK E out (rebuilt F tag) A 0)) 0).part s-
      (observe marks₀ 0 (logMarked (Bulk.Fk lowerK E out bankNow A 0)) 0).part s‖≤
      delta*WilsonPositionProgramGaussianConnectedBank.price (Board marks₀ 0) (Precision.Key E G)
        (variance R j) B d (Join.pair s (pick 0 0)) := by
  let c:=(ε*heat^q)/((nside).val:ℝ)^exponent
  let d:=age₀ 0
  let b₀:=amount (base₀ 0) (high₀ A) d
  let δ:=c*amount (change₀ 0) (high₀ A) d
  have hδ:0≤δ:=by
    have c0:0≤c:=by dsimp [c,Coat.gStep];positivity
    exact mul_nonneg c0 (WilsonPositionProgramDatedGaussianCaps.nonneg _ _ _)
  have wpos(i:V):0<shared i:=lt_min (P.salary.positive i) (L.salary.positive i)
  have all(i:Multi.Hot (Board marks₀ 0))(z:Precision.Key E G→ℝ):=
    WilsonPositionProgramReceivedOccupiedCaps.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf
      seats floor physical P L file course cut pass month fits narrow x F tag 0 (Nat.zero_le _) q exponent ε he large
      out A i (WilsonPositionProgramHeatedWallet.zero i) z
  have invoice:=WilsonPositionProgramFiniteGaussianReturn.original lowerK E out (rebuilt F tag) bankNow A
    (d:=0) (r:=0) (Nat.le_refl 0) shared wpos d (base:=b₀) (δ:=δ)
    (WilsonPositionProgramDatedGaussianCaps.nonneg _ _ _) hδ (variance R j)
    (WilsonPositionProgramDatedGaussianCaps.paid R N j per (lt_trans (Nat.lt_succ_self j) cut) out)
    (fun i z=>(all i z).1) (fun i z=>(all i z).2) s hs
  simpa only [Nat.factorial_zero,Nat.cast_one,one_mul] using invoice

end YM.Integration.WilsonPositionProgramReceivedRootGround
end
