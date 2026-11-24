import YM.Integration.WilsonPositionProgramReceivedRecastCurved
import YM.Integration.WilsonPositionProgramRecastDraw

/-! Signed prices on the real translated fluctuations for every generator of the next Wilson block. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramReceivedRecastDrivers
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

private theorem invoice {a b c d h:ℝ}(hb:0≤b)(sold:a*c≤d*h):a*(b*c)≤b*d*h:=by
  rw [mul_left_comm a b c,mul_assoc b d h]
  exact mul_le_mul_of_nonneg_left sold hb

include file course cut pass month fits narrow in
theorem original (F:Forest (upperStep).ratio)(tag:(upperStep).Choices)(r:ℕ)(hr:r≤order)
    (q exponent:ℕ)(ε:ℝ)(he:0<ε)
    (large:threshold R D Q books (j+1) k q seats exponent ε he≤(nside).val)
    (E:Forest (lowerStep).ratio)(out:(lowerStep).Choices)(A:fieldDir G (R.family.side j per) 1)
    (i:Multi.Hot (Board (Stock.census V) r))(hit:(Join.left i.val).val.Nonempty)
    (z:Precision.Key E G→ℝ):
    let s:Multi.Hot (Stock.census V):=⟨Join.left i.val,hit⟩
    let t:=(Join.right i.val).val.card
    let J:=(bankNow).power s+t
    ((nside).val:ℝ)^exponent*Poly.toll P.w s.val*
        ‖Cloud.paint z (drivers lowerK E out (rebuilt F tag) A r i-drivers lowerK E out bankNow A r i)‖ ≤
      ‖(t.factorial:ℂ)‖*(2*(2*WilsonPositionProgramCurvedAngularPrice.price G J (Burn.horizon k+4)+1)*
          ((ε*heat^q)*tariff s*(2+‖(arm).symm.toContinuousLinearMap‖)^(Burn.horizon k+4)))*
            (1+‖(Bulk.translated lowerK E A z).2‖)^(J*(Burn.horizon k+4)) := by
  let s:Multi.Hot (Stock.census V):=⟨Join.left i.val,hit⟩
  let t:=(Join.right i.val).val.card
  have ht:t≤order:=by
    apply le_trans _ hr
    simpa only [Fintype.card_fin] using (Finset.card_le_univ (Join.right i.val).val)
  have sale:=WilsonPositionProgramReceivedRecastCurved.original R hk D Q π Γ Ψ books ahead actors pieces
    grades order shelf seats floor physical P L file course cut pass month fits narrow x F tag s
    t ht q exponent ε he large E (Bulk.translated lowerK E A z).2
  dsimp only
  rw [WilsonPositionProgramRecastDraw.occupied lowerK E out (rebuilt F tag) bankNow A i hit z,norm_mul]
  exact invoice (norm_nonneg (t.factorial:ℂ)) sale

end YM.Integration.WilsonPositionProgramReceivedRecastDrivers
end
