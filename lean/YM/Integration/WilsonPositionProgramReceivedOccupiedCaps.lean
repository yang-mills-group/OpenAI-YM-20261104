import YM.Integration.WilsonPositionProgramDatedGaussianCaps
import YM.Integration.WilsonPositionProgramReceivedRecastDrivers
import YM.Integration.WilsonPositionProgramRecastInputInvoice

/-! Genuine normalized next-block log, with its full inherited Wilson cofactor and original quiet upon insertion. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramReceivedOccupiedCaps
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
local notation "base₀" r:max => (WilsonPositionProgramDatedDrivers.salary (R:=marks₀) (r:=r) G grades σ₀ order shelf)
local notation "change₀" r:max => (movement (R:=marks₀) (r:=r) G grades h₀ probes)
local notation "high₀" A:max => WilsonPositionProgramMeasuredFieldShift.height G (R.family.side j per) (WilsonPositionProgramRecastInputInvoice.mean R j) ‖A‖

include file course cut pass month fits narrow in
theorem original (F:Forest (upperStep).ratio)(tag:(upperStep).Choices)(r:ℕ)(hr:r≤order)
    (q exponent:ℕ)(ε:ℝ)(he:0<ε)
    (large:threshold R D Q books (j+1) k q seats exponent ε he≤(nside).val)
    (out:(lowerStep).Choices)(A:fieldDir G (R.family.side j per) 1)
    (i:Multi.Hot (Board marks₀ r))(hit:(Join.left i.val).val.Nonempty)(z:Precision.Key E G→ℝ):
    let d:=age₀ r
    let c:=(ε*heat^q)/((nside).val:ℝ)^exponent
    Poly.toll shared (Join.left i.val)*‖Cloud.paint z (drivers lowerK E out bankNow A r i)‖ ≤
      amount (base₀ r) (high₀ A) d*(1+‖z‖)^d ∧
    Poly.toll shared (Join.left i.val)*‖Cloud.paint z (drivers lowerK E out (rebuilt F tag) A r i-
      drivers lowerK E out bankNow A r i)‖≤(c*amount (change₀ r) (high₀ A) d)*(1+‖z‖)^d := by
  let s:Multi.Hot marks₀:=⟨Join.left i.val,hit⟩
  let t:=(Join.right i.val).val.card
  let J:=WilsonPositionProgramDatedDrivers.length grades i
  let b:=1+‖(Bulk.translated lowerK E A z).2‖
  let nn:=((nside).val:ℝ)
  let c:=(ε*heat^q)/nn^exponent
  have gp:0≤heat:=by unfold Coat.gStep;positivity
  have aq:0≤ε*heat^q:=mul_nonneg he.le (pow_nonneg gp _)
  have np:0<nn:=by dsimp [nn];exact_mod_cast (nside).property
  have cp:0≤c:=div_nonneg aq (pow_nonneg np.le _)
  have bp:1≤b:=by exact le_add_of_nonneg_right (norm_nonneg _)
  have zp:1≤1+‖z‖:=by exact le_add_of_nonneg_right (norm_nonneg _)
  have rn:=WilsonPositionProgramHeatedWallet.shrunk P.w L.w P.salary.positive L.salary.positive s.val
  have grow:=WilsonPositionProgramRecastInputInvoice.drawn R N j per (lt_trans (Nat.lt_succ_self j) cut) out A z
  have legalLo : Legal tape₀ (π (j+1)) := by
    rw [L.lesson.ticket]
    exact AllOrder.Floe.Step.PlanV.audited R.rolls D _ _ _ L.lesson.entry
  have cap:L.cost≤1:=L.affordable.trans (inv_le_one_of_one_le₀ L.issued.Waffle.cool)
  constructor
  · have dated:=WilsonPositionProgramDatedDrivers.occupied lowerK E out L.model L.w grades L.salary cap
      (Poetry.Agenda.stem ..) x (π (j+1)) tape₀ legalLo A hr i hit z
    have hitc:0≤(base₀ r) i:=by dsimp only [WilsonPositionProgramDatedDrivers.salary,WilsonPositionProgramDatedDrivers.gain,WilsonReceivedSourceCoefficientIncome.price];positivity
    have earned:Poly.toll shared s.val*‖Cloud.paint z (drivers lowerK E out bankNow A r i)‖ ≤ ((base₀ r) i)*b^(J*v₀):=
      (mul_le_mul_of_nonneg_right rn.2 (norm_nonneg _)).trans dated
    have lifted:=funded grades v₀ h₀ v₀ (le_max_left _ _) (base₀ r) i hitc zero_le_one bp zp grow
      (by simpa only [one_mul] using earned)
    simpa only [one_mul] using lifted
  · have raw:=WilsonPositionProgramReceivedRecastDrivers.original R hk D Q π Γ Ψ books ahead actors pieces grades
      order shelf seats floor physical P L file course cut pass month fits narrow x F tag r hr q exponent ε he large E out A i hit z
    let obs:=‖Cloud.paint z (drivers lowerK E out (rebuilt F tag) A r i-drivers lowerK E out bankNow A r i)‖
    let C:=2*(2*WilsonPositionProgramCurvedAngularPrice.price G J h₀+1)
    have prod:=WilsonPositionProgramResetProbeWallet.nonneg back order (resetDegree grades s.val order)
    have numeric:nn^exponent*(Poly.toll P.w s.val*obs)≤(t.factorial:ℝ)*(C*((ε*heat^q)*(probes s.val)*(2+‖(arm).symm.toContinuousLinearMap‖)^h₀))*b^(J*h₀):=by
      rw [←mul_assoc,←Complex.norm_natCast]
      exact raw
    have bound:=WilsonPositionProgramDatedDrivers.released (G:=G) nside exponent (J*h₀) h₀
      (R.family.side (j+1) per) (a:=ε*heat^q) (t:=(t.factorial:ℝ)) (C:=C) (w:=probes s.val) (b:=b)
      aq (Nat.cast_nonneg _) prod (zero_le_one.trans bp) (Poly.toll P.w s.val*obs)
      numeric
    have hitc:0≤(change₀ r) i:=by dsimp only [movement,gain];positivity
    have earned:Poly.toll shared s.val*obs≤c*((change₀ r) i)*b^(J*h₀):=
      (mul_le_mul_of_nonneg_right rn.1 (norm_nonneg _)).trans bound
    exact funded grades v₀ h₀ h₀ (le_max_right _ _) (change₀ r) i hitc cp bp zp grow earned

end YM.Integration.WilsonPositionProgramReceivedOccupiedCaps
end
