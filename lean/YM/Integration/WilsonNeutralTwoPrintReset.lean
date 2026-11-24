import YM.Integration.WilsonOriginalSubmittedAngularFiling
import YM.Integration.WilsonOriginalRestampedSourceIncome
import YM.Integration.WilsonEmittedTransitionJet
import YM.Integration.WilsonThermometerPositionFilmSelf
import YM.Integration.WilsonEmittedRecordedJet

/-! The measured lower stamp and a separately deposited compact row are both
read on their own complete physical torus after the genuine coupling reset. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintReset
open WilsonOriginalReceivedChain WilsonOriginalCopiedHistory
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Stationary Comparison.RG02 Comparison.RG02.Order Further.PhysicalPeriodLimitF933 Laurent
open FVA1Physical.TwoReset
open scoped Classical BigOperators Topology



open WilsonOriginalSubmittedAngularFiling (program)
open WilsonEmittedWordJointFare WilsonEmittedCutGrouping WilsonEmittedRootCensus
open Comparison.Density QuadraticLocal.Sunrise AllOrder.Ker AnalyticBridge.SectorAffine.Offset
open scoped ContDiff
section Row
variable {G:Gauge}{n:Side}{V Y ι:Type}[DecidableEq V]{C:Census V}{p₀:Passport n V}
  (M:ι→Row p₀ C G Y)(x:Y)(grades:V→ℕ){σ:ℝ}{p:ℕ}
  (staff:Air.Staff M (fun i=>(M i).paint x) grades σ p)
  (s:Multi.Hot C)(L:Layout G)(tape:Finset Age)
local notation "f" => WilsonEmittedRootCensus.field M (fun i=>(M i).paint x) (picked M s.val)

include staff L tape in
theorem row (ℓ j:ℕ)(A:Directions G n):
    Assembly.jet (fun z:Chart G n=>z.1^ℓ • f z) j (1,A)=
      if ℓ+(Launch.index C grades s.val+1)≤j then
        (peek dvd_rfl M grades L tape x (j-ℓ-(Launch.index C grades s.val+1))
          (WilsonCubicOriginalTorus.coordinates G n A)).part s.val
      else 0:=by
  have smooth:=WilsonEmittedRecordedJet.analytic M x grades staff L tape s
  rw [WilsonEmittedTransitionJet.original ℓ j f smooth A]
  by_cases lag:ℓ≤j
  · rw [if_pos lag]
    by_cases enough:ℓ+(Launch.index C grades s.val+1)≤j
    · rw [if_pos enough,WilsonThermometerPositionFilmSelf.pupil]
      have add:j-ℓ=Launch.index C grades s.val+1+(j-ℓ-(Launch.index C grades s.val+1)):=by omega
      conv_lhs => rw [add]
      exact WilsonEmittedRecordedJet.original M x grades staff L tape s _ A
    · rw [if_neg enough]
      exact WilsonEmittedRecordedJet.below M x grades staff L tape s _ (by omega) _
  · simp [lag,show ¬ℓ+(Launch.index C grades s.val+1)≤j by omega]
end Row

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



local notation "nextCut" => Nat.lt_trans (Nat.lt_succ_self j) cut
local notation "lowerStudent" => Oak.student (n:=per) R hk D Q π Γ books floor L.op L.lesson ahead actors
  L.model order L.voter
local notation "C₀" => Stock.census V
local notation "date" => R.family.side (j+1) per


variable {ι:Type}(passport:Passport (R.family.side ((j+1)+1) per) V)
  (M:ι→Row passport (Stock.census V) G (Wallet actors))
  (placed:P.passport=passport)(names:P.modelIndex=ι)(same:HEq P.model M)



variable (sized:shelf ≤ R.alloy.B.a.clock.J j)
local notation "dated" => program R cut M grades x π Γ origin depth order
local notation "actualZero" => Oak.grade0 R hk D Q π Γ floor L.lesson
local notation "nextStamp" => Mutation.stamp lowerStudent (Γ j) actualZero depth order


variable {I₂ Y₂:Type}{origin₂:Passport (R.family.side j per) V}
  (Z:I₂→Row origin₂ (Stock.census V) G Y₂)(x₂:Y₂)(w₂:V→ℝ)(grade₂:V→ℕ)
  {σ₂ b₂:ℝ}{p₂ seats₂ shelf₂:ℕ}
  (sold₂:Earn.Scene.Armada Z w₂ grade₂ σ₂ b₂ p₂ seats₂ shelf₂)(pos₂:0<σ₂)
  (s:Multi.Hot (Stock.census V))
local notation "n" => R.family.side j per
local notation "left" => WilsonEmittedRootCensus.field nextStamp (fun i=>(nextStamp i).paint x) (picked nextStamp s.val)
local notation "right" => WilsonEmittedRootCensus.field Z (fun i=>(Z i).paint x₂) (picked Z s.val)

include file course cut pass month fits narrow x placed names same sized sold₂ pos₂ in
theorem original (ℓ₁ ℓ₂ head:ℕ)
    (lev₁:ℓ₁+(Launch.index (Stock.census V) grades s.val+1)=head)
    (lev₂:ℓ₂+(Launch.index (Stock.census V) grade₂ s.val+1)=head)
    (r:ℕ)(through:r≤order)(d:ℕ)(kept:d≤head+r)(A:Directions G n):
    let arg:=WilsonCubicOriginalTorus.coordinates G n A
    let full:=fun z:Chart G n=>z.1^ℓ₁ • left z-z.1^ℓ₂ • right z
    Assembly.jet full d (1,A)=if head≤d then
        Adjacent.born (fun l u=>((dated) n dvd_rfl l u).part s.val)
          ((Rebirth.caliber (Γ j) actualZero).back depth) 0 r (d-head) arg -
        (peek dvd_rfl Z grade₂ (π j) tape₀ x₂ (d-head) arg).part s.val
      else 0:=by
  intro arg full
  have ready:=WilsonOriginalRestampedSourceIncome.original R hk D Q π Γ Ψ books ahead actors pieces grades order
    shelf seats floor earlier L course nextCut pass month fits sized
  have staff₁:=Air.license nextStamp _ grades L.w ready.1 ready.2.1 (fun i=>ready.1.honor i x)
  have staff₂:=Air.license Z _ grade₂ w₂ sold₂ pos₂ (fun i=>sold₂.honor i x₂)
  have sm₁:=WilsonEmittedRecordedJet.analytic nextStamp x grades staff₁ (π j) tape₀ s
  have sm₂:=WilsonEmittedRecordedJet.analytic Z x₂ grade₂ staff₂ (π j) tape₀ s
  let f₁:=fun z:Chart G n=>z.1^ℓ₁ • left z
  let f₂:=fun z:Chart G n=>z.1^ℓ₂ • right z
  have a₁:ContDiffAt ℝ ω f₁ 0:=(contDiffAt_fst.pow _).smul sm₁
  have a₂:ContDiffAt ℝ ω f₂ 0:=(contDiffAt_fst.pow _).smul sm₂
  have sub:Assembly.jet full d (1,A)=Assembly.jet f₁ d (1,A)-Assembly.jet f₂ d (1,A):=by
    unfold Assembly.jet
    change _ • iteratedFDeriv ℝ d (f₁-f₂) 0 _=_
    rw [iteratedFDeriv_sub_apply (a₁.of_le le_top) (a₂.of_le le_top)]
    exact smul_sub ..
  refine sub.trans ((congrArg₂ (fun v w:ℂ=>v-w)
    (row nextStamp x grades staff₁ s (π j) tape₀ ℓ₁ d A)
    (row Z x₂ grade₂ staff₂ s (π j) tape₀ ℓ₂ d A)).trans ?_)
  rw [lev₁,lev₂]
  by_cases active:head≤d
  · simp only [if_pos active]
    rw [Nat.sub_sub,lev₁,Nat.sub_sub,lev₂]
    have issued:=WilsonOriginalSubmittedAngularFiling.original R hk D Q π Γ Ψ books ahead actors pieces
      grades order shelf seats floor physical P L file course cut pass month fits narrow x passport M
      placed names same sized (dvd_refl (R.family.side j per).val) r through
    exact congrArg (fun v=>v-(peek dvd_rfl Z grade₂ (π j) tape₀ x₂ (d-head) arg).part s.val)
      (issued.2.2.2 s (d-head) (by omega) arg)
  · simp [active]

end YM.Integration.WilsonNeutralTwoPrintReset
end
