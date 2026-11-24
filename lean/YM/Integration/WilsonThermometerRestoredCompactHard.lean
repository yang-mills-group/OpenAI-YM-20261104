import YM.Integration.WilsonOriginalCollaredMarkedSheet
import YM.Integration.WilsonMeasuredModelRun

/-! The genuine nonbare counted post carrying the full unmasked nominal on its actual hard stock. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerRestoredCompactHard
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Push.AbsoluteSums Stationary Comparison.RG02 QuadraticLocal.Rebirth
open VowsR LocalComparison ConnectedActivityE6
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple) {m i N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀ j, RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ → ℕ} (scroll:LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (hi:m ≤ i) (cut:i < N)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=N) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (chamber:VowsR.Chamber scroll R.kit D Q books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
  {V ι:Type} [Fintype V] [DecidableEq V] [Countable ι] {X:V → Type}
  [∀ v,AddCommGroup (X v)] [∀ v,Module ℝ (X v)]
  (passport:Earn.Passport (R.family.side (i+1) per) V)
  (A:∀v, Set (X v)) (K:∀v, Submodule ℝ (X v))
  (M:ι → Row passport (Stock.census V) G (Wallet A)) (w:V → ℝ) (grades:V → ℕ) (order shelf:ℕ)
  (voter:Mentor.Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)))
    order op.count op.stage k (R.alloy.B.a.clock.J i))

local notation "marks" => Stock.census V
local notation "H" => Ψ (i+1)
local notation "scale" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "oldG" => Coat.gStep (H).beta
local notation "newG" => Coat.gStep (Ψ i).beta
local notation "sheet" => R.family.path.levels.clock.op i per
local notation "lamp" => rendered M (H).p oldG
local notation "physical" => fun t U=>((H).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut M oldG t U)
local notation "teacher" => Oak.student (n:=per) R hk D Q π Γ books hi op lesson ahead A M order voter

open WilsonRootedKioskOccupiedSlip


private theorem presented {n:Side} {V ι T:Type} [Fintype V] [DecidableEq V] {P:Rep G n}
    {o:Passport n V} {C:Census V} (M:ι→Row o C G T)
    (F:Hard T P.p P.activities.forced P.activities.K o.origin C) (t:T) (U:Config G n) :
    let Z:Tint.Incoming o P T Empty C:=⟨Spill.Foundry.noneL P o.origin,F⟩
    let L:=rendered M P.p (Coat.gStep P.beta)
    (Tint.Patrol.picture M Z).density t U=(⟨L,F⟩:Gallery T ι o.origin P C).density t U := by
  intro Z L
  have hs:(Tint.Patrol.picture M Z).E.log t U=L.log t U:=by
    change (∑'j:ι⊕Empty,(L.join Z.old).frame j t U)=∑'j,L.frame j t U
    convert (Equiv.sumEmpty ι Empty).tsum_eq (fun j=>L.frame j t U) using 1
    apply tsum_congr
    intro j
    cases j with
    | inl a=>rfl
    | inr b=>exact b.elim
  unfold Gallery.density
  rw [hs]
  rfl

include simple course cut hospital cal chamber voter in
theorem original (count:op.count ≤ Burn.horizon k+2) (level:shelf ≤ R.alloy.B.a.clock.J i)
    {b τ bill shrink:ℝ} {initial:V→ℝ}
    (stock:Scene.Armada M w grades scale b order op.count shelf) (table:Tableau K A M)
    (x₀:Wallet A) (unit:b ≤ 1) (afford:b ≤ (Ω)⁻¹) (positive:0<τ) (cap:τ ≤ 1)
    (top:Topline (H) (R.family.path.levels.clock.forcedAllowance (i+1)))
    (named:∀v,0 < initial v) (one:1 ≤ shrink) (wallet:w=fun v=>initial v/shrink)
    (earned:Gross (lamp) initial (H).p.B ((H).p.supportExponent+1) bill)
    (enough:shrink⁻¹*bill ≤ Willow.haloSlack (H).p.B) :
    ∃ P:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead A K grades
        order shelf op.count i hi (physical),
      P.w=w ∧ P.rent=τ ∧ P.cost=b ∧ P.passport=passport ∧ P.inputIndex=Empty ∧
      P.op=op ∧ P.lesson=lesson ∧ P.modelIndex=ι ∧ HEq P.model M ∧
      P.input.hard.Paid P.w (H).p.B (H).p.supportExponent (R.family.path.levels.clock.forcedAllowance (i+1)) := by
  obtain ⟨F,enrolled,plain,held⟩:=WilsonOriginalCollaredMarkedSheet.original A K passport.support
    (H) (lamp) (table.line (H).p oldG) top named one earned enough
  rw [←wallet] at plain
  let Z:Tint.Incoming passport (H) (Wallet A) Empty marks:=⟨Spill.Foundry.noneL (H) passport.origin,F⟩
  have law:Taut passport.support A K Z.old:=⟨fun i=>i.elim,fun i=>i.elim⟩
  have cover:Crown passport.support A K Z.hard:=enrolled
  have zero:Z.old.Paid w (H).p.B ((H).p.supportExponent+1+1) 0:=
    Spill.Foundry.empty_lit (H) Z _ _
  have reg:=Z.old.loan_monotone zero positive.le
  have budget:=Z.old.loan_monotone (Spill.Foundry.empty_lit (H) Z (H).p.supportExponent (H).p.B (w:=w)) positive.le
  have sqrtCap:=Graces.glyphBound R.alloy.B.a (i+1)
  have hallow:=Extra.Histories.forcedPos R.family.path.levels (i+1)
  have sq:=Real.sq_sqrt hallow.le
  have divide:R.alloy.B.a.clock.forcedAllowance (i+1) ≤ forcedDivisor R.family (i+1):=by
    change R.family.path.levels.clock.forcedAllowance (i+1) ≤ Real.sqrt (R.family.path.levels.clock.forcedAllowance (i+1))
    have radius:0 ≤ Real.sqrt (R.family.path.levels.clock.forcedAllowance (i+1)):=sqrtCap.1.le
    have small:Real.sqrt (R.family.path.levels.clock.forcedAllowance (i+1)) ≤ 1:=sqrtCap.2
    nlinarith [mul_nonneg radius (sub_nonneg.mpr small)]
  have forced:Z.hard.Paid w (H).p.B (H).p.supportExponent (forcedDivisor R.family (i+1)):=
    Z.hard.mono plain divide
  obtain ⟨J,cd,out,posted⟩:=Oak.Buffered.arrive R simple hk D Q π Γ Ψ course scroll books chamber hi cut
    op lesson cal ahead hospital A K M Z w grades order shelf voter τ b count level stock table x₀ law
    cover budget (Z.hard.mono forced sqrtCap.2) unit positive cap
  have whole (t:Wallet A) (U:Config G (R.family.side (i+1) per)) :
      (Tint.Patrol.picture M Z).density t U=(physical) t U:=
    (presented M F t U).trans (held t U)
  let P:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead A K grades order shelf
      op.count i hi (physical):=
    ⟨op,rfl,lesson,passport,ι,Empty,J,inferInstance,cd,M,Z,out,w,b,τ,afford,positive,cap,voter,
      stock,table,law,cover,reg,forced,fun t=>funext (whole t),posted⟩
  exact ⟨P,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,HEq.rfl,plain⟩

end YM.Integration.WilsonThermometerRestoredCompactHard
