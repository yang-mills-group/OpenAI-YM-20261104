import YM.Integration.WilsonOriginalFiledSuccessStory
import YM.Integration.WilsonPhysicalMarkedDefectSource
import YM.Integration.WilsonOriginalReceivedPost

/-! Apply one genuine nonbare measured block to an independently enrolled
analytic teacher, with its own radii. Its incoming occupied residual is empty
and all its quiet hard addresses have their original weights on every field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredModelRun
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
local notation "physical" => fun t U=>((H).eval U:ℂ) • Poly.pass ((lamp).log t U)
local notation "teacher" => Oak.student (n:=per) R hk D Q π Γ books hi op lesson ahead A M order voter

open WilsonPhysicalMarkedDefect

private theorem pure_value {n:Side} {V ι X:Type} [Fintype V] [DecidableEq V] {P:Rep G n}
    {A:Passport n V} {Γ:Census V} (M:ι→Row A Γ G X) {w:V→ℝ} {k:ℝ}
    (h:Hard.Rent P.activities.forced P.activities.K P.p P.p.supportExponent k)
    (hw:∀j,0<w j) (x:X) (U:Config G n) :
    (Tint.Patrol.picture M (modelInput A P Γ X h)).density x U =
      (P.eval U:ℂ) • Poly.pass ((rendered M P.p (Coat.gStep P.beta)).log x U) := by
  let S:=modelInput A P Γ X h
  let L:=rendered M P.p (Coat.gStep P.beta)
  let e:=Equiv.sumEmpty ι Empty
  have hs:((Tint.Patrol.picture M S).E.log x U)=L.log x U := by
    change (∑' j:ι⊕Empty,(L.join S.old).frame j x U) = ∑' j,L.frame j x U
    convert (e.tsum_eq (fun j=>L.frame j x U)) using 1
    apply tsum_congr
    intro j
    cases j with
    | inl a => rfl
    | inr b => exact b.elim
  have gas:=model_input_gas (A:=A) (Γ:=Γ) h hw x U
  rw [Gallery.density,hs]
  change (Real.exp (P.exponent U):ℂ) • (Poly.pass (L.log x U)*
    (∑' j,QuadraticLocal.Fusion.Attached.packet P.activities P.p (S.hard.hard x) U j))=_
  rw [gas,mul_comm (Poly.pass _),Poly.product_bead,smul_smul,Rep.eval,Complex.ofReal_mul]

include simple course cut hospital cal chamber in
theorem original (count:op.count≤Burn.horizon k+2) (level:shelf≤R.alloy.B.a.clock.J i)
    {b τ:ℝ} (stock:Scene.Armada M w grades scale b order op.count shelf)
    (table:Tableau K A M) (x₀:Wallet A)
    (unit:b≤1) (afford:b≤(Ω)⁻¹) (positive:0<τ) (cap:τ≤1) :
    ∃ P:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead A K grades
        order shelf op.count i hi (physical),
      P.w=w ∧ P.rent=τ ∧ P.cost=b ∧ P.passport=passport ∧ P.inputIndex=Empty ∧ P.op=op ∧ P.lesson=lesson ∧
      ∀ t U,(rendered (Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead A
        P.model order P.voter) (Ψ i).p oldG).log t U = (rendered teacher (Ψ i).p oldG).log t U := by
  have live:=(later R π Γ Ψ course (hi.trans i.le_succ) cut).truep.valid.labels
  let hard:=Hard.rentValid live.forced live.boundK
  let Z:=modelInput passport H marks (Wallet A) hard
  have plain := (model_input_prices (A:=passport) (Γ:=marks) (X:=Wallet A) hard w).2
  have zero:Z.old.Paid w (H).p.B ((H).p.supportExponent+1+1) 0:=
    Spill.Foundry.empty_lit (H) Z _ _
  obtain ⟨law,cover⟩:= model_input_addresses (A:=passport) (Γ:=marks) A K hard
  have reg:=Z.old.loan_monotone zero positive.le
  have budget:=Z.old.loan_monotone (Spill.Foundry.empty_lit (H) Z (H).p.supportExponent (H).p.B (w:=w)) positive.le
  have sqrtCap:=Graces.glyphBound R.alloy.B.a (i+1)
  have hallow:=Extra.Histories.forcedPos R.family.path.levels (i+1)
  have sq:=Real.sq_sqrt hallow.le
  have divide:R.alloy.B.a.clock.forcedAllowance (i+1)≤forcedDivisor R.family (i+1):=by
    change R.family.path.levels.clock.forcedAllowance (i+1) ≤ Real.sqrt (R.family.path.levels.clock.forcedAllowance (i+1))
    have radius:0 ≤ Real.sqrt (R.family.path.levels.clock.forcedAllowance (i+1)):=sqrtCap.1.le
    have small:Real.sqrt (R.family.path.levels.clock.forcedAllowance (i+1))≤1:=sqrtCap.2
    nlinarith [mul_nonneg radius (sub_nonneg.mpr small)]
  have forced:Z.hard.Paid w (H).p.B (H).p.supportExponent (forcedDivisor R.family (i+1)):=
    Z.hard.mono plain divide
  obtain ⟨J,cd,out,posted⟩:=Oak.Buffered.arrive R simple hk D Q π Γ Ψ course scroll books chamber hi cut
    op lesson cal ahead hospital A K M Z w grades order shelf voter τ b count level stock table x₀ law
    cover budget (Z.hard.mono forced sqrtCap.2) unit positive cap
  let L:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead A K grades order shelf
      op.count i hi (physical) :=
    ⟨op,rfl,lesson,passport,ι,Empty,J,inferInstance,cd,M,Z,out,w,b,τ,afford,positive,cap,voter,stock,
      table,law,cover,reg,forced,fun t=>funext (pure_value M hard stock.positive t),posted⟩
  exact ⟨L,rfl,rfl,rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩

end YM.Integration.WilsonMeasuredModelRun
end

