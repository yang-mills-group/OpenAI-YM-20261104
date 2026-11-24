import YM.Integration.WilsonOriginalAlternativeFiniteSchool
import YM.Integration.WilsonOriginalReceivedPost
import YM.Integration.WilsonOriginalFiledSuccessStory
import YM.Integration.WilsonOriginalThermometerTopGrading

/-! The actual upper post, with its accountable index, marked request and original lesson. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeFinitePost
open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor 
open WilsonPositionThermometerCapStation WilsonOriginalStarSceneWords WilsonOriginalThermometerPalette
open WilsonOriginalThermometerTopDensity
open scoped Classical BigOperators

variable {V:Type} [Fintype V] [DecidableEq V]
variable {G:Gauge} (R:Run G) (simple:G.Simple) (d:V→ℕ) (positive:∀j,0<d j) {m per k i:ℕ}
  (y:∀j,R.family.book.Ref (d j))
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m (i+1) per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (chamber:VowsR.Chamber scroll R.kit D Q books) (hi:m ≤ i)
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ (i+1)) (R.family.path.levels.clock.forcedAllowance (i+1)))
  (school:Syl.School k) (w:V→ℝ)
  (o:Positions (V) (R.family.side (i+1) per))
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=i+1) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=i+1) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
local notation "M₀" => WilsonOriginalAlternativeFiniteSource.words R d positive (i+1) per y o.origin σ₀
local notation "S₀" => (WilsonOriginalAlternativeFiniteSource.sectors (V:=V))
local notation "P₀" => Ψ (i+1)
local notation "J₀" => Stock.census (V)
local notation "E₀" => Passport.point o.origin
local notation "Ω₀" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead school.order school.horizon
local notation "head" => WilsonOriginalAlternativeFiniteSource.offer R d (i+1) per y o.origin

include simple history scroll chamber warm top cal hospital in
theorem counted {τ c:ℝ} (pos:0 < τ) (bounded:τ ≤ 1) (unit:c ≤ 1) (afford:c ≤ (Ω₀)⁻¹) 
    (shape:op.count=school.pieces) (stock:Scene.Armada M₀ w d σ₀ c school.order op.count school.horizon)
    (voter:Cruise.Voter M₀ σ₀ school.order op.count op.stage k (R.alloy.B.a.clock.J i))
    (test:Tableau S₀ WilsonOriginalAlternativeFiniteSource.disks M₀) (width:Sycamore.Boot.need 0 school ≤ R.alloy.B.a.clock.J (i+1))
    (refs:∀ j,R.family.ref (d j) ≤ (i+1)) :
    ∃ P:WilsonOriginalReceivedChain.Post (N:=i+1) R hk D Q π Γ Ψ books ahead WilsonOriginalAlternativeFiniteSource.disks S₀ d
      school.order school.horizon school.pieces i hi (head),
       P.w=w ∧ P.rent=τ ∧ P.cost=c ∧ P.passport=E₀ ∧
       Countable P.inputIndex ∧ P.inputIndex=Empty ∧ P.op=op ∧ P.lesson=lesson := by
  have reserve:school.horizon ≤ R.alloy.B.a.clock.J i:=
    (Nat.le_add_left _ _).trans (school.tall.trans (hk.trans (R.alloy.B.a.fits.mono hi)))
  obtain ⟨Z,⟨zero,forced⟩,law,cover,field⟩:=WilsonOriginalAlternativeFiniteSchool.original R d positive y hk
    D Q π Γ Ψ history scroll books chamber (hi.trans i.le_succ) warm top school w o unit
    (shape ▸ stock) test width refs
  have reg:=Z.old.loan_monotone zero pos.le
  have budget:=Z.old.loan_monotone (Spill.Foundry.empty_lit (P₀) Z (P₀).p.supportExponent (P₀).p.B (w:=w)) pos.le
  have grant:forcedDivisor R.family (i+1) ≤ 1 := (Graces.glyphBound R.alloy.B.a (i+1)).2
  obtain ⟨J,countable,out,post⟩:=Oak.Buffered.arrive R simple hk D Q π Γ Ψ history scroll books chamber hi i.lt_succ_self
    op lesson cal ahead hospital WilsonOriginalAlternativeFiniteSource.disks S₀ M₀ Z w d school.order school.horizon voter τ c
    (shape.trans_le school.sense) reserve stock test (WilsonOriginalAlternativeFiniteSource.fired (V:=V)) law cover budget
    (Hard.mono _ forced grant) unit pos bounded
  let L:WilsonOriginalReceivedChain.Post (N:=i+1) R hk D Q π Γ Ψ books ahead WilsonOriginalAlternativeFiniteSource.disks S₀ d
      school.order school.horizon school.pieces i hi (head) :=
    ⟨op,shape,lesson,E₀,Entry R d,Empty,J,inferInstance,countable,M₀,Z,out,w,c,τ,
      afford,pos,bounded,voter,stock,test,law,cover,reg,forced,fun x=>funext (field x),post⟩
  exact ⟨L,rfl,rfl,rfl,rfl,(inferInstance : Countable Empty),rfl,rfl,rfl⟩

end YM.Integration.WilsonOriginalAlternativeFinitePost
