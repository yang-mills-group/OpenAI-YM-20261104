import YM.Integration.WilsonOriginalThermometerSchoolIntake
import YM.Integration.WilsonOriginalReceivedPost
import YM.Integration.WilsonOriginalFiledSuccessStory
import YM.Integration.WilsonOriginalCoveredTrail
import YM.Integration.WilsonOriginalThermometerTopGrading

/-! Copy the actual bare thermometer rows before the first contraction. Each physical
column keeps its numerical cutoff fit, angular grade, marked slot and translated path. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredPupil
open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor 
open WilsonPositionThermometerCapStation WilsonOriginalStarSceneWords WilsonOriginalThermometerPalette
open WilsonOriginalThermometerTopDensity FVA1Physical.TwoReset Stationary
open Further.PhysicalPeriodLimitF933
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6) {m per k i:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m (i+1) per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (chamber:VowsR.Chamber scroll R.kit D Q books) (hi:m ≤ i)
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ (i+1)) (R.family.path.levels.clock.forcedAllowance (i+1)))
  (school:Syl.School k) (w:Fin 3→ℝ)
  (o:Positions (Fin 3) (R.family.side (i+1) per))
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=i+1) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=i+1) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
local notation "M₀" => primitive R A (i+1) per o.origin σ₀
local notation "S₀" => WilsonThermometerCourseHearing.sectors
local notation "P₀" => Ψ (i+1)
local notation "J₀" => Stock.census (Fin 3)
local notation "E₀" => Passport.point o.origin
local notation "Ω₀" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead school.order school.horizon
local notation "head" => WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self i) o

local notation "tape₀" => AllOrder.Floe.Step.tape (Burn.horizon k+2)
local notation "teach" P:max => Oak.student (n:=per) R hk D Q π Γ books hi (P).op (P).lesson ahead disks
  (P).model school.order (P).voter

/-- The first cover calculation uses the physical primitive at the submitted
cutoff vectors on all copies, before an output voter is read. -/
def bare (x : Wallet disks) : WilsonOriginalCopiedHistory.Values G (J₀) (R.family.side i per) :=
  WilsonOriginalCopiedHistory.block R (Nat.lt_succ_self i) school.order
    (fun _ mult => copyColor mult (M₀) levels (fun h=>((M₀) h).paint x) (π (i+1)) tape₀)

include history scroll chamber warm top cal hospital in
theorem original {τ c:ℝ} (pos:0 < τ) (bounded:τ ≤ 1) (unit:c ≤ 1) (afford:c ≤ (Ω₀)⁻¹) 
    (shape:op.count=school.pieces) (stock:Scene.Armada M₀ w levels σ₀ c school.order op.count school.horizon)
    (voter:Cruise.Voter M₀ σ₀ school.order op.count op.stage k (R.alloy.B.a.clock.J i))
    (test:Tableau S₀ disks M₀) (width:Sycamore.Boot.need 0 school ≤ R.alloy.B.a.clock.J (i+1))
    (refs:∀ j,R.family.ref (levels j) ≤ (i+1)) :
    ∃ P:WilsonOriginalReceivedChain.Post (N:=i+1) R hk D Q π Γ Ψ books ahead disks S₀ levels
      school.order school.horizon school.pieces i hi (head),
       P.w=w ∧ P.rent=τ ∧ P.cost=c ∧ P.passport=E₀ ∧
       Countable P.inputIndex ∧ P.inputIndex=Empty ∧ P.op=op ∧ P.lesson=lesson ∧
       P.modelIndex=Entry R levels ∧ HEq P.model (M₀) ∧ HEq P.voter voter ∧
       ∀ (x : Wallet disks) (grid : Side) (mult : (R.family.side i per).val∣grid.val)
         (d : ℕ), d ≤ school.order → ∀ a : Stationary.Link G grid,
         bare R A D π (φ:=φ) school o x grid mult d a = peek mult (teach P) levels (π (i+1)) tape₀ x d a := by
  have reserve:school.horizon ≤ R.alloy.B.a.clock.J i:=
    (Nat.le_add_left _ _).trans (school.tall.trans (hk.trans (R.alloy.B.a.fits.mono hi)))
  obtain ⟨Z,⟨zero,forced⟩,law,cover,field⟩:=WilsonOriginalThermometerSchoolIntake.original R simple A hk
    D Q π Γ Ψ history scroll books chamber (hi.trans i.le_succ) warm top school w o unit
    (shape ▸ stock) test width refs
  have reg:=Z.old.loan_monotone zero pos.le
  have budget:=Z.old.loan_monotone (Spill.Foundry.empty_lit (P₀) Z (P₀).p.supportExponent (P₀).p.B (w:=w)) pos.le
  have grant:forcedDivisor R.family (i+1) ≤ 1 := (Graces.glyphBound R.alloy.B.a (i+1)).2
  obtain ⟨J,countable,out,post⟩:=Oak.Buffered.arrive R simple hk D Q π Γ Ψ history scroll books chamber hi i.lt_succ_self
    op lesson cal ahead hospital disks S₀ M₀ Z w levels school.order school.horizon voter τ c
    (shape.trans_le school.sense) reserve stock test WilsonThermometerCourseHearing.fired law cover budget
    (Hard.mono _ forced grant) unit pos bounded
  let L:WilsonOriginalReceivedChain.Post (N:=i+1) R hk D Q π Γ Ψ books ahead disks S₀ levels
      school.order school.horizon school.pieces i hi (head) :=
    ⟨op,shape,lesson,E₀,Entry R levels,Empty,J,inferInstance,countable,M₀,Z,out,w,c,τ,
      afford,pos,bounded,voter,stock,test,law,cover,reg,forced,fun x=>funext (field x),post⟩
  refine ⟨L,rfl,rfl,rfl,rfl,(inferInstance : Countable Empty),rfl,rfl,rfl,rfl,HEq.rfl,HEq.rfl,?_⟩
  intro x grid mult d hd a
  let input := fun b : Covers R.family.path.levels.S i grid =>
    copyColor (tiled R mult b) (M₀) levels (fun j=>((M₀) j).paint x) (π (i+1)) tape₀
  have named := WilsonOriginalReceivedCopiedCover.published R hk D Q π Γ Ψ history books hi
    i.lt_succ_self ahead disks S₀ levels school.order school.horizon school.pieces head L
  apply WilsonOriginalCoverCoefficient.identified
  exact WilsonOriginalCopiedContraction.named (R:=R) (h:=i.lt_succ_self) (p:=school.order)
    (M:=(M₀)) (Y:=(teach L)) (published:=named) (t:=x) (grid:=grid) (multiple:=mult)
    (inputs:=input) (matched:=fun _=>rfl) (F:=WilsonOriginalCopiedHistory.forest R i grid)
    (tag:=WilsonOriginalCopiedHistory.tag R i grid) (A:=a) (e:=d) (he:=hd)

end YM.Integration.WilsonThermometerRegisteredPupil
