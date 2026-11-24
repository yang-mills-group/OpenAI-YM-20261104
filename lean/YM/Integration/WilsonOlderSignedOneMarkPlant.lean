import YM.Integration.WilsonOlderSignedOneMarkStep
import YM.Integration.WilsonOlderSignedOneMarkMasks
import YM.Integration.WilsonReceivedSourceGross


/-! The full singleton residual of an original post relative to its unmasked
integral marked log. The rejected parts of each physical lamp stay attached
to the original quiet hard gas and are paid at their true supports. -/

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderSignedOneMarkPlant
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m ≤ i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) {V : Type} [Fintype V] [DecidableEq V]
  {X : V → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical)

local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "lamps" => (rendered student (Ψ i).p oldG)
local notation "gauge" => (Tint.Patrol.report student P.output oldG)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "width" => ((Ψ i).p.supportExponent+1+1)

local notation "weights" => Stoop.radius P.w (Ω^6)
local notation "homes" => (P.passport.coarser (sheet).ratio).origin
local notation "debt" => (⟨P.output.old,P.output.hard⟩ :
  Gallery (Wallet actors) P.outputIndex homes (Ψ i) (Stock.census V))
local notation "βhat" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "gf" => Coat.gStep (R.family.path.rep N per (i+1)).beta

include course cut in
theorem original (way : WayStation R.kit) (simple : G.Simple)
    (late : WilsonCenteredCaptureClock.first R simple ≤ i) (p q : ℕ)
    (ready : q ≤ R.alloy.B.a.clock.J i) (deep : 2*(p+1)+8 ≤ order)
    (aged : p+4 ≤ 3*k+2) {ε : ℝ} (ep : 0<ε)
    (opened : WilsonFirstReceivedEarnedFee.opening R simple P.op.count p order k deep aged ep ≤ i)
    (x : Wallet actors) (v : V) (Z : Support (R.family.side i per)) (y : Site (R.family.side i per))
    (center : y∈Z) (member : homes v∈Z) (rad : ℕ) (near : separation (homes v) y≤rad)
    {d : ℕ} {F : Labels.Frame G d} (S : SectionData F) (Y : Hol G) {μ : ℝ}
    (reader : Readable Y S (Ψ i).p (R.family.side i per) μ) :
    let s := (Stock.census V).fire v
    let toll := WilsonOlderSignedSingletonFare.fare (Ψ i).p S Y weights s 1 Z rad
      ((Ω^6)⁻¹*((8*Ω^P.op.count)*P.rent+ε*gf^p)) (βhat^(-(q:ℝ))*κ) κ
      (R.alloy.B.a.clock.forcedAllowance i) μ
    let stages := AllOrder.Floe.Step.tape (Burn.horizon k+2)
    let gross := (Spill.allOver (Ψ i).p)^(order+shelf+1)*Ω
    let maskCost := WilsonOlderSignedOneMarkMasks.fare (Ψ i).p Z (R.alloy.B.a.clock.forcedAllowance i)
      (Poly.toll P.w s) gross κ
    ∃ A : Coefficient F (R.family.side i per), A.Format y Y (Ψ i) ∧
      A.remBound y (Ψ i) κ (toll+maskCost) ∧ ∀ U, A.density y S (Ψ i) U =
        (LocalComparison.actualPush R.family N per i (physical x) U).part s -
        ((Ψ i).eval U:ℂ)*(Integral.markedLog gf U (Air.craft student (fun b=>(student b).paint x)
          grades (π i) stages)).part s := by
  intro s toll stages gross maskCost
  obtain ⟨A,format,fee,valA⟩:=WilsonOlderSignedOneMarkStep.original R hk D Q π Γ Ψ course books hi cut
    ahead actors pieces grades order shelf seats physical P way simple late p q ready deep aged ep opened x v
    Z y center member rad near S Y reader
  letI : Countable P.modelIndex:=P.modelCount
  letI students : Countable (Scene.Texts P.model
    (Pane.panel R.alloy i (R.alloy.B.a.S.oneStep i per).exact_size).ratio
    (Cruise.publish D R.rolls Q R.alloy φ books P.op (Oak.era R hk D Q π Γ hi P.op P.lesson)
      (R.alloy.B.a.S.oneStep i per).exact_size P.model order P.voter P.lesson.entry)) := Scene.crewC P.model
    (Pane.panel R.alloy i (R.alloy.B.a.S.oneStep i per).exact_size).ratio
    (Cruise.publish D R.rolls Q R.alloy φ books P.op (Oak.era R hk D Q π Γ hi P.op P.lesson)
      (R.alloy.B.a.S.oneStep i per).exact_size P.model order P.voter P.lesson.entry)
    (Cruise.funded D R.rolls Q R.alloy φ books P.op (Oak.era R hk D Q π Γ hi P.op P.lesson)
      (R.alloy.B.a.S.oneStep i per).exact_size P.model order P.voter P.lesson.entry P.lesson.studied ahead)
  have actual:=(course.1.walk i hi cut.le).truep
  obtain ⟨K⟩:=WilsonCenteredCourseKeeper.original R course i hi cut
  obtain ⟨div,pos,room⟩:=(eventually_atTop.mp (WilsonCenteredCaptureClock.original R simple)).choose_spec i late
  rw [←actual.point] at room
  have unweighted:=WilsonReceivedSourceGross.landed R hk D Q π Γ Ψ books hi ahead actors pieces grades
    order shelf seats physical P
  have gross' : WilsonRootedKioskOccupiedSlip.Gross lamps P.w (Ψ i).p.B ((Ψ i).p.supportExponent+2) gross:=by
    dsimp only [gross]
    simpa only [add_assoc,one_add_one_eq_two] using unweighted
  have gaps:=@WilsonOlderSignedOneMarkMasks.original G (R.family.side i per) V (Wallet actors) _ _
    students (Stock.census V) homes (Ψ i) d F lamps s v (mem_singleton_self _) P.w P.issued.earning.positive
    gross gross' x Z y center member K (R.alloy.B.a.clock.forcedAllowance i) κ div pos room
    actual.valid.labels.boundK actual.valid.labels.forced S Y
  let trueDiff := fun U => (LocalComparison.actualPush R.family N per i (physical x) U).part s -
    ((Ψ i).eval U:ℂ)*((lamps).log x U).part s
  have stored : WilsonCenteredFiledAtoms.Store (Ψ i) S Y y κ toll trueDiff:=⟨A,format,fee,valA⟩
  obtain ⟨B,laws,priceB,present⟩:=WilsonCenteredFiledAtoms.add actual.valid div stored gaps
  refine ⟨B,laws,priceB,fun U=>?_⟩
  have nominal : WilsonRootedKioskOccupiedSlip.bare lamps x U =
      Integral.markedLog gf U (Air.craft student (fun b=>(student b).paint x) grades (π i) stages) := by
    have hp : 0 < (R.family.path.rep N per (i+1)).beta := Overlay.beta_positive R.makes.wilson cut
    have gp : 0 < gf := inv_pos.mpr (Real.sqrt_pos.mpr hp)
    let inks := fun b=>(student b).paint x
    have issued:=Air.license student inks grades P.w P.issued.earning (Poetry.Agenda.stem ..)
      (fun b=>P.issued.earning.honor b x)
    have reading:=Air.liftPassport student inks grades issued (π i) stages gf gp.ne' U
    refine Eq.trans ?_ reading.tsum_eq
    unfold WilsonRootedKioskOccupiedSlip.bare
    apply tsum_congr
    intro b
    have shift := (course.1.walk (i+1) (Nat.le_succ_of_le hi) cut).beta
    simp only [rendered,Air.grainR,Row.nominal,inks,shift]
    rfl
  refine (present U).trans ?_
  change trueDiff U+((Ψ i).eval U:ℂ)*(((lamps).log x U).part s-
    (WilsonRootedKioskOccupiedSlip.bare lamps x U).part s)=_
  dsimp only [trueDiff]
  rw [nominal]
  ring

end YM.Integration.WilsonOlderSignedOneMarkPlant
