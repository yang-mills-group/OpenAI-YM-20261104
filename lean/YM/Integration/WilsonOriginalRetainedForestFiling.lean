import YM.Integration.WilsonOriginalRetainedStamp
import YM.Integration.WilsonOriginalRetainedForest
import YM.Integration.WilsonOriginalCoveredStampReturn
/-! All original marked faces on the actual deposited model in the next finite conditional. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalRetainedForestFiling

open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Stationary Comparison.RG02 QuadraticLocal.Rebirth
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933
open scoped Classical BigOperators

open Precision YM.Wilson QuadraticLocal.Sunrise

open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Stationary Comparison.RG02 QuadraticLocal.Rebirth
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933
open scoped Classical BigOperators


variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (hi : m ≤ i) (cut : i < N)
  (op : Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson : Lesson (N:=N) R hk D Q π Γ hi)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V ι : Type} [Fintype V] [DecidableEq V] {marks : Census V} {X : V → Type}
  {passport : Earn.Passport (R.family.side (i+1) per) V}
  (actors : ∀ v, Set (X v)) (M : ι → Row passport marks G (Affinity.Wallet actors))
  (w : V → ℝ) (grades : V → ℕ) (order shelf : ℕ)
  (voter : Mentor.Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)))
    order op.count op.stage k (R.alloy.B.a.clock.J i))

local notation "M₁" => Oak.student (n:=per) R hk D Q π Γ books hi op lesson ahead actors M order voter
local notation "ζ" => Oak.grade0 R hk D Q π Γ hi lesson
local notation "depth" => Burn.horizon k+2
local notation "level" => (show Burn.horizon k+2 ≤ R.alloy.B.a.clock.J i from hk.trans (R.alloy.B.a.fits.mono hi))
local notation "book" => (litP D R.alloy Q level lesson.entry)
local notation "filed" => (book).issue lesson.entry
local notation "zeroFiled" => ((book).sustenance.due lesson.entry).1
local notation "stamped" => Mutation.stamp M₁ (Γ i) ζ depth order
local notation "T₀" => AllOrder.Floe.Step.tape depth
local notation "scale" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)




local notation "powers" => (fun s:Multi.Hot marks=>Launch.index marks grades s.val+1)
local notation "unit" => ((Rebirth.caliber (Γ i) ζ).back depth)
local notation "raw" div:max tester:max => copyColor div stamped grades (fun v=>(stamped v).paint tester) (π i) T₀
local notation "canonical" r:max value:max => WilsonOriginalCoverJetColors.colors (QuadraticLocal.Fk.money (π i) T₀) powers r
  (WilsonOriginalCoverJetColors.reset r value unit)

def Reads (x:Affinity.Wallet actors){grid:Side}(h:(R.family.side i per).val ∣ grid.val)
    (r:ℕ)(value:ℕ → Stationary.Link G grid → Poly marks):Prop :=
  ∀ {side:Side}{st:StepData side grid}{clip:Clip}{data:PathData G}{chart:ChartRatio G}
    (K:Bulk.Kernel st clip data chart)(F:Forest st.ratio)(tag:st.Choices)(z:Exterior.fieldDir G side 1),
      Bulk.Fk K F tag (raw h x) z r=Bulk.Fk K F tag (canonical r value) z r

include course cut in
theorem original (pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (fits:order ≤ Burn.horizon k+1)(narrow:shelf ≤ R.alloy.B.a.clock.J i)
    (cost:ℝ)(issued:Scene.Armada M₁ w grades scale cost order op.count shelf)
    (x:Affinity.Wallet actors){grid:Side}(h:(R.family.side i per).val ∣ grid.val)(r:ℕ)(small:r ≤ order)
    (value:ℕ → Stationary.Link G grid → Poly marks)
    (source:∀a≤r,∀ y,value a y=peek h M₁ grades (π (i+1)) T₀ x a y):
    Reads R hk D Q π Γ books hi op lesson ahead actors M grades order voter x h r value:=by
  intro side st clip data chart K F tag z
  have priced:=(WilsonOriginalMeasuredReentry.credited R hk D Q pass π Γ Ψ course hi cut lesson
    books op ahead month order shelf fits narrow).1
  have bought:=Mutation.allocate M₁ (Γ i) ζ depth order w grades priced issued
  have staff:=Air.license stamped (fun v=>(stamped v).paint x) grades w bought
    (Poetry.Agenda.stem D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)) (fun v=>bought.honor v x)
  have clean:Legal ∅ (π i):=⟨by simp,by simp⟩
  have analytic:=(copy_standard h stamped grades (fun v=>(stamped v).paint x) (π i) ∅ staff clean).1
  apply WilsonOriginalRetainedForest.original K F tag r grades (raw h x) _ (fun _=>rfl) analytic.suppose_mark
  intro s j hj y
  let ray:=(Stationary.arm G grid 1).symm y
  have heard:=WilsonOriginalRetainedStamp.original (R:=R) (course:=course) (cut:=cut) (pass:=pass)
    (month:=month) (fits:=fits) (narrow:=narrow) (issued:=issued) (small:=small) (kept:=hj)
    (s:=s) (z:=ray) (source:=source)
  change (Air.discharge (raw h x) j ((Stationary.arm G grid 1) ray)).part s.val = _ at heard
  rw [show (Stationary.arm G grid 1) ray=y from (Stationary.arm G grid 1).apply_symm_apply y] at heard
  exact heard

end YM.Integration.WilsonOriginalRetainedForestFiling
