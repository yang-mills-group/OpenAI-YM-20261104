import YM.Integration.WilsonOriginalCoveredStamp
import YM.Integration.WilsonOriginalCoveredJoinWick
import YM.Integration.WilsonMixedPassportVote

/-! The whole next Wilson contraction on an independently reconstructed original deposited input. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCoveredStampReturn
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



local notation "powers" => (fun s : Multi.Hot marks => Launch.index marks grades s.val+1)
local notation "unit" => ((Rebirth.caliber filed zeroFiled).back depth)
local notation "raw" div:max tester:max => copyColor div stamped grades (fun v=>(stamped v).paint tester) (π i) T₀
local notation "canonical" data:max => WilsonOriginalCoverJetColors.colors (QuadraticLocal.Fk.money (π i) T₀)
  powers order (WilsonOriginalCoverJetColors.reset order data unit)

include course cut in
theorem finite (pass : Pass D Q R.alloy R.kit) (month : Scholar.Month R.rolls D Q R.alloy.delay)
    (fits : order ≤ Burn.horizon k+1) (narrow : shelf ≤ R.alloy.B.a.clock.J i)
    (cost : ℝ) (issued : Scene.Armada M₁ w grades scale cost order op.count shelf)
    (x : Affinity.Wallet actors) {grid : Side} (multiple : (R.family.side i per).val ∣ grid.val)
    (value : ℕ → Stationary.Link G grid → Poly marks)
    (declared : ∀ d≤order, ∀ a, value d a = peek multiple M₁ grades (π i) T₀ x d a)
    {side : Side} {step : StepData side grid} {clip : Clip} {path : PathData G} {chart : ChartRatio G}
    (kernel : Bulk.Kernel step clip path chart) (forest : Forest step.ratio) (tag : step.Choices)
    (left newSites : Finset V) (apart : Disjoint left newSites) (newGrades : V → ℕ)
    (fresh : Bulk.Colors marks G grid) (z : Exterior.fieldDir G side 1) :
    let mix := WilsonMixedPassportVote.choice left grades newGrades
    let join := WilsonOriginalJoinedCopyBank.joined left newSites mix
    Bulk.Fk kernel forest tag (join (raw multiple x) fresh) z order =
      Bulk.Fk kernel forest tag (join (canonical value) fresh) z order := by
  intro mix join
  have priced := (WilsonOriginalMeasuredReentry.credited R hk D Q pass π Γ Ψ course hi cut lesson
    books op ahead month order shelf fits narrow).1
  have bought := Mutation.allocate M₁ (Γ i) ζ depth order w grades priced issued
  have staff := Air.license stamped (fun v => ((stamped) v).paint x) grades w bought
    (Poetry.Agenda.stem D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)) (fun v=>bought.honor v x)
  have emptyLegal : Legal ∅ (π i) := ⟨by simp, by simp⟩
  have analytic := (copy_standard multiple stamped grades (fun v=>(stamped v).paint x)
    (π i) ∅ staff emptyLegal).1
  apply WilsonOriginalCoveredJoinWick.finite kernel forest tag order left newSites apart mix (raw multiple x)
    fresh (QuadraticLocal.Fk.money (π i) T₀) powers (WilsonOriginalCoverJetColors.reset order value unit) rfl rfl _ _ _ z
  · intro s active
    apply congrArg (fun n : ℕ => n+1)
    apply Finset.sum_congr rfl
    intro v hv
    exact if_pos (active hv)
  · exact analytic.suppose_mark
  · intro s j hj y
    exact WilsonOriginalCoveredStamp.occupied (R:=R) (hk:=hk) (course:=course) (hi:=hi) (cut:=cut)
      (lesson:=lesson) (books:=books) (op:=op) (ahead:=ahead) (pass:=pass) (month:=month)
      (fits:=fits) (narrow:=narrow) (cost:=cost) (issued:=issued) (x:=x) (multiple:=multiple)
      (value:=value) (declared:=declared) (z:=y) (j:=j) (hj:=hj) (s:=s)

end YM.Integration.WilsonOriginalCoveredStampReturn
