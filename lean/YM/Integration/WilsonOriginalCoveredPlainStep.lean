import YM.Integration.WilsonOriginalCoveredStampReturn
import YM.Integration.WilsonOriginalCoveredJoinWick
import YM.Integration.WilsonMixedPassportVote

/-! The whole next Wilson contraction on an independently reconstructed original deposited input. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCoveredPlainStep
open Precision YM.Wilson QuadraticLocal.Sunrise

open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Stationary Comparison.RG02 QuadraticLocal.Rebirth
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933
open scoped Classical BigOperators


private theorem plain {V : Type} [Fintype V] [DecidableEq V] {W : Census V} {G : Gauge} {f : Side}
    (costs : V → ℕ) (X Y : Bulk.Colors W G f)
    (power : ∀ a, X.power a = Launch.index W costs a.val+1) :
    WilsonOriginalJoinedCopyBank.joined Finset.univ ∅ costs X Y = X := by
  cases X with
  | mk vac mark powers =>
    change ∀ a, powers a = _ at power
    have paid := funext power
    subst powers
    unfold WilsonOriginalJoinedCopyBank.joined
    congr 1
    funext a
    have off : ¬a.val.val ⊆ (∅ : Finset V) := by
      obtain ⟨z,hz⟩ := a.property
      exact fun h => Finset.notMem_empty z (h hz)
    simp [off]

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

    (z : Exterior.fieldDir G side 1) :
    Bulk.Fk kernel forest tag (raw multiple x) z order =
      Bulk.Fk kernel forest tag (canonical value) z order := by
  have full := WilsonOriginalCoveredStampReturn.finite (R:=R) (hk:=hk) (course:=course) (hi:=hi) (cut:=cut)
    (lesson:=lesson) (books:=books) (op:=op) (ahead:=ahead) (pass:=pass) (month:=month)
    (fits:=fits) (narrow:=narrow) (cost:=cost) (issued:=issued) (x:=x) (multiple:=multiple)
    (value:=value) (declared:=declared) (kernel:=kernel) (forest:=forest) (tag:=tag)
    (left:=Finset.univ) (newSites:=∅) (apart:=Finset.disjoint_empty_right _) (newGrades:=grades)
    (fresh:=raw multiple x) (z:=z)
  have hg : WilsonMixedPassportVote.choice (Finset.univ : Finset V) grades grades = grades := by
    funext s
    simp [WilsonMixedPassportVote.choice]
  dsimp only at full
  rw [hg] at full
  rw [plain grades (raw multiple x) (raw multiple x) (fun s => rfl),
      plain grades (canonical value) (raw multiple x) (fun s => rfl)] at full
  exact full

end YM.Integration.WilsonOriginalCoveredPlainStep
