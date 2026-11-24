import YM.Integration.WilsonOriginalMeasuredStampCoefficients
import YM.Integration.FVA1Physical.TwoReset.ResetCopies

/-! The measured adjacent coupling acts on every copied occupied jet of the actual deposited writer. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMeasuredCopiedReset

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


include course cut in
theorem original (pass : Pass D Q R.alloy R.kit) (month : Scholar.Month R.rolls D Q R.alloy.delay)
    (fits : order ≤ Burn.horizon k+1) (narrow : shelf ≤ R.alloy.B.a.clock.J i)
    (cost : ℝ) (issued : Scene.Armada M₁ w grades scale cost order op.count shelf)
    (x : Affinity.Wallet actors) {grid : Side} (multiple : (R.family.side i per).val ∣ grid.val)
    (A : Stationary.Link G grid) (e : ℕ) (he : e ≤ order) (s : marks.Mode) :
    (peek multiple stamped grades (π i) T₀ x e A).part s =
      Adjacent.born (fun d a => (peek multiple M₁ grades (π i) T₀ x d a).part s)
        ((Rebirth.caliber filed zeroFiled).back depth) 0 order e A := by
  have priced := (WilsonOriginalMeasuredReentry.credited R hk D Q pass π Γ Ψ course hi cut lesson
    books op ahead month order shelf fits narrow).1
  have bought := Mutation.allocate M₁ (Γ i) ζ depth order w grades priced issued
  have stem := Poetry.Agenda.stem D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)
  have h₁ := Air.license M₁ (fun v => ((M₁) v).paint x) grades w issued stem (fun v => issued.honor v x)
  have h₂ := Air.license stamped (fun v => ((stamped) v).paint x) grades w bought stem (fun v => bought.honor v x)
  let lags := Finset.Icc (-(shelf+1:ℤ)) (order:ℤ)
  have inLags (v) : ((M₁) v).lamp.lag ∈ lags := by
    have deg := Scene.Armada.degreeR grades issued.toMinistry ((M₁) v) (issued.purchases.usable v)
    have crest := ((M₁) v).lamp.crest
    change _ ∈ Finset.Icc _ _
    rw [Finset.mem_Icc]
    unfold Sunrise.Loan.lag
    omega
  have reset : Rebirth.caliber (Γ i) ζ = Rebirth.caliber filed zeroFiled := by
    unfold Rebirth.caliber
    simp only [lesson.eats]
  rw [← reset]
  exact active_bend M₁ x grades (π i) T₀ (Γ i) ζ depth order multiple lags inLags h₁ h₂ s e he A

end YM.Integration.WilsonOriginalMeasuredCopiedReset
