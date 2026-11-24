import YM.Integration.WilsonOriginalMeasuredCopiedReset
import YM.Integration.WilsonOriginalCopiedMarkerLayout
import YM.Integration.WilsonNeutralPupilOrder
import YM.Integration.WilsonOriginalCoverCoefficient
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalRetainedStamp

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
theorem original (pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (fits:order ≤ Burn.horizon k+1)(narrow:shelf ≤ R.alloy.B.a.clock.J i)
    (cost:ℝ)(issued:Scene.Armada M₁ w grades scale cost order op.count shelf)
    (x:Affinity.Wallet actors){grid:Side}(h:(R.family.side i per).val ∣ grid.val)
    (r d:ℕ)(small:r ≤ order)(kept:d ≤ r)(s:Multi.Hot marks)(z:Stationary.Link G grid)
    (value:ℕ → Stationary.Link G grid → Poly marks)
    (source:∀ a≤r,∀ y,value a y=peek h M₁ grades (π (i+1)) T₀ x a y):
    (peek h stamped grades (π i) T₀ x d z).part s.val =
      Adjacent.born (fun a y=>(value a y).part s.val) ((Rebirth.caliber (Γ i) ζ).back depth) 0 r d z:=by
  have att:=WilsonOriginalMeasuredCopiedReset.original (R:=R) (hk:=hk) (course:=course) (hi:=hi)
    (cut:=cut) (lesson:=lesson) (books:=books) (op:=op) (ahead:=ahead) (pass:=pass) (month:=month)
    (fits:=fits) (narrow:=narrow) (cost:=cost) (issued:=issued) (x:=x) (multiple:=h) (A:=z)
    (e:=d) (he:=kept.trans small) (s:=s.val)
  have unit:Rebirth.caliber (Γ i) ζ=Rebirth.caliber filed zeroFiled:=by
    unfold Rebirth.caliber
    simp only [lesson.eats]
  rw [← unit] at att
  have staff:=Air.license M₁ (fun v=>(M₁ v).paint x) grades w issued (Poetry.Agenda.stem ..) (fun v=>issued.honor v x)
  refine att.trans ((WilsonNeutralPupilOrder.triangular (fun a y=>(peek h M₁ grades (π i) T₀ x a y).part s.val)
    _ kept small z (fun a _=>WilsonNeutralPupilOrder.smooth h M₁ grades (π i) T₀ x a s)).trans ?_)
  apply WilsonOriginalCoverCoefficient.reset_eq
  intro a ha
  funext y
  rw [source a ha y, WilsonOriginalCopiedMarkerLayout.same h M₁ grades (π (i+1)) (π i) T₀ x a y staff]

end YM.Integration.WilsonOriginalRetainedStamp
