import YM.Integration.WilsonFiniteSignedResetProbes
import YM.Integration.WilsonOriginalMeasuredStampCoefficients

/-! On the same issued Wilson course compare the actual dated student after
its measured reset with the exact preceding finite Wilson Wick coefficient
in that same variable. Its signed error uses only the genuine dated missing
club bills on the finite real rays, before either regulator is taken. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalIssuedFiniteResetProbes
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Stationary Comparison.RG02 QuadraticLocal.Rebirth
open scoped Classical BigOperators
open WilsonFiniteSignedResetProbes

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


variable (cost : ℝ)
  (incoming : Scene.Armada M w grades (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)))
    cost order op.count shelf)
  (x : Affinity.Wallet actors)
  (F : Forest (R.family.path.levels.clock.op i per).ratio) (tag : (R.family.path.levels.clock.op i per).Choices)
local notation "arm" => Stationary.arm G (R.family.side i per) 1
local notation "X₀" => Air.craft M (fun a => (M a).paint x) grades (π (i+1)) T₀
local notation "X₁" => Air.craft M₁ (fun a => ((M₁) a).paint x) grades (π i) T₀
local notation "X₂" => Air.craft stamped (fun a => ((stamped) a).paint x) grades (π i) T₀
local notation "form" => (RunFormalChain.fromRun R).step N i per cut
local notation "κ" => (Rebirth.caliber filed zeroFiled).back depth
local notation "invoice" z:max => Oak.Tutoring.bill R hk D Q π Γ books hi op lesson z cost

include course incoming F tag
theorem original (pass : Pass D Q R.alloy R.kit) (month : Scholar.Month R.rolls D Q R.alloy.delay)
    (fits : order ≤ Burn.horizon k+1) (narrow : shelf ≤ R.alloy.B.a.clock.J i)
    (outcost : ℝ) (outgoing : Scene.Armada M₁ w grades scale outcost order op.count shelf)
    (small : cost ≤ 1) (p : ℕ) (hp : p ≤ order) (s : marks.Mode)
    (A : Stationary.Link G (R.family.side i per)) :
    let d := FVA1Physical.Wilson.resetDegree grades s order
    let finite := fun j z => (Order.observe marks order (Order.logMarked
      (PhysicalWilsonPeriodizedMaterial.reference R N i per cut (arm z) X₀ order)) j).part s
    let issued := fun j z => (Air.discharge X₁ j (arm z)).part s
    let discrepancy := Adjacent.born finite κ 0 order p A - (Air.discharge X₂ p (arm A)).part s
    discrepancy =
      ∑ j∈range (order+1), ∑ b:Fin (d+1), ∑ l:Fin (d+1),
        weight κ 0 d p j b l * (finite j (node d l • A) - issued j (node d l • A)) ∧
    Poly.toll w s * ‖discrepancy‖ ≤
      ∑ j∈range (order+1), ∑ b:Fin (d+1), ∑ l:Fin (d+1),
        ‖weight κ 0 d p j b l‖ * invoice (node d l • A) := by
  intro d finite issued discrepancy
  have legal : Legal T₀ (π (i+1)) := by
    rw [lesson.ticket]
    exact AllOrder.Floe.Step.PlanV.audited R.rolls D _ _ _ lesson.entry
  have fineStaff := Air.license M (fun a => (M a).paint x) grades w incoming
    (Poetry.Agenda.stem ..) (fun a => incoming.honor a x)
  have well := (Air.standard M _ grades fineStaff (π (i+1)) T₀ legal).1
  have finiteDegree : Adjacent.Charge order (fun _=>(d:ℤ)) finite := by
    have h := FVA1Physical.Wilson.ledger_charge form F tag X₀ grades s (fun _=>rfl) order
    have identify : finite = fun j z=>(Order.observe marks order (Order.logMarked
        (Bulk.Fk form F tag X₀ (arm z) order)) j).part s := by
      funext j z
      exact congrArg (fun Z=>(Order.observe marks order (Order.logMarked Z) j).part s)
        (PhysicalWilsonPeriodizedMaterial.original R N i per cut (arm z) X₀ order F tag well).symm
    exact identify.symm ▸ h
  have staff := Air.license M₁ (fun a=>((M₁) a).paint x) grades w outgoing
    (Poetry.Agenda.stem ..) (fun a=>outgoing.honor a x)
  have issuedDegree : Adjacent.Charge order (fun _=>(d:ℤ)) issued :=
    FVA1Physical.Wilson.painter_charge grades s X₁ (fun _=>rfl)
      (fun a=>(Air.grade M₁ _ grades staff (π i) T₀ a).smooth) order
  have stampedEq := (WilsonOriginalMeasuredStampCoefficients.original R hk D Q π Γ Ψ course books hi cut
    op lesson ahead actors M w grades order shelf voter pass month fits narrow outcost outgoing x).2.2 A p hp s
  change Adjacent.born finite κ 0 order p A - (Air.discharge X₂ p (arm A)).part s = _ ∧ _ 
  dsimp only [discrepancy]
  rw [stampedEq]
  refine ⟨signed finite issued κ 0 finiteDegree issuedDegree p A, ?_⟩
  apply measured finite issued κ 0 finiteDegree issuedDegree p A (Poly.toll w s) (Poly.worth incoming.positive _).le (fun z=>invoice z)
  intro j hj z
  obtain ⟨e, eqn, fair, _, _⟩ := (WilsonOriginalRosterFiniteMaterial.original R hk D Q π Γ Ψ course books hi
    cut op lesson ahead actors M w grades order shelf voter cost incoming x F tag z outcost outgoing small).2.2 j hj
  have same : finite j z - issued j z = e.part s := by
    change (Order.observe marks order _ j).part s - (Air.discharge X₁ j (arm z)).part s = _
    rw [eqn]; simp
  rw [same]
  exact (Poly.member incoming.positive s e).trans fair

end YM.Integration.WilsonOriginalIssuedFiniteResetProbes
