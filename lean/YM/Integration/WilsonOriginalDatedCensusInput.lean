import YM.Integration.WilsonOriginalCensusAppointment
import YM.Integration.WilsonOriginalPhysicalFieldsAtBoard
import YM.Integration.WilsonOriginalMixedBlockRows

/-! Opening an authentic paid census book at its selected wallet on an original dated Wilson post. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalDatedCensusInput
open Function Finset Filter RG Lattice Wilson Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison Multi
open WilsonRootedKioskOccupiedSlip VowsR LocalComparison ConnectedActivityE6
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G){m i N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
  (π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀j,RG.Rep G (R.family.side j per))
  {φ:ℕ → ℕ}(books:Mentor.Offices.Books D R.rolls Q φ)(hi:m ≤ i)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  {V:Type}[Fintype V][DecidableEq V]
local notation "J" => Stock.census V
local notation "A" => WilsonOriginalMixedBlockRows.room V
local notation "K₀" => fun _:V => (⊥:Submodule ℝ ℂ)
local notation "χ" => R.family.path.levels.clock.hatBeta i

/-- The actual fresh post, its original invoice, and the given appointed independent input at that date. -/
structure Filed (S:V → ℝ)(a:ℕ)(submitted:Config G (R.family.side (i+1) per) → Poly J) where
  grades : V → ℕ
  order : ℕ
  shelf : ℕ
  seats : ℕ
  law : Wallet (A) → Config G (R.family.side (i+1) per) → Poly J
  post : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead (A) (K₀) grades order shelf seats i hi law
  appointment : WilsonOriginalCensusAppointment.Book R hk D Q π Γ Ψ books hi ahead (A) (K₀) grades order shelf seats law post
    (fun t=>χ^a*Poly.toll S t)
  x : Wallet (A)
  atInput : law x=submitted

namespace Filed
theorem paid (S:V → ℝ)(a:ℕ)(submitted:Config G (R.family.side (i+1) per) → Poly (J))
    (pub:Filed (N:=N) R hk D Q π Γ Ψ books hi ahead S a submitted)(s:(J).Mode):
    let row:=pub.appointment.row pub.x
    row.A.density row.x=LocalComparison.actualPush R.family N per i submitted ∧
    (WilsonOriginalOccupiedSalary.debit row.regular row.hard)^s.val.card ≤ χ^a*(Poly.toll S s*Poly.toll row.w s):=by
  intro row
  constructor
  · exact (pub.appointment.density pub.x).trans (congrArg (LocalComparison.actualPush R.family N per i) pub.atInput)
  · simpa only [mul_assoc] using pub.appointment.wage pub.x s
end Filed

/-- Use the original book's own declaration of its entire submitted uncut group function. -/
def ofBook (grades:V → ℕ)(order shelf seats:ℕ)
    (law:Wallet (A) → Config G (R.family.side (i+1) per) → Poly J)
    (post:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead (A) (K₀) grades order shelf seats i hi law)
    (S:V → ℝ)(a:ℕ)(book:WilsonOriginalCensusAppointment.Book R hk D Q π Γ Ψ books hi ahead (A) (K₀)
      grades order shelf seats law post (fun s=>χ^a*Poly.toll S s))(x:Wallet (A)):
    Filed (N:=N) R hk D Q π Γ Ψ books hi ahead S a
      (fun U=>((Ψ (i+1)).eval U:ℂ) • Poly.pass (bare (rendered post.model (Ψ (i+1)).p (Coat.gStep (Ψ (i+1)).beta)) x U)) where
  grades:=grades
  order:=order
  shelf:=shelf
  seats:=seats
  law:=law
  post:=post
  appointment:=book
  x:=x
  atInput:=funext (book.declared x)

end YM.Integration.WilsonOriginalDatedCensusInput
end
