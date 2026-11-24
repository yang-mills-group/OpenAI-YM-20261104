import YM.Integration.WilsonOriginalDatedCensusInput
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathVotedBook
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

open WilsonOriginalDatedCensusInput

/-- An independently named incoming function may be replaced by the original book's equal declaration on its chosen wallet. -/
theorem same {S:V → ℝ}{a:ℕ}{submitted:Config G (R.family.side (i+1) per) → Poly J}
    (z:Filed (N:=N) R hk D Q π Γ Ψ books hi ahead S a submitted)
    (f:Config G (R.family.side (i+1) per) → Poly J)(read:z.law z.x=f):
    HEq z (⟨z.grades,z.order,z.shelf,z.seats,z.law,z.post,z.appointment,z.x,read⟩:
      Filed (N:=N) R hk D Q π Γ Ψ books hi ahead S a f) := by
  cases z with
  | mk grades order shelf seats law post book x written =>
    dsimp only at read
    cases written
    cases read
    rfl

/-- The actual voted post, grades and finite-period wallet survive taking the artist's whole printed field. -/
theorem original {S:V → ℝ}{a:ℕ}{submitted:Config G (R.family.side (i+1) per) → Poly J}
    (z:Filed (N:=N) R hk D Q π Γ Ψ books hi ahead S a submitted):
    HEq z (ofBook R hk D Q π Γ Ψ books hi ahead z.grades z.order z.shelf z.seats z.law z.post
      S a z.appointment z.x) :=
  same R hk D Q π Γ Ψ books hi ahead z _ (funext (z.appointment.declared z.x))

/-- Recover the very appointment in the hired post when its dependent indices were published by equality. -/
theorem mounted {S:V → ℝ}{a:ℕ}{submitted:Config G (R.family.side (i+1) per) → Poly J}
    (g:V → ℕ)(o h s:ℕ)(law:Wallet (A) → Config G (R.family.side (i+1) per) → Poly J)
    (F:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead (A) (K₀) g o h s i hi law)
    (x:Wallet (A))(z:Filed (N:=N) R hk D Q π Γ Ψ books hi ahead S a submitted)
    (xv:z.x=x)(gv:z.grades=g)(ov:z.order=o)(hv:z.shelf=h)(sv:z.seats=s)(lv:z.law=law)(fv:HEq z.post F):
    ∃b:WilsonOriginalCensusAppointment.Book R hk D Q π Γ Ψ books hi ahead (A) (K₀) g o h s law F
      (fun t => χ^a*Poly.toll S t),
      HEq z (ofBook R hk D Q π Γ Ψ books hi ahead g o h s law F S a b x) := by
  subst g; subst o; subst h; subst s; subst law; subst x
  have posted:=eq_of_heq fv
  subst F
  exact ⟨z.appointment,original R hk D Q π Γ Ψ books hi ahead z⟩

end YM.Integration.WilsonNeutralTwoPrintPathVotedBook
end
