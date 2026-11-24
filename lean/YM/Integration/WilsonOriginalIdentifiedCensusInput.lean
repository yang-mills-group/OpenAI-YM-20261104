import YM.Integration.WilsonOriginalDatedCensusInput
import YM.Integration.WilsonOriginalDepositedModelBook

/-! Submit the predetermined compact bank on its own support and retain the paid original post. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalIdentifiedCensusInput
open Function Finset Filter RG Lattice Wilson Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison Multi
open WilsonRootedKioskOccupiedSlip VowsR LocalComparison ConnectedActivityE6
open WilsonOriginalPhysicalFieldsAtBoard
open scoped Classical BigOperators

private theorem identical {G:Gauge}{n:Side}{V α I₀ I₁:Type}[Fintype V][DecidableEq V]{p₀ p₁:Earn.Passport n V}
    {M₀:I₀ → Earn.Row p₀ (Stock.census V) G α}{M₁:I₁ → Earn.Row p₁ (Stock.census V) G α}
    (home:p₀=p₁)(index:I₀=I₁)(same:HEq M₀ M₁)(b:BudgetPoint)(g:ℝ)(x:α)(U:Config G n):
    bare (rendered M₀ b g) x U=bare (rendered M₁ b g) x U:=by
  subst p₁ I₁
  rw [eq_of_heq same]

variable {G:Gauge}(R:Run G){m i N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
  (π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀j,RG.Rep G (R.family.side j per))
  {φ:ℕ → ℕ}(books:Mentor.Offices.Books D R.rolls Q φ)(hi:m ≤ i)
  (ahead:Mentor.Forecast D R.rolls Q φ books){V:Type}[Fintype V][DecidableEq V]
local notation "J" => Stock.census V
local notation "A" => WilsonOriginalMixedBlockRows.room V
local notation "K₀" => fun _:V => (⊥:Submodule ℝ ℂ)
local notation "H" => R.alloy.B.a.clock.hatBeta i
local notation "vac" => Ψ (i+1)
local notation "y" => Coat.gStep (vac).beta

variable {I:Type}{p₀:Earn.Passport (R.family.side (i+1) per) V}
  (M:I → Earn.Row p₀ (Stock.census V) G (Wallet (WilsonOriginalMixedBlockRows.room V)))
  (grades:V → ℕ)(order shelf seats:ℕ)
  (law:Wallet (WilsonOriginalMixedBlockRows.room V) → Config G (R.family.side (i+1) per) → Marker.Poly (Stock.census V))
  (F:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead (WilsonOriginalMixedBlockRows.room V)
    (fun _:V=>(⊥:Submodule ℝ ℂ)) grades order shelf seats i hi law)
  (S:V→ℝ)(a:ℕ)
  (book:WilsonOriginalCensusAppointment.Book R hk D Q π Γ Ψ books hi ahead (WilsonOriginalMixedBlockRows.room V)
    (fun _:V=>(⊥:Submodule ℝ ℂ)) grades order shelf seats law F (fun s=>(R.alloy.B.a.clock.hatBeta i)^a*Poly.toll S s))
  (home:F.passport=p₀)(index:F.modelIndex=I)(same:HEq F.model M)
local notation "submitted" x:max => printed (J) (vac) (rendered M (vac).p (y)) x

include book home index same in
theorem declared (x:Wallet (A)):law x=submitted x:=by
  funext U
  exact (book.declared x U).trans (congrArg (fun z=>((vac).eval U:ℂ) • Poly.pass z)
    (identical home index same (vac).p (y) x U))

def issue (x:Wallet (A)):WilsonOriginalDatedCensusInput.Filed (N:=N) R hk D Q π Γ Ψ books hi ahead S a (submitted x) where
  grades:=grades
  order:=order
  shelf:=shelf
  seats:=seats
  law:=law
  post:=F
  appointment:=book
  x:=x
  atInput:=declared R hk D Q π Γ Ψ books hi ahead M grades order shelf seats law F S a book home index same x

include book home index same in
theorem original (x:Wallet (A)):
    ∃Z:WilsonOriginalDatedCensusInput.Filed (N:=N) R hk D Q π Γ Ψ books hi ahead S a (submitted x),
    Z.x=x ∧ Z.grades=grades ∧ Z.order=order ∧ Z.shelf=shelf ∧ Z.seats=seats ∧ Z.law=law ∧ HEq Z.post F ∧
      Z.post.passport=p₀ ∧ Z.post.modelIndex=I ∧ HEq Z.post.model M ∧ Z.post.w=F.w ∧ Z.post.rent=F.rent:=by
  exact ⟨issue R hk D Q π Γ Ψ books hi ahead M grades order shelf seats law F S a book home index same x,
    rfl,rfl,rfl,rfl,rfl,rfl,HEq.rfl,home,index,same,rfl,rfl⟩

end YM.Integration.WilsonOriginalIdentifiedCensusInput
end
