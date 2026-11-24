import YM.Integration.WilsonOriginalRosterFiniteMaterial
import YM.Integration.WilsonReceivedSourceCoefficientIncome
import YM.Integration.WilsonThermometerPositionFilmRecast

/-! All genuinely registered upper logarithmic faces on each real angular direction. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFilmUpperTerms
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order
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
  (cost : ℝ)
  (incoming : Scene.Armada M w grades (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)))
    cost order op.count shelf)
  (x : Affinity.Wallet actors)
  (F : Forest (R.family.path.levels.clock.op i per).ratio) (tag : (R.family.path.levels.clock.op i per).Choices)
  (A : Stationary.Link G (R.family.side i per))

local notation "T₀" => AllOrder.Floe.Step.tape (Burn.horizon k + 2)
local notation "X₀" => Air.craft M (fun j => (M j).paint x) grades (π (i+1)) T₀
local notation "M₁" => Oak.student (n:=per) R hk D Q π Γ books hi op lesson ahead actors M order voter
local notation "X₁" => Air.craft M₁ (fun j => ((M₁) j).paint x) grades (π i) T₀
local notation "b" => Stationary.arm G (R.family.side i per) 1 A
local notation "K₀" => (RunFormalChain.fromRun R).step N i per cut
local notation "published" => Mentor.Cruise.publish D R.rolls Q R.alloy φ books op
  (Oak.era R hk D Q π Γ hi op lesson) (R.alloy.B.a.S.oneStep i per).exact_size M order voter lesson.entry
local notation "miss" r:max => Alliance.miss M (fun j => (M j).paint x) (R.family.path.levels.clock.op i per).ratio
  K₀ F tag A (π (i+1)) T₀ published r
local notation "total" => Oak.Tutoring.bill R hk D Q π Γ books hi op lesson A cost

local notation "width" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)
local notation "placed" => passport.coarser (R.family.path.levels.clock.op i per).ratio
local notation "upper" => PhysicalWilsonPeriodizedMaterial.reference R N i per cut b X₀ order
include course F tag incoming in
theorem original (outcost : ℝ)
  (outgoing:Scene.Armada M₁ w grades width outcost order op.count shelf)
  (small:cost≤1){cap:ℝ}(hc:0≤cap)(axes:∀e,‖Exterior.collect G b e‖≤cap)
  
  (s:marks.Mode)(j:ℕ)(hj:j≤order):
    Poly.toll w s*‖(Order.observe marks order (Order.logMarked upper) j).part s‖≤
      WilsonReceivedSourceCoefficientIncome.price G width cap order shelf*((s.val.image (placed).origin).card*outcost)+total:=by
  have hs:0<width:=Poetry.Agenda.stem D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)
  have salary:=WilsonReceivedSourceCoefficientIncome.original M₁ w grades outgoing hs x A hc axes j hj (π i) T₀ s
  obtain ⟨e,eqn,invoice,_,_⟩:=(WilsonOriginalRosterFiniteMaterial.original R hk D Q π Γ Ψ course books hi cut op lesson
    ahead actors M w grades order shelf voter cost incoming x F tag A outcost outgoing small).2.2 j hj
  have residual:Poly.toll w s*‖e.part s‖≤total:=(Poly.member outgoing.positive s e).trans invoice
  rw [eqn]
  calc
    _ ≤ Poly.toll w s*(‖(Air.discharge X₁ j b).part s‖+‖e.part s‖):=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (Poly.worth outgoing.positive _).le
    _ ≤ _:=by rw [mul_add];exact add_le_add salary residual

end YM.Integration.WilsonThermometerPositionFilmUpperTerms
end
