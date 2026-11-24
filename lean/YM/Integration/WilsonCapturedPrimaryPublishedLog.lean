import YM.Integration.WilsonReceivedSourceRoster
import YM.Integration.WilsonFirstReceivedOriginalNodalIncome
import YM.Integration.WilsonFirstReceivedIssuedPolynomial

/-! The elected publication and the independent finite Wilson log on one actual reporting chart. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryPublishedLog
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
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
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
variable {old next:Type}(pieces:∀ v,Submodule ℝ (X v))
  (Z:Tint.Incoming passport (Ψ (i+1)) (Affinity.Wallet actors) old marks)
  (rent:ℝ) (Y:Tint.Incoming (passport.coarser (R.family.path.levels.clock.op i per).ratio)
      (Ψ i) (Affinity.Wallet actors) next marks)
local notation "received" => Oak.Buffered.SuccessStory R hk D Q π Γ Ψ books hi op lesson ahead
   actors pieces M Z w grades order shelf voter rent cost Y


open ConnectedActivityE6
local notation "gf" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "pΩ" => Oak.figureReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "fee" => Ω^op.count * Earn.Earnings.hitPrice pΩ G
  (R.family.path.levels.clock.op i per).ratio.count (Ψ (i+1)).p (Ψ i).p
  (Ω⁻¹*cost) (Ω⁻¹*rent) (Burn.young (R.alloy.B.a.clock.hatBeta (i+1)) k)
  (Coat.gStep (Ψ (i+1)).beta)

local notation "width" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)
local notation "capital" => (pΩ).produce (R.family.path.levels.clock.op i per).ratio.count * cost
local notation "placed" => passport.coarser (R.family.path.levels.clock.op i per).ratio

local notation "angle" => Stationary.arm G (R.family.side i per) 1 A
local notation "K₀" => (RunFormalChain.fromRun R).step N i per cut
local notation "point" => Order.value (gf:ℂ) (Order.logMarked (Bulk.Fk K₀ F tag X₀ angle order))
local notation "folded" => WilsonCoherentMayerWindingGrades.panel order (gf:ℂ) (fun j => Air.discharge X₁ j angle)
local notation "seam" => Oak.Tutoring.bill R hk D Q π Γ books hi op lesson A cost

include course incoming cut F tag A in
theorem original (returned : received) (small : cost ≤ 1) (simple : G.Simple)
    (opened : WilsonCoherentMayerRosterWindingRun.firstDate R simple ≤ i+1)
    {cap : ℝ} (hc : 0 ≤ cap) (axis : ∀ e, ‖Exterior.collect G angle e‖ ≤ cap)
    (clear : flags (Ψ i).p.threshold (Integral.sample gf angle) = ∅) (s : marks.Mode) :
    let W := Integral.sample gf angle
    let read := (rendered M₁ (Ψ i).p gf).log x W
    read = Integral.markedLog gf W X₁ ∧
    Poly.toll w s * ‖(read-point).part s‖ ≤
      WilsonReceivedSourceRoster.tariff G width cap gf order shelf * ((s.val.image (placed).origin).card*capital)
        + 2*seam := by
  intro W read
  have gp : 0 < gf := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  obtain ⟨_, certified⟩ := WilsonOriginalMarkedEvaluation.assessed R hk D Q π Γ Ψ course
    books hi cut op lesson ahead actors M w grades order shelf voter cost incoming x F tag A
    pieces Z rent Y returned small simple opened
  have painted := certified.2.1 gf gp.ne' W
  have frames : (fun j => (rendered M₁ (Ψ i).p gf).frame j x W) =
      fun j => Poly.send ((M₁) j).mode (((M₁) j).nominal gf x W) := by
    funext j
    have healthy : Healthy (Ψ i).p.threshold (((M₁) j).ground (Ψ i).p) W := by
      change Disjoint _ (RG.flags (Ψ i).p.threshold W)
      rw [clear]
      exact disjoint_bot_right
    by_cases sunny : ((M₁) j).clear
    · simp [Lamps.frame,Lamps.light,rendered,sunny]
    · simp [Lamps.frame,Lamps.light,Lamps.ground,rendered,sunny,masked_eq _ _ _ _ healthy]
  rw [←frames] at painted
  have exactAt : read=Integral.markedLog gf W X₁ := painted.tsum_eq
  refine ⟨exactAt,?_⟩
  have tail := WilsonReceivedSourceRoster.original M₁ w grades returned.earning (Poetry.Agenda.stem ..)
    x A hc axis gp (π i) T₀ s
  have legal : Legal T₀ (π (i+1)) := by
    rw [lesson.ticket]
    exact AllOrder.Floe.Step.PlanV.audited R.rolls D _ _ _ lesson.entry
  have staff := Air.license M (fun a => (M a).paint x) grades w incoming (Poetry.Agenda.stem ..) (fun a => incoming.honor a x)
  have well := (Air.standard M _ grades staff (π (i+1)) T₀ legal).1
  have winding : Poly.price w (folded-point) ≤ 2*seam := by
    rw [PhysicalWilsonPeriodizedMaterial.original R N i per cut angle X₀ order F tag well]
    exact certified.2.2.2.2
  rw [exactAt]
  let κ := Poly.toll w s
  let mid := (Integral.markedLog gf W X₁).part s
  have move (a b c : ℂ) : κ*‖a-c‖ ≤ κ*‖a-b‖ + κ*‖b-c‖ := by
    rw [←mul_add]
    exact mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using dist_triangle a b c)
      (Poly.worth returned.earning.positive s).le
  calc
    _ ≤ κ*‖mid-(folded).part s‖+κ*‖(folded).part s-(point).part s‖ := move _ _ _
    _ ≤ _ := add_le_add tail ((Poly.member returned.earning.positive s (folded-point)).trans winding)

end YM.Integration.WilsonCapturedPrimaryPublishedLog
