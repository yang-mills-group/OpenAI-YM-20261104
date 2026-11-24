import YM.Integration.WilsonFirstReceivedGalleryNodes
import YM.Integration.WilsonOriginalMarkedEvaluation

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonFirstReceivedOriginalNodalIncome
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

include course incoming cut F tag A in
theorem original (returned:received) (small:cost≤1) (simple:G.Simple)
    (opened:WilsonCoherentMayerRosterWindingRun.firstDate R simple ≤ (i+1))
    (hw:∀v,0<w v) (W:Config G (R.family.side i per)) (hW:flags (Ψ i).p.threshold W=∅)
    (s:marks.Mode) (v:V) (hv:v∈s.val) :
    let read := Order.logTo (Fintype.card V) ((((Ψ i).eval W:ℂ)⁻¹) •
      (LocalComparison.actualPush R.family N per i ((Tint.Patrol.picture M Z).density x) W))
    read = Integral.markedLog gf W X₁ + Y.old.log x W ∧
      Poly.toll w s * ‖(read-Integral.markedLog gf W X₁).part s‖ ≤ fee := by
  dsimp only
  obtain ⟨push,filed⟩ := WilsonOriginalMarkedEvaluation.assessed R hk D Q π Γ Ψ course
    books hi cut op lesson ahead actors M w grades order shelf voter cost incoming x F tag A
    pieces Z rent Y returned small simple opened
  have positive : 0 < (R.family.path.rep N per (i+1)).beta := Overlay.beta_positive R.makes.wilson cut
  have gp : 0<gf := inv_pos.mpr (Real.sqrt_pos.mpr positive)
  have group := filed.2.1 gf gp.ne' W
  have frames : (fun j=>(rendered M₁ (Ψ i).p gf).frame j x W) =
      fun j=>Poly.send ((M₁) j).mode (((M₁) j).nominal gf x W) := by
    funext j
    have h : Healthy (Ψ i).p.threshold (((M₁) j).ground (Ψ i).p) W := by
      change Disjoint _ (RG.flags (Ψ i).p.threshold W)
      rw [hW]
      exact disjoint_bot_right
    by_cases isClear : ((M₁) j).clear
    · simp [Lamps.frame,Lamps.light,rendered,isClear]
    · simp [Lamps.frame,Lamps.light,Lamps.ground,rendered,isClear,masked_eq _ _ _ _ h]
  rw [←frames] at group
  have logged : (rendered M₁ (Ψ i).p gf).log x W=Integral.markedLog gf W X₁ :=
    group.tsum_eq
  have invoice := WilsonFirstReceivedGalleryNodes.original M₁ Y
    (w:=w) (g:=gf) (by linarith only [(Ψ i).p.exponent_pos]) hw returned.tuition x W hW
    group.summable s v hv
  dsimp only at invoice
  rw [logged] at invoice
  rw [congr_fun (push x) W]
  exact invoice

end YM.Integration.WilsonFirstReceivedOriginalNodalIncome
end
