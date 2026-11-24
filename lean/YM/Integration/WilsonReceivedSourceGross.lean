import YM.Integration.WilsonOriginalReceivedFoldedPost
import YM.Integration.WilsonCoherentMayerPublishedGross
import YM.Integration.WilsonRootedKioskPostRadius
import YM.Integration.WilsonMovingMentorHardTemperature

/-! The all-group nominal receipt on the actual received output. Its support
and budget are carried through the same pupil and the same measured course. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedSourceGross
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open scoped Classical BigOperators Topology
open Push.AbsoluteSums

def opening {G : Gauge} (R : Run G) (simple : G.Simple) : ℕ :=
  (eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m ≤ i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) {V : Type} [Fintype V] [DecidableEq V]
  {X : V → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical)

local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "lamps" => (rendered student (Ψ i).p oldG)
local notation "exponent" => ((Ψ i).p.supportExponent+1+1)
local notation "price" => ((Spill.allOver (Ψ i).p)^(order+shelf+1)*Ω)
local notation "g" => Coat.gStep (R.family.path.rep N per (i+1)).beta

/-- These are the analytic lamps inside the published physical gallery. Its
joined old regular set and its complete physical hard array are the actual post's. -/
theorem gallery : (Tint.Patrol.report student P.output oldG).E=(lamps).join P.output.old ∧
    (Tint.Patrol.report student P.output oldG).K=P.output.hard := ⟨rfl,rfl⟩

/-- Every issued analytic occurrence at all group fields, using the original
source weights and the retained support exponent plus two. -/
theorem landed : WilsonRootedKioskOccupiedSlip.Gross lamps P.w (Ψ i).p.B exponent price := by
  let cash := P.issued.Waffle
  let cap := (fig).produce (sheet).ratio.count*P.cost
  have b₀ : 0 ≤ P.cost := budget_nonneg (P.salary.suggests 0)
  have enough : cap ≤ 1 := calc
    _ ≤ Ω*P.cost := mul_le_mul_of_nonneg_right cash.earns b₀
    _ ≤ Ω*Ω⁻¹ := mul_le_mul_of_nonneg_left P.affordable cash.paysAbove.le
    _ = _ := mul_inv_cancel₀ cash.paysAbove.ne'
  let due := Invoice.price (Ψ i).p (fig).mist (order+shelf+1) P.op.count exponent (fig).limitC G
  have salary : due*cap ≤ Ω :=
    (mul_le_of_le_one_right cash.minted.le enough).trans cash.quote
  obtain ⟨f,pos,values,paid⟩ := (WilsonCoherentMayerPublishedGross.landed student P.w grades (Ψ i).p
    P.issued.earning cash.soon).before
  refine ⟨f,pos,values,fun x => budget_loosen (paid x) ?_⟩
  exact mul_le_mul_of_nonneg_left salary (pow_nonneg (zero_le_one.trans (Spill.allOver_ge _)) _)

include course cut in
/-- The date threshold is independent of every physical regulator, chosen
position and issued pupil. The extra factor of the adjacent temperature pays
the expense ceiling on the same course. -/
theorem original (simple : G.Simple) (late : opening R simple ≤ i)
    (pass : Pass D Q R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (narrow : shelf ≤ R.alloy.B.a.clock.J i) (load : P.op.count ≤ Burn.horizon k+2) :
    WilsonRootedKioskOccupiedSlip.Gross lamps P.w (Ψ i).p.B exponent price ∧
      price ≤ (2:ℝ)^(order+shelf+2)/g^(2*(order+shelf+2)) := by
  refine ⟨landed R hk D Q π Γ Ψ books hi ahead actors pieces grades order shelf seats physical P,?_⟩
  let iWalk := course.1.walk i hi cut.le
  let jWalk := course.1.walk (i+1) (Nat.le_succ_of_le hi) cut
  let x := R.alloy.B.a.clock.hatBeta i
  let y := R.alloy.B.a.clock.hatBeta (i+1)
  have window := (eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose_spec i late
  have land : Spill.allOver (Ψ i).p ≤ y := by
    rw [iWalk.truep.point]
    exact window.2.2.1.trans window.2.1
  have upper : 1 ≤ y := window.1.trans window.2.1
  let paidWalk := (WilsonMovingMentorIncomingSlots.original R course hi cut).2.2.choose
  letI : Countable P.modelIndex := P.modelCount
  have band : (Ψ (i+1)).beta ∈ Shoot.band R.alloy.B.a (i+1) := by
    rw [jWalk.beta]
    exact (R.makes.wilson.represents N per (i+1) cut).band
  have wallet := Mentor.Cruise.Semester.tight D R.rolls Q R.alloy R.kit φ books pass P.op
    (Oak.era R hk D Q π Γ hi P.op P.lesson) (R.alloy.B.a.S.oneStep i per).exact_size P.model order
    P.voter ahead jWalk.truep.point paidWalk iWalk.truep.point hospital load shelf narrow band
  have grain : Beaming.grain (R.alloy.B.a.clock.J i) ≤ 1 := by
    unfold Beaming.grain
    exact (div_le_one (by positivity)).mpr (by linarith only [Nat.cast_nonneg (α:=ℝ) (R.alloy.B.a.clock.J i)])
  have expense : Ω ≤ y := (wallet.1.trans (min_le_right ..)).trans
    ((Real.rpow_le_rpow_of_exponent_le upper grain).trans_eq (Real.rpow_one y))
  have gross : price ≤ y^(order+shelf+2) := by
    rw [show y^(order+shelf+2)=y^(order+shelf+1)*y from pow_succ ..]
    exact mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans (Spill.allOver_ge _)) land _) expense
      P.issued.Waffle.paysAbove.le (pow_nonneg (zero_le_one.trans upper) _)
  have gp : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  apply (le_div_iff₀ (pow_pos gp _)).mpr
  have hot := WilsonMovingMentorHardTemperature.measured R cut per (order+shelf+2) 0
  calc
    _ = g^(2*(order+shelf+2))*price := mul_comm .. 
    _ ≤ g^(2*(order+shelf+2))*y^(order+shelf+2) :=
      mul_le_mul_of_nonneg_left gross (pow_nonneg gp.le _)
    _ ≤ _ := by simpa only [Nat.zero_add,pow_zero,one_mul,y] using hot

end YM.Integration.WilsonReceivedSourceGross
