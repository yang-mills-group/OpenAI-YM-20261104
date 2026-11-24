import YM.Integration.WilsonReceivedCloseOrdinary
import YM.Integration.WilsonReceivedCloseOrdinaryScale
import YM.Integration.WilsonReceivedSingletonWindow

/-! Ordinary close-window hearing on the same measured post as the enrolled four faces. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseOrdinaryPurchase
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Extra.Histories MergeProof.Accent Pert.Asymptotics Filter WilsonOriginalReceivedChain
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra Source
open FullQLocal FullQLocal.RenderedStep Multi Exterior Comparison.RG02.Cumulants
open scoped BigOperators

variable {G : Gauge} (R : Run G) {m b N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (mb : m ≤ b)
  (source : Wallet actors → Config G (R.family.side (b+1) per) → Poly (Stock.census V))

local notation "read" i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R actors source i ib
local notation "P" i:max f:max y:max => Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y
local notation "g" => regulatorRun R.family N per
local notation "move" i:max => R.family.path.levels.clock.op i per


def Heard (P₀ : P b mb source) (top : b<N) (span : ℕ) (H angleCap : ℝ)
    (C : V) (s : (Stock.census V).Mode) (tolerance : ℝ) : Prop :=
    ∀ i (ib : i ≤ b) (mi : m ≤ i), ∃ L : P i mi (read i ib),
      WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
        mb source P₀ i mi (read i ib) L ∧
      ∀ (x : Wallet actors) (F : Forest (move i).ratio) (tag : (move i).Choices)
        (u : Stationary.Link G (R.family.side i per)) (z : ℝ),
        let Q₀ := R.family.path.levels.budget i
        let angle := Stationary.arm G (R.family.side i per) 1 u
        |z| ≤ |H| * (Real.log (R.family.path.levels.clock.hatBeta i))^span*((Q₀.B:ℝ)^2*Q₀.threshold)/(g (i+1)) →
        (∀ e, ‖Exterior.collect G angle e‖ ≤ angleCap * |z|) →
        let U := Integral.sample (g (i+1)) angle
        flags (Ψ i).p.threshold U=∅ →
        let Y := (((Ψ i).eval U:ℂ)⁻¹) • LocalComparison.actualPush R.family N per i ((read i ib) x) U
        let bank := Air.craft L.model (fun s => (L.model s).paint x) grades (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
        let program := (RunFormalChain.fromRun R).step N i per (ib.trans_lt top)
        let W := Bulk.Fk program F tag bank angle order
        let Z := Order.value (g (i+1):ℂ) (Order.ratio W)
        ‖(Y.part s-Y.part ((Stock.census V).fire C))-(Z.part s-Z.part ((Stock.census V).fire C))‖ ≤ tolerance

def fee (cash unit : ℝ) (q D : ℕ) : ℝ :=
  2*cash+2*cash*(3*unit)+cash^2+(3:ℝ)^(q+1+2*(2*D+2))*(3*unit)^2

theorem nonneg {cash unit : ℝ} (cp : 0≤cash) (up : 0≤unit) (q D : ℕ) : 0≤fee cash unit q D := by
  dsimp [fee]; positivity

local notation "stage" => (budgetR R b)^2*(budgetR R (b+1))^7
local notation "requested" cash:max x:max prec:max D:max => cash*(x^(-(1:ℝ))*x^(-(1:ℝ)))*x^(prec-2*D*2)
local notation "stars" => Stock.census V

theorem original (P₀ : P b mb source) (top : b<N) (simple : G.Simple)
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ) (kfit : k ≤ R.alloy.B.a.clock.J m)
    (protection : ∀ x k : ℕ, k ≤ x → ∀ β : ℝ, R.alloy.delay.betaEntry x ≤ β →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹^2) ≤ β)
    (law : VowsR.LawScroll G φ) (chamber : VowsR.Chamber law R.kit D Q books)
    (fund : Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (A B C : V) (s : (stars).Mode) (different : A≠B) (pair : s.val={A,B})
    (q prec D₀ span degree : ℕ) (cash unit ε H angleCap cap : ℝ)
    (cash₀ : 0≤cash) (unit₀ : 0≤unit) (ep : 0<ε) (hc : 0≤angleCap) (cn : 0≤cap)
    (grade : q+6*D₀+5 ≤ prec) (testedOrder : prec ≤ order)
    (width : V→ℝ) (wp : ∀v,0<width v)
    (enrolled : ∀v ∈ ({A,B,C}: Finset V), width v=1)
    (birth : ∀v ∈ ({A,B,C}:Finset V), 1 ≤ stage^2*(unit*((g b)⁻¹)^(2*D₀))*P₀.w v)
    (paid : WilsonReceivedCloseSlate.Paid R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      mb source P₀ top 2 span H angleCap width (fun _ => requested cash (g b) prec D₀))
    (close : PaceR.Close R degree cap m b)
    (budget : (eventually_atTop.mp (WilsonReceivedCloseEndpoint.with_history R simple degree
      (2*2) 0 cn (η:=1) zero_lt_one (le_rfl:0≤(0:ℝ)))).choose ≤ b)
    (clock : (eventually_atTop.mp (WilsonReceivedCloseChainFunding.upper R simple degree cap)).choose ≤ b)
    (birthCalendar : (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose ≤ b)
    (cooled : (eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose ≤ b)
    (selected : (eventually_atTop.mp (WilsonReceivedSingletonWindow.original R simple D φ protection grades
      order shelf k seats span H angleCap hc)).choose ≤ m)
    (wait : (eventually_atTop.mp (WilsonReceivedCloseSourceCalendar.reporter_fee R simple
      (nonneg cash₀ unit₀ q D₀) ep)).choose ≤ b) :
    Heard R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb source P₀ top span H angleCap C s
      (ε*(g b)^q) := by
  intro i ib mi
  obtain ⟨L,record,ordinary⟩ := WilsonReceivedCloseOrdinary.original R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats mb source P₀ top 2 span H angleCap width _ paid wp le_rfl A B C s different pair i ib mi
  refine ⟨L,record,?_⟩
  obtain ⟨d,one,radius,room⟩ := WilsonReceivedCloseTrailWallet.original R hk D Q π Γ Ψ books ahead actors pieces
    grades order shelf seats mb source P₀ simple record degree 2 cn zero_lt_one top.le close budget
  let base := g b
  let heat := g (i+1)
  have bands := (eventually_atTop.mp (WilsonReceivedCloseChainFunding.upper R simple degree cap)).choose_spec b clock m mb close N per top.le
  have temp := bands (i+1) (by omega) (by omega)
  have temper := (eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose_spec b cooled N per top.le
  have comparable := WilsonReceivedCloseOrdinaryScale.inverse R simple (per:=per) ib top birthCalendar
  have node : ‖(heat:ℂ)‖ = heat := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg temp.1.le]
  have gsmall : ‖(heat:ℂ)‖ ≤ 1 := node.trans_le (temp.2.trans temper.2)
  have u₀ := zero_lt_one.trans_le one
  have edge₁ : 1 ≤ stage := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (budget_pos R)) (one_le_pow₀ (budget_pos R))
  have capD : stage^2*d ≤ base⁻¹ := by
    have raised : 1 ≤ stage^2*d := one_le_mul_of_one_le_of_one_le (one_le_pow₀ edge₁) one
    have up : stage^2*d ≤ (stage^2*d)^2 := by simpa only [pow_one] using pow_le_pow_right₀ raised (by decide:1≤2)
    exact up.trans (by simpa only [Real.rpow_neg_one] using room)
  have bill (v:V) (seen : v∈({A,B,C}:Finset V)) :
      (heat*L.w v)⁻¹ ≤ 3*unit*(base⁻¹)^(2*D₀+2) :=
    WilsonReceivedCloseOrdinaryScale.singleton D₀ temper.1 u₀ (L.salary.positive v) unit₀ comparable capD
      (birth v seen) (radius v)
  intro x F tag u z Q₀ angle tested inside U healthy Y bank program W Z
  let axis := (stars).fire
  let T := Order.value (heat:ℂ) (Order.logMarked W)
  let mean (v:V) := ‖T.part (axis v)‖
  let mass' (v:V) := WilsonIndependentOrdinaryPairGrade.mass
    (WilsonIndependentOrdinaryPairGrade.slot (axis v) (Order.render (Order.ratio W)))
  let E := requested cash base prec D₀
  have en : 0 ≤ E := mul_nonneg (mul_nonneg cash₀ (mul_nonneg (Real.rpow_nonneg temper.1.le _) (Real.rpow_nonneg temper.1.le _))) (pow_nonneg temper.1.le _)
  have win := (eventually_atTop.mp (WilsonReceivedSingletonWindow.original R simple D φ protection grades order shelf k
    seats span H angleCap hc)).choose_spec i (selected.trans mi) hk (kfit.trans (R.alloy.B.a.fits.mono mi)) Q
      π Γ Ψ course books law chamber fund mi (ib.trans_lt top) ahead actors pieces (read i ib) L x u z tested inside F tag
  have moment (v:V) : heat*(L.w v*mass' v) ≤ 1 ∧ heat*(L.w v*mean v) ≤ 1 := by
    obtain ⟨m,h⟩ := win v
    have y := h (heat:ℂ) gsmall
    have m' : heat*(Poly.toll L.w (axis v)*mass' v) ≤ 1 := m
    have y' : heat*(Poly.toll L.w (axis v)*mean v) ≤ 1 := y
    have oneSlot : Poly.toll L.w (axis v)=L.w v := by simp only [axis,Poly.toll,Marker.Census.fire,Finset.prod_singleton]
    rw [oneSlot] at m' y'
    exact ⟨m',y'⟩
  have fire (v : V) (seen : v∈({A,B,C}:Finset V)) : Poly.toll width (axis v)=1 := by
    simpa only [axis,Poly.toll,Marker.Census.fire,Finset.prod_singleton] using enrolled v seen
  have fa := fire A (by simp)
  have fb := fire B (by simp)
  have fc := fire C (by simp)
  have fs : Poly.toll width s=1 := by
    unfold Poly.toll
    rw [pair]
    simp [different,enrolled A (by simp),enrolled B (by simp)]
  let err := ‖(Y.part s-Y.part (axis C))-(Z.part s-Z.part (axis C))‖
  have entered : err ≤ E+E+E*(mean B+E)+mean A*E+heat^(order+1)*(mass' A*mass' B) := by
    let cc (v:(stars).Mode) := E/Poly.toll width v
    have raw : err ≤ cc s+cc (axis C)+cc (axis A)*(mean B+cc (axis B))+mean A*cc (axis B)+
      ‖(heat:ℂ)‖^(order+1)*(mass' A*mass' B) := ordinary x F tag u z tested inside healthy gsmall
    simpa only [cc,fs,fa,fb,fc,div_one,node] using raw
  have mb₀ : 0 ≤ mass' B := Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  have invoice := WilsonReceivedOrdinaryPayment.numeric temp.1 (L.salary.positive A) (L.salary.positive B)
    en en mb₀ (moment A).2 (moment B).2 (moment A).1 (moment B).1 entered
  have growth := WilsonReceivedCloseOrdinaryScale.booked temper.1 (by linarith only [temper.1,temper.2])
    cash₀ (show 2*D₀*2+(q+1+(2*D₀+2))+2 ≤ prec by omega)
  have finish := WilsonReceivedCloseOrdinaryScale.finish temper.1 temper.2 temp.1 temp.2 cash₀
    (mul_nonneg (by norm_num : (0:ℝ)≤3) unit₀) en (inv_nonneg.mpr (mul_nonneg temp.1.le (L.salary.positive A).le))
    (inv_nonneg.mpr (mul_nonneg temp.1.le (L.salary.positive B).le)) growth (bill A (by simp)) (bill B (by simp))
    (show q+1+2*(2*D₀+2) ≤ order+1 by omega) invoice
  have revenue := (eventually_atTop.mp (WilsonReceivedCloseSourceCalendar.reporter_fee R simple
    (nonneg cash₀ unit₀ q D₀) ep)).choose_spec b wait N per top.le
  change err ≤ _
  apply finish.trans
  change fee cash unit q D₀*base^(q+1) ≤ ε*base^q
  rw [pow_succ,mul_comm (base^q) base,←mul_assoc]
  exact mul_le_mul_of_nonneg_right revenue (pow_nonneg temper.1.le _)

end YM.Integration.WilsonReceivedCloseOrdinaryPurchase
