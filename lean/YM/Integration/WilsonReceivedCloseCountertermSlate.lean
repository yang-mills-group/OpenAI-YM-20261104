import YM.Integration.WilsonReceivedCloseCounterterm
import YM.Integration.WilsonReceivedCloseOrdinaryPurchase

/-! One original dated post for the complete signed finite filed counterterm. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseCountertermSlate
open WilsonReceivedCloseOrdinaryPurchase
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
    (active : Finset V) (width : V → ℝ) (budget tolerance : ℝ) : Prop :=
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
        let axis := (Stock.census V).fire
        (∀ v, width v * ‖Y.part (axis v)-Z.part (axis v)‖ ≤ budget) ∧
        ∀ A ∈ active, ∀ B ∈ active, A≠B → ∀ s : (Stock.census V).Mode, s.val={A,B} →
          ∀ counter : Finset V, counter ⊆ active → ∀ c : V → ℂ,
            let err := ‖WilsonReceivedCloseCounterterm.compensated Y s counter c-
              WilsonReceivedCloseCounterterm.compensated Z s counter c‖
            err ≤ tolerance+budget/width A+∑ v ∈ counter, ‖c v‖*(budget/width v) ∧
            err ≤ (2+∑ v ∈ counter, ‖c v‖)*tolerance

local notation "stage" => (budgetR R b)^2*(budgetR R (b+1))^7
local notation "requested" cash:max x:max prec:max D:max => cash*(x^(-(1:ℝ))*x^(-(1:ℝ)))*x^(prec-2*D*2)
local notation "stars" => Stock.census V

theorem original (P₀ : P b mb source) (top : b<N) (simple : G.Simple)
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ) (kfit : k ≤ R.alloy.B.a.clock.J m)
    (protection : ∀ x k : ℕ, k ≤ x → ∀ β : ℝ, R.alloy.delay.betaEntry x ≤ β →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹^2) ≤ β)
    (law : VowsR.LawScroll G φ) (chamber : VowsR.Chamber law R.kit D Q books)
    (fund : Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (active : Finset V)
    (q prec D₀ span degree : ℕ) (cash unit ε H angleCap cap : ℝ)
    (cash₀ : 0≤cash) (unit₀ : 0≤unit) (ep : 0<ε) (hc : 0≤angleCap) (cn : 0≤cap)
    (grade : q+6*D₀+5 ≤ prec) (testedOrder : prec ≤ order)
    (width : V→ℝ) (wp : ∀v,0<width v)
    (enrolled : ∀v ∈ active, width v=1)
    (birth : ∀v ∈ active, 1 ≤ stage^2*(unit*((g b)⁻¹)^(2*D₀))*P₀.w v)
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
    Heard R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb source P₀ top span H angleCap
      active width (requested cash (g b) prec D₀) (ε*(g b)^q) := by
  intro i ib mi
  obtain ⟨L,record,loan⟩ := paid i ib mi
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
  have bill (v:V) (seen : v ∈ active) :
      (heat*L.w v)⁻¹ ≤ 3*unit*(base⁻¹)^(2*D₀+2) :=
    WilsonReceivedCloseOrdinaryScale.singleton D₀ temper.1 u₀ (L.salary.positive v) unit₀ comparable capD
      (birth v seen) (radius v)
  intro x F tag u z Q₀ angle tested inside U healthy Y bank program W Z axis
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
  letI := L.modelCount
  have readout := congrFun (WilsonOriginalReceivedChain.report R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i mi (read i ib) L x) U
  have quiet : Y.part (stars).quiet=1 :=
    (congrArg (fun d => ((((Ψ i).eval U:ℂ)⁻¹) • d).part (stars).quiet) readout).trans
      (WilsonReceivedOrdinaryHearing.clear _ x U healthy)
  have normalized : Order.UnitLeading W := Assembly.prescription_unit ..
  have symmetric : Order.Symmetric W := Assembly.prescription_sym (hv := program.positive F tag) ..
  have singleSize (v : V) : (axis v).val.card ≤ 2 ∧ (axis v).val.Nonempty := by
    change ({v}:Finset V).card ≤ 2 ∧ ({v}:Finset V).Nonempty
    simp
  have singlePrice (v : V) : width v*‖Y.part (axis v)-Z.part (axis v)‖ ≤ E := by
    have paidOne := loan x F tag u z tested inside healthy (axis v) (singleSize v).1 (singleSize v).2
    change Poly.toll width (axis v)*‖(logTo (Fintype.card V) Y-T).part (axis v)‖ ≤ E at paidOne
    have reading := WilsonReceivedCloseCounterterm.singleton Y quiet W normalized symmetric (heat:ℂ) v
    change (logTo (Fintype.card V) Y-T).part (axis v)=Y.part (axis v)-Z.part (axis v) at reading
    rw [reading] at paidOne
    simpa only [axis,Poly.toll,Marker.Census.fire,Finset.prod_singleton] using paidOne
  refine ⟨singlePrice,?_⟩
  intro A inA B inB different s pair counter covered c fullErr
  have fs : Poly.toll width s=1 := by
    unfold Poly.toll
    rw [pair]
    simp [different,enrolled A inA,enrolled B inB]
  have fire (v : V) (hv : v ∈ active) : Poly.toll width (axis v)=1 := by
    simpa only [axis,Poly.toll,Marker.Census.fire,Finset.prod_singleton] using enrolled v hv
  let err := ‖(Y.part s-Y.part (axis A))-(Z.part s-Z.part (axis A))‖
  have entered : err ≤ E+E+E*(mean B+E)+mean A*E+heat^(order+1)*(mass' A*mass' B) := by
    have pairSize : s.val.card ≤ 2 ∧ s.val.Nonempty := by
      rw [pair]
      exact ⟨(Finset.card_insert_le _ _).trans (by simp),Finset.insert_nonempty _ _⟩
    have all (t : (stars).Mode) (ht:t ∈ ({s,axis A,axis A,axis B}:Finset _)) :
        (Poly.toll width t=1) ∧ t.val.card ≤ 2 ∧ t.val.Nonempty := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact ⟨fs,pairSize⟩
      · exact ⟨fire A inA,singleSize A⟩
      · exact ⟨fire A inA,singleSize A⟩
      · exact ⟨fire B inB,singleSize B⟩
    have signed : ∀ t ∈ ({s,axis A,axis A,axis B}:Finset _),
        ‖(logTo (Fintype.card V) Y-T).part t‖ ≤ E := by
      intro t ht
      obtain ⟨white,size,nonempty⟩ := all t ht
      have row := loan x F tag u z tested inside healthy t size nonempty
      change Poly.toll width t*‖(logTo (Fintype.card V) Y-T).part t‖ ≤ E at row
      simpa only [white,one_mul] using row
    have raw : err ≤ E+E+E*(mean B+E)+mean A*E+‖(heat:ℂ)‖^(order+1)*(mass' A*mass' B) :=
      WilsonReceivedOrdinaryHearing.priced Y W quiet normalized symmetric (heat:ℂ) gsmall A B A s different
        pair (fun _=>E) signed
    simpa only [node] using raw
  have mb₀ : 0 ≤ mass' B := Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  have invoice := WilsonReceivedOrdinaryPayment.numeric temp.1 (L.salary.positive A) (L.salary.positive B)
    en en mb₀ (moment A).2 (moment B).2 (moment A).1 (moment B).1 entered
  have growth := WilsonReceivedCloseOrdinaryScale.booked temper.1 (by linarith only [temper.1,temper.2])
    cash₀ (show 2*D₀*2+(q+1+(2*D₀+2))+2 ≤ prec by omega)
  have finish := WilsonReceivedCloseOrdinaryScale.finish temper.1 temper.2 temp.1 temp.2 cash₀
    (mul_nonneg (by norm_num : (0:ℝ)≤3) unit₀) en (inv_nonneg.mpr (mul_nonneg temp.1.le (L.salary.positive A).le))
    (inv_nonneg.mpr (mul_nonneg temp.1.le (L.salary.positive B).le)) growth (bill A inA) (bill B inB)
    (show q+1+2*(2*D₀+2) ≤ order+1 by omega) invoice
  have revenue := (eventually_atTop.mp (WilsonReceivedCloseSourceCalendar.reporter_fee R simple
    (nonneg cash₀ unit₀ q D₀) ep)).choose_spec b wait N per top.le
  have feePaid : fee cash unit q D₀*base^(q+1) ≤ ε*base^q := by
    rw [pow_succ,mul_comm (base^q) base,←mul_assoc]
    exact mul_le_mul_of_nonneg_right revenue (pow_nonneg temper.1.le _)
  have coeff : cash ≤ fee cash unit q D₀ := by
    dsimp [WilsonReceivedCloseOrdinaryPurchase.fee]
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) cash₀)
      (mul_nonneg (by norm_num : (0:ℝ)≤3) unit₀),sq_nonneg cash,
      mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤3) (q+1+2*(2*D₀+2))) (sq_nonneg (3*unit))]
  have smallE : E ≤ ε*base^q := by
    apply growth.trans
    apply le_trans _ feePaid
    exact mul_le_mul coeff (pow_le_pow_of_le_one temper.1.le (by linarith only [temper.1,temper.2])
      (by omega : q+1 ≤ q+1+(2*D₀+2))) (pow_nonneg temper.1.le _) (cash₀.trans coeff)
  have singleAbsolute (v : V) : ‖Y.part (axis v)-Z.part (axis v)‖ ≤ E/width v := by
    rw [le_div_iff₀ (wp v),mul_comm]
    exact singlePrice v
  have pairAbsolute : err ≤ ε*base^q := finish.trans feePaid
  have total := WilsonReceivedCloseCounterterm.linear Y Z A s counter c (ε*base^q)
    (fun v=>E/width v) pairAbsolute (singleAbsolute A) (fun v _=>singleAbsolute v)
  refine ⟨total,?_⟩
  apply total.trans
  rw [enrolled A inA,div_one]
  have each : ∑ v ∈ counter, ‖c v‖*(E/width v) ≤ (∑ v ∈ counter, ‖c v‖)*(ε*base^q) := by
    rw [sum_mul]
    refine sum_le_sum fun v hv=>?_
    rw [enrolled v (covered hv),div_one]
    exact mul_le_mul_of_nonneg_left smallE (norm_nonneg _)
  calc
    ε*base^q+E+∑ v ∈ counter, ‖c v‖*(E/width v) ≤
      ε*base^q+(ε*base^q)+(∑ v ∈ counter, ‖c v‖)*(ε*base^q) := add_le_add (add_le_add le_rfl smallE) each
    _ = _ := by ring

end YM.Integration.WilsonReceivedCloseCountertermSlate
