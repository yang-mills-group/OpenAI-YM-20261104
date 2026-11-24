import YM.Integration.WilsonReceivedCloseOrdinaryGrade
import YM.Integration.WilsonReceivedCloseFaceIncome
import YM.Integration.WilsonReceivedOrdinaryPanel

/-! Complete ordinary moments of the actual close source on its shared Wilson history. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseOrdinaryRoster
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


def Served (P₀ : P b mb source) (top : b<N) (span : ℕ) (H angleCap : ℝ)
    (active : Finset V) (arity : ℕ) (price connected tolerance : ℝ) : Prop :=
    ∀ i (ib : i ≤ b) (mi : m ≤ i), ∃ L : P i mi (read i ib),
      WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
        mb source P₀ i mi (read i ib) L ∧
      (∀ s : (Stock.census V).Mode, s.val ⊆ active → (Poly.toll L.w s)⁻¹ ≤ price^s.val.card) ∧
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
        Y.part (Stock.census V).quiet=1 ∧
        ∀ s : (Stock.census V).Mode, s.val ⊆ active → s.val.card ≤ arity →
          ‖Y.part s-(Order.value (g (i+1):ℂ) (Order.ratio W)).part s‖ ≤ tolerance ∧
          ‖(Order.logTo (Fintype.card V) Y-Order.value (g (i+1):ℂ) (Order.logMarked W)).part s‖ ≤ connected ∧
          g (i+1)*(Poly.toll L.w s*WilsonIndependentOrdinaryPairGrade.mass
            (WilsonIndependentOrdinaryPairGrade.slot s (Order.render (Order.logMarked W)))) ≤ 1

local notation "stars" => Stock.census V

theorem original (P₀ : P b mb source) (top : b<N) (simple : G.Simple)
    (active : Finset V) (a d q degree span : ℕ) (cap unit H angleCap ε : ℝ)
    (unit₁ : 1 ≤ unit) (dp : 0 < ε) (fit : a+(q+d*a+1) ≤ order+1)
    (income : WilsonReceivedCloseFaceIncome.Earned R hk D Q π Γ Ψ books ahead actors pieces grades order shelf
      seats mb source P₀ top span H angleCap active a (unit*((g b)⁻¹)^d) ((g b)^(q+d*a+1+a)))
    (close : PaceR.Close R degree cap m b)
    (clock : (eventually_atTop.mp (WilsonReceivedCloseChainFunding.upper R simple degree cap)).choose ≤ b)
    (birthCalendar : (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose ≤ b)
    (cooled : (eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose ≤ b)
    (wait : (eventually_atTop.mp (WilsonReceivedCloseSourceCalendar.reporter_fee R simple
      (WilsonReceivedCloseOrdinaryGrade.nonneg (stars) a d q (zero_le_one.trans unit₁)) dp)).choose ≤ b) :
    Served R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb source P₀ top span H angleCap
      active a (unit*((g b)⁻¹)^d) ((g b)^(q+d*a+1+a)) (ε*(g b)^q) := by
  intro i ib mi
  obtain ⟨L,record,stocks,readings⟩ := income i ib mi
  refine ⟨L,record,stocks,?_⟩
  letI := L.modelCount
  let base := g b
  let heat := g (i+1)
  let u₀ := q+d*a+1
  let E := base^(u₀+a)
  let price := unit*(base⁻¹)^d
  let w (v:V) := min 1 (L.w v)
  have wp (v:V) : 0<w v := lt_min zero_lt_one (L.salary.positive v)
  have cold := (eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose_spec b cooled N per top.le
  have low : base ≤ 1 := by linarith only [cold.1,cold.2]
  have cost₁ : 1 ≤ price := one_le_mul_of_one_le_of_one_le unit₁ (one_le_pow₀ (one_le_inv_iff₀.mpr ⟨cold.1,low⟩))
  have bands := (eventually_atTop.mp (WilsonReceivedCloseChainFunding.upper R simple degree cap)).choose_spec b clock m mb close N per top.le
  have edge := bands (i+1) (by omega) (by omega)
  have reverse := WilsonReceivedCloseOrdinaryScale.inverse R simple (per:=per) ib top birthCalendar
  have cost (v:V) (hv:v∈active) : (w v)⁻¹ ≤ price := by
    have hear := stocks ((stars).fire v) (by simpa only [Marker.Census.fire,Finset.singleton_subset_iff] using hv)
    have fee : (L.w v)⁻¹ ≤ price := by
      simpa only [Poly.toll,Marker.Census.fire,Finset.prod_singleton,Finset.card_singleton,pow_one] using hear
    by_cases hi : 1 ≤ L.w v
    · simpa only [w,min_eq_left hi,inv_one] using cost₁
    · simpa only [w,min_eq_right (le_of_not_ge hi)] using fee
  have one (t:(stars).Mode) : Poly.toll w t ≤ 1 := by
    calc
      _ ≤ ∏ _v∈t.val,(1:ℝ) := Finset.prod_le_prod (fun v _=>(wp v).le) (fun v _=>min_le_left ..)
      _ = 1 := by simp
  have smaller (t:(stars).Mode) : Poly.toll w t ≤ Poly.toll L.w t :=
    Finset.prod_le_prod (fun v _=>(wp v).le) (fun v _=>min_le_right ..)
  intro x F tag u z B angle tested inside U healthy Y bank program W
  obtain ⟨quiet,rows⟩ := readings x F tag u z tested inside healthy
  refine ⟨quiet,?_⟩
  intro s named count
  have settled := rows s named count
  refine ⟨?_,settled.1,settled.2.1⟩
  have raw := WilsonReceivedOrdinaryPanel.measured_on Y quiet W (Bulk.fk_unit ..) (Bulk.fk_sym ..) w wp heat E
    edge.1 (edge.2.trans cold.2) (pow_nonneg cold.1.le _) s
    (fun v hv=>by
      have bill := (rows v.val (hv.trans named) ((Finset.card_le_card hv).trans count)).2.1
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (smaller v.val)
        (IterationFour.Series.mass_nn _)) edge.1.le).trans bill)
    (fun v hv=>by
      have bill := (rows v.val (hv.trans named) ((Finset.card_le_card hv).trans count)).1
      exact (mul_le_of_le_one_left (norm_nonneg _) (one v.val)).trans bill)
    u₀ (by dsimp only [u₀]; omega)
  let full := (∑ h∈shards (stars) s,(h.val.card:ℝ)*E*(heat⁻¹+E)^h.val.card)+heat^u₀*(shards (stars) s).card
  have bn : 0 ≤ full := (mul_nonneg (Poly.worth wp s).le (norm_nonneg _)).trans raw
  let error := ‖Y.part s-(Order.value (heat:ℂ) (Order.ratio W)).part s‖
  have purchased : error ≤ price^s.val.card*full := by
    have width := Poly.worth wp s
    have restored := WilsonReceivedCloseFaceBudget.product wp s named cost
    calc
      _ = (Poly.toll w s)⁻¹*(Poly.toll w s*error) := by rw [←mul_assoc,inv_mul_cancel₀ width.ne',one_mul]
      _ ≤ (Poly.toll w s)⁻¹*full := mul_le_mul_of_nonneg_left raw (inv_nonneg.mpr width.le)
      _ ≤ _ := mul_le_mul_of_nonneg_right restored bn
  have bound := WilsonReceivedCloseOrdinaryGrade.earned (stars) s a d q unit₁ cold.1 low edge.1 edge.2 reverse count purchased
  apply bound.trans
  have fee := (eventually_atTop.mp (WilsonReceivedCloseSourceCalendar.reporter_fee R simple
    (WilsonReceivedCloseOrdinaryGrade.nonneg (stars) a d q (zero_le_one.trans unit₁)) dp)).choose_spec b wait N per top.le
  rw [pow_succ,mul_comm (base^q) base,←mul_assoc]
  exact mul_le_mul_of_nonneg_right fee (pow_nonneg cold.1.le _)

end YM.Integration.WilsonReceivedCloseOrdinaryRoster
