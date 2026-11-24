import YM.Integration.WilsonReceivedCloseFaceBudget
import YM.Integration.WilsonReceivedCloseOrdinaryPurchase

/-! Every occupied face and its full finite logarithmic polynomial on one original Wilson post. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseFaceIncome
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


def Earned (P₀ : P b mb source) (top : b<N) (span : ℕ) (H angleCap : ℝ)
    (active : Finset V) (arity : ℕ) (price tolerance : ℝ) : Prop :=
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
        let T := Order.value (g (i+1):ℂ) (Order.logMarked W)
        Y.part (Stock.census V).quiet=1 ∧
        ∀ s : (Stock.census V).Mode, s.val ⊆ active → s.val.card ≤ arity →
          let mass := WilsonIndependentOrdinaryPairGrade.mass
            (WilsonIndependentOrdinaryPairGrade.slot s (Order.render (Order.logMarked W)))
          ‖(Order.logTo (Fintype.card V) Y-T).part s‖ ≤ tolerance ∧
          g (i+1)*(Poly.toll L.w s*mass) ≤ 1 ∧
          (∀ y : ℂ, ‖y‖ ≤ 1 →
            g (i+1)*(Poly.toll L.w s*‖(Order.value y (Order.logMarked W)).part s‖) ≤ 1) ∧
          mass ≤ (3*(g b)⁻¹)*price^s.val.card

local notation "requested" cash:max x:max a:max prec:max D:max => cash*(x^(-(1:ℝ))*x^(-(1:ℝ)))*x^(prec-2*D*a)
local notation "capPrice" unit:max x:max D:max => unit*(x⁻¹)^(2*D+1)
local notation "census" => Stock.census V

theorem original (P₀ : P b mb source) (top : b<N) (simple : G.Simple)
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ) (kfit : k ≤ R.alloy.B.a.clock.J m)
    (protection : ∀ x k : ℕ, k ≤ x → ∀ β : ℝ, R.alloy.delay.betaEntry x ≤ β →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹^2) ≤ β)
    (law : VowsR.LawScroll G φ) (chamber : VowsR.Chamber law R.kit D Q books)
    (fund : Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (active : Finset V) (arity q prec D₀ span : ℕ) (cash unit ε H angleCap : ℝ)
    (cash₀ : 0 ≤ cash) (ep : 0 < ε) (hc : 0 ≤ angleCap) (reserve : 2*D₀*arity+q+3 ≤ prec)
    (width : V→ℝ) (oneAt : ∀ v ∈ active, width v=1)
    (sold : WilsonReceivedCloseNamedWallet.Sold R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      mb source P₀ active (capPrice unit (g b) D₀))
    (paid : WilsonReceivedCloseSlate.Paid R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      mb source P₀ top arity span H angleCap width (fun _=>requested cash (g b) arity prec D₀))
    (birthCalendar : (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose ≤ b)
    (cooled : (eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose ≤ b)
    (selected : (eventually_atTop.mp (WilsonReceivedLogWindow.original R simple D φ protection grades
      order shelf k seats span H angleCap hc)).choose ≤ m)
    (wait : (eventually_atTop.mp (WilsonReceivedCloseSourceCalendar.reporter_fee R simple cash₀ ep)).choose ≤ b) :
    Earned R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb source P₀ top span H angleCap
      active arity (capPrice unit (g b) D₀) (ε*(g b)^q) := by
  intro i ib mi
  obtain ⟨L,trace,readings⟩ := paid i ib mi
  have raw := (sold i ib mi L trace).1
  have stocks (s : (census).Mode) (good:s.val⊆active) : (Poly.toll L.w s)⁻¹ ≤ (capPrice unit (g b) D₀)^s.val.card :=
    WilsonReceivedCloseFaceBudget.product (L.salary.positive) s good raw
  refine ⟨L,trace,stocks,?_⟩
  intro x F tag u z B angle tested inside U healthy Y bank program W T
  letI := L.modelCount
  let base := g b
  let heat := g (i+1)
  let E := requested cash base arity prec D₀
  have cold := (eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose_spec b cooled N per top.le
  have positive : 0 < heat := by
    have axis := (R.makes.wilson.represents N per (i+1) (by omega)).band.1
    have hat := zero_lt_one.trans (Extension.UV.hat_positive simple R.alloy.B.a (i+1))
    change 0 < (Real.sqrt (R.family.path.β N per (i+1)))⁻¹
    apply inv_pos.mpr
    apply Real.sqrt_pos.mpr
    exact (half_pos hat).trans_le axis
  have fee := (eventually_atTop.mp (WilsonReceivedCloseSourceCalendar.reporter_fee R simple cash₀ ep)).choose_spec
    b wait N per top.le
  have bought : E ≤ ε*base^q := by
    apply (WilsonReceivedCloseOrdinaryScale.booked cold.1 (by linarith only [cold.1,cold.2]) cash₀
      (by omega : 2*D₀*arity+(q+1)+2 ≤ prec)).trans
    rw [pow_succ,mul_comm (base^q) base,←mul_assoc]
    exact mul_le_mul_of_nonneg_right fee (pow_nonneg cold.1.le _)
  have edge := WilsonReceivedCloseOrdinaryScale.inverse R simple (per:=per) ib top birthCalendar
  have literal := congrFun (WilsonOriginalReceivedChain.report R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i mi (read i ib) L x) U
  have quiet : Y.part (census).quiet=1 :=
    (congrArg (fun d=>((((Ψ i).eval U:ℂ)⁻¹) • d).part (census).quiet) literal).trans
      (WilsonReceivedOrdinaryHearing.clear _ x U healthy)
  have unitW : Order.UnitLeading W := Assembly.prescription_unit ..
  have all := (eventually_atTop.mp (WilsonReceivedLogWindow.original R simple D φ protection grades order shelf k
    seats span H angleCap hc)).choose_spec i (selected.trans mi) hk (kfit.trans (R.alloy.B.a.fits.mono mi)) Q
      π Γ Ψ course books law chamber fund mi (ib.trans_lt top) ahead actors pieces (read i ib) L x u z tested inside F tag
  refine ⟨quiet,?_⟩
  intro s good size mass
  have signed : ‖(Order.logTo (Fintype.card V) Y-T).part s‖ ≤ ε*base^q := by
    rcases s.val.eq_empty_or_nonempty with empty|full
    · have blank : s=(census).quiet := Subtype.ext empty
      rw [blank,Extra.Trajectories.part_sub,WilsonReceivedCloseFaceBudget.empty_physical Y quiet,
        show T.part (census).quiet=0 from WilsonReceivedCloseFaceBudget.empty_finite W unitW (heat:ℂ)]
      simpa only [sub_zero,norm_zero] using mul_nonneg ep.le (pow_nonneg cold.1.le q)
    · have one : Poly.toll width s=1 := Finset.prod_eq_one fun v hv=>oneAt v (good hv)
      have loan := readings x F tag u z tested inside healthy s size full
      change Poly.toll width s * ‖(Order.logTo (Fintype.card V) Y-T).part s‖ ≤ E at loan
      rw [one,one_mul] at loan
      exact loan.trans bought
  obtain ⟨full,each⟩ := all s
  have testedMass : heat*(Poly.toll L.w s*mass) ≤ 1 := full
  exact ⟨signed,testedMass,each,WilsonReceivedCloseFaceBudget.mass positive cold.1
    (Finset.prod_pos fun v _=>L.salary.positive v) edge (stocks s good) testedMass⟩

end YM.Integration.WilsonReceivedCloseFaceIncome
