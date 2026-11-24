import YM.Integration.WilsonReceivedCloseSlate
import YM.Integration.WilsonReceivedCenteredChart

/-! The ordinary product-minus-counterterm from the jointly heard finite Wilson close history. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseOrdinary
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


/-- The four logarithmic readings have the same Wilson numerator, vacuum divisor, station, tree,
angle and independent bank. The remaining kernels belong to the two finite singleton polynomials. -/
theorem original (P₀ : P b mb source) (top : b<N) (a span : ℕ) (H angleCap : ℝ) (width : V→ℝ)
    (cap : (Stock.census V).Mode → ℝ)
    (paid : WilsonReceivedCloseSlate.Paid R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      mb source P₀ top a span H angleCap width cap) (wp : ∀v,0<width v) (room : 2≤a)
    (A B C : V) (s : (Stock.census V).Mode) (different : A ≠ B) (pair : s.val={A,B}) :
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
        flags (Ψ i).p.threshold U=∅ → ‖(g (i+1):ℂ)‖≤1 →
        let Y := (((Ψ i).eval U:ℂ)⁻¹) • LocalComparison.actualPush R.family N per i ((read i ib) x) U
        let bank := Air.craft L.model (fun s => (L.model s).paint x) grades (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
        let program := (RunFormalChain.fromRun R).step N i per (ib.trans_lt top)
        let W := Bulk.Fk program F tag bank angle order
        let Z := Order.value (g (i+1):ℂ) (Order.ratio W)
        let T := Order.value (g (i+1):ℂ) (Order.logMarked W)
        let cost := fun t => cap t / Poly.toll width t
        let axis := (Stock.census V).fire
        let singleton := fun v=>WilsonIndependentOrdinaryPairGrade.slot (axis v) (Order.render (Order.ratio W))
        ‖(Y.part s-Y.part (axis C))-(Z.part s-Z.part (axis C))‖ ≤
          (cost s+cost (axis C)+cost (axis A)*(‖T.part (axis B)‖+cost (axis B))+‖T.part (axis A)‖*cost (axis B)) +
          ‖(g (i+1):ℂ)‖^(order+1)*(WilsonIndependentOrdinaryPairGrade.mass (singleton A)*WilsonIndependentOrdinaryPairGrade.mass (singleton B)) := by
  intro i ib mi
  obtain ⟨L,trace,loan⟩ := paid i ib mi
  refine ⟨L,trace,?_⟩
  intro x F tag u z Q₀ angle tested inside U healthy small Y bank program W Z T cost axis singleton
  letI := L.modelCount
  let invVac := (((Ψ i).eval U):ℂ)⁻¹
  have unitY : Y.part (Stock.census V).quiet=1 := by
    have readout := congrFun (WilsonOriginalReceivedChain.report R hk D Q π Γ Ψ books ahead actors pieces grades
      order shelf seats i mi (read i ib) L x) U
    exact (congrArg (fun d => (invVac • d).part (Stock.census V).quiet) readout).trans
      (WilsonReceivedOrdinaryHearing.clear _ x U healthy)
  have normalized : Order.UnitLeading W := Assembly.prescription_unit ..
  have symmetric : Order.Symmetric W := Assembly.prescription_sym (hv := program.positive F tag) ..
  apply WilsonReceivedOrdinaryHearing.priced Y W unitY normalized symmetric (g (i+1):ℂ) small A B C s different pair cost
  intro t ht
  have endpoints : s.val.card≤a ∧ s.val.Nonempty := by
    rw [pair]
    exact ⟨(Finset.card_insert_le _ _).trans (by simp; omega),Finset.insert_nonempty _ _⟩
  have one (v:V) : ((Stock.census V).fire v).val.card≤a ∧ ((Stock.census V).fire v).val.Nonempty := by
    change ({v}:Finset V).card≤a ∧ ({v}:Finset V).Nonempty
    rw [Finset.card_singleton]
    exact ⟨by omega,Finset.singleton_nonempty _⟩
  have admissible : t.val.card≤a ∧ t.val.Nonempty := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact endpoints
    · exact one C
    · exact one A
    · exact one B
  have receipt := loan x F tag u z tested inside healthy t admissible.1 admissible.2
  have tp : 0 < Poly.toll width t := Finset.prod_pos fun i _=>wp i
  apply (le_div_iff₀ tp).mpr
  exact (le_of_eq (mul_comm _ _)).trans receipt

end YM.Integration.WilsonReceivedCloseOrdinary
