import YM.Integration.WilsonThermometerSolitaryPeerWage
import YM.Integration.WilsonMeasuredCourseQuietSlots

/-! The two actual ordinary exchange terms transfer fieldwise to the canonical P at their own test wages. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCompanionCoursePeers
open Function Finset Lattice Wilson RG Source QuadraticLocal QuadraticLocal.Earn Marker Ac Push Labels
open QuadraticLocal.Advent QuadraticLocal.Fusion QuadraticLocal.Fusion.Attached Extra.Trajectories RG05Readout
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open WilsonMeasuredCompanionFace WilsonThermometerSolitaryExchange
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)
variable {G:Gauge}{n:Side}{T I I':Type}[Countable I][Countable I']{o:Fin 3→Site n}
omit [Countable I] in
private theorem lodged {a b:BudgetPoint}(same:a=b)(E:Lamps T I G a o (J))(v:Fin 3)(w:Fin 3→ℝ)
    (cash:∀weight:ℝ,E.Paid (wage v w weight) a.B a.supportExponent 1):
    ∃L:Lamps T I G b o (J),(∀weight:ℝ,L.Paid (wage v w weight) b.B b.supportExponent 1) ∧
      ∀x U,L.log x U=E.log x U:=by
  subst b
  exact ⟨E,cash,fun _ _=>rfl⟩

theorem original (R:Run G){f m N p k:ℕ}(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
    (Ψ:∀j,Rep G (R.family.side j p))(course:Concourse R.alloy R.kit R.T π Γ m N p k Ψ)
    (birth:m≤f)(cut:f≤N)(o:Fin 3→Site (R.family.side f p))
    (a:Lamps T I G (Ψ f).p o (J))(b:Lamps T I' G (Ψ f).p o (J))(w:Fin 3→ℝ)
    (hp:∀i,0<w i)(pa:a.Paid w (Ψ f).p.B (Ψ f).p.supportExponent 1)
    (pb:b.Paid w (Ψ f).p.B (Ψ f).p.supportExponent 1)(v:Fin 3):
    let P:=R.family.path.rep N p f
    ∃(ι:Type)(_:Countable ι)(E:Lamps T ι G P.p o (J)),
      (∀h:ℝ,E.Paid (wage v (Stoop.radius w 2) h) P.p.B P.p.supportExponent 1) ∧
      ∀x U,Poly.pass (E.log x U)=peer (fun i=>(a.log x U).part ((J).fire i))
        (fun i=>(b.log x U).part ((J).fire i)) v:=by
  intro P
  obtain ⟨ι,count,E,bill,_free,value⟩:=WilsonThermometerSolitaryPeerWage.original a b w hp _ _
    (Ψ f).p.exponent_pos.le pa pb v
  have eq:=(WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course birth cut).1
  obtain ⟨L,paid,read⟩:=lodged eq.symm E v (Stoop.radius w 2) bill
  exact ⟨ι,count,L,paid,fun x U=>(congrArg Poly.pass (read x U)).trans (value x U)⟩

end YM.Integration.WilsonOriginalCompanionCoursePeers
end
