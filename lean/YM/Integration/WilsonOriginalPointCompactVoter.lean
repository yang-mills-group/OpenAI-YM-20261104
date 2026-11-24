import YM.Integration.WilsonOriginalPointCompactProgram

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPointCompactVoter
open Lattice RG QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder AllOrder.Ink
open WilsonOriginalPointCompactRoster
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {I:Type} [Fintype I] {q:ℕ} {σ:ℝ}
  (owner:I→Fin 3) (grades:Fin 3→ℕ) (sites:Fin 3→Site n)
  (T:(i:I)→WilsonOlderFreshGraphSlate.Copy G (grades (owner i)) q σ)
  (A:Fin 3→Set ℂ) (charge:I→ℂ)

theorem original (σ0:0 ≤ σ) (unit:∀v (t:ℂ),t∈A v→‖t‖ ≤ 1) (order seats stage vac shelf:ℕ)
    (size:3 ≤ seats) (reserve:(∑v:Fin 3,grades v) ≤ shelf)
    (qo:q ≤ order) (qs:q ≤ shelf) (start:order+1 ≤ stage) (expense:order+(∑v:Fin 3,grades v) ≤ Burn.horizon vac+2) :
    Cruise.Voter (rows owner grades sites T A charge) σ order seats stage vac shelf:=by
  obtain ⟨w,_,_,_,_,voter⟩:=WilsonOriginalPointCompactProgram.original owner grades sites T A charge σ0 unit
    (b:=1) zero_lt_one (order:=order) (seats:=seats) (stage:=stage) (vac:=vac) (shelf:=shelf) size reserve qo qs start expense
  exact voter

end YM.Integration.WilsonOriginalPointCompactVoter
