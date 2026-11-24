import YM.Integration.WilsonOriginalFundedCompactProduct
import YM.Integration.WilsonOriginalPointCompactVoter

/-! The declared compact material and the complete invoice are fixed before post selection. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalThreeCompactCommission
open Function Finset Lattice Laurent RG Wilson Marker Gauge
open Push Push.AbsoluteSums Paths Animals ConnectedActivityE6 QuadraticLocal QuadraticLocal.Sunrise
open QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder AllOrder.Ink QuadraticLocal.Affinity
open WilsonOriginalPointCompactRoster WilsonOriginalPointCompactCash WilsonOriginalThreeCompactProduct
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{I:Type}[Fintype I]{q:ℕ}{σ:ℝ}
  (owner:I→Fin 3) (grades:Fin 3→ℕ) (sites:Fin 3→Site n)
  (T:(i:I)→WilsonOlderFreshGraphSlate.Copy G (grades (owner i)) q σ)
  (A:Fin 3→Set ℂ) (charge:I→ℂ)
local notation "M" => rows owner grades sites T A charge
local notation "budget" => WilsonOriginalPointCompactSalary.invoice owner grades sites T charge
local notation "pole" => (∑v:Fin 3,grades v)+1

structure Sale (p:BudgetPoint) (b g cap ticket price:ℝ) (order seats shelf:ℕ) where
  raw : Fin 3→ℝ
  shrink : ℝ
  raw_pos : ∀v,0<raw v
  one : 1 ≤ shrink
  paid : (budget) (fun v=>raw v/shrink) ≤ b
  inverse : ∀v,(raw v/shrink)⁻¹=(1+ceiling I cap ticket)*(b⁻¹+|price|/Willow.haloSlack p.B)
  stock : Scene.Armada M (fun v=>raw v/shrink) grades σ
    ((budget) (fun v=>raw v/shrink)) order seats shelf
  gross : WilsonRootedKioskOccupiedSlip.Gross (rendered M p g) raw p.B (p.supportExponent+1) (price*((budget) raw))
  restored : shrink⁻¹*(price*((budget) raw)) ≤ Willow.haloSlack p.B
  held : ∀t (u:Config G n), Poly.pass (Spill.Foundry.uncut M g t u)=
    ∏v:Fin 3,(1+Poly.send ((Stock.census (Fin 3)).fire v) (value owner
      (fun z=>WilsonOriginalPointCompactFaces.amount owner grades sites T A charge z g t u) v))

theorem original (p:BudgetPoint) {b g U ξ cap ticket:ℝ} (bp:0<b)
    (ticket0:0 ≤ ticket) (fares:∀i:I,(∑j,(T i).fare j) ≤ ticket)
    (charges:∀i:I,‖charge i‖ ≤ cap) (σ0:0 ≤ σ) (unit:∀v (t:ℂ),t∈A v→‖t‖ ≤ 1)
    (order seats shelf:ℕ) (qorder:q ≤ order) (slots:3 ≤ seats) (fit:(∑v:Fin 3,grades v) ≤ shelf)
    (fund:Invoice.Supports p U (p.supportExponent+1) g σ ξ) :
    Nonempty (Sale owner grades sites T A charge p b g cap ticket
      (WilsonOriginalThreeCompactWallet.fee G p U g ξ order seats shelf (pole)) order seats shelf) := by
  obtain ⟨hr,hs,_,paid,inverse,stock,gross,fee⟩:=WilsonOriginalThreeCompactWallet.original
    owner grades sites T A charge p bp ticket0 fares charges σ0 unit order seats shelf qorder slots fit fund
  exact ⟨⟨_,_,hr,hs,paid,inverse,stock,gross,fee,
    WilsonOriginalFundedCompactProduct.current owner grades sites T A charge p gross hr σ0 unit order seats
      shelf qorder slots fit fund⟩⟩

end YM.Integration.WilsonOriginalThreeCompactCommission
