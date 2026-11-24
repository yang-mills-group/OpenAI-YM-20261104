import YM.Integration.WilsonOriginalPointCompactCash
import YM.Integration.WilsonMarkedFixedPoleGross

/-! A single wallet buys the three original point compacts and their full countable failure sheet. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalThreeCompactWallet
open Function Finset Lattice Laurent RG Wilson Marker Gauge
open Push Push.AbsoluteSums Paths Animals ConnectedActivityE6 QuadraticLocal QuadraticLocal.Sunrise
open QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder AllOrder.Ink QuadraticLocal.Affinity
open WilsonOriginalPointCompactRoster WilsonOriginalPointCompactCash
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{I:Type}[Fintype I]{q:ℕ}{σ:ℝ}
  (owner:I→Fin 3) (grades:Fin 3→ℕ) (sites:Fin 3→Site n)
  (T:(i:I)→WilsonOlderFreshGraphSlate.Copy G (grades (owner i)) q σ)
  (A:Fin 3→Set ℂ) (charge:I→ℂ)
local notation "J" => Stock.census (Fin 3)
local notation "M" => rows owner grades sites T A charge
local notation "budget" => WilsonOriginalPointCompactSalary.invoice owner grades sites T charge
local notation "pole" => (∑v:Fin 3,grades v)+1

def fee (G:Gauge) (p:BudgetPoint) (U g ξ:ℝ) (order seats shelf d:ℕ) : ℝ :=
  (2^(order+shelf+1)/g^d)*Invoice.price p U (order+shelf+1) seats (p.supportExponent+1) ξ G

theorem original (p:BudgetPoint) {b g U ξ cap ticket:ℝ} (bp:0<b)
    (ticket0:0 ≤ ticket) (fares:∀i:I,(∑j,(T i).fare j) ≤ ticket)
    (charges:∀i:I,‖charge i‖ ≤ cap) (σ0:0 ≤ σ) (unit:∀v (t:ℂ),t∈A v→‖t‖ ≤ 1)
    (order seats shelf:ℕ) (qorder:q ≤ order) (slots:3 ≤ seats) (gradesFit:(∑v:Fin 3,grades v) ≤ shelf)
    (fund:Invoice.Supports p U (p.supportExponent+1) g σ ξ) :
    let size:=ceiling I cap ticket
    let price:=fee G p U g ξ order seats shelf (pole)
    let raw:Fin 3→ℝ:=fun _=>b/(1+size)
    let shrink:=1+|price| * b/Willow.haloSlack p.B
    let w:Fin 3→ℝ:=fun v=>raw v/shrink
    (∀v,0<raw v) ∧ 1 ≤ shrink ∧ (∀v,0<w v) ∧ (budget) w ≤ b ∧
    (∀v,(w v)⁻¹=(1+size)*(b⁻¹+|price|/Willow.haloSlack p.B)) ∧
    Scene.Armada M w grades σ ((budget) w) order seats shelf ∧
    WilsonRootedKioskOccupiedSlip.Gross (rendered M p g) raw p.B (p.supportExponent+1) (price*((budget) raw)) ∧
    shrink⁻¹*(price*((budget) raw)) ≤ Willow.haloSlack p.B := by
  intro size price raw shrink w
  let sumFees:=∑i:I,(1+‖charge i‖)*(∑j,(T i).fare j)
  have sum0:0 ≤ sumFees:=by
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (by positivity)
    rw [←own_source owner grades sites T i]
    exact budget_nonneg (WilsonOriginalPointCompactSalary.original_salary owner grades sites T A i σ0)
  have fit:sumFees ≤ size:=bound owner grades T charge fares charges ticket0
  have size0:0 ≤ size:=sum0.trans fit
  have rad:0<b/(1+size):=div_pos bp (by linarith)
  have identity:(budget) raw=(b/(1+size))*sumFees:=total owner grades sites T charge _
  obtain ⟨used0,used⟩:=share bp size0 sum0 fit
  rw [←identity] at used0 used
  obtain ⟨one,pos,afford,inverse⟩:=restored (gross:=price) bp size0 (Willow.spare_pos p.B) used0 used
  have final:(budget) w ≤ (budget) raw:=by
    rw [WilsonOriginalPointCompactCash.total owner grades sites T charge (b/(1+size)/shrink),identity]
    apply mul_le_mul_of_nonneg_right _ sum0
    exact div_le_self rad.le one
  have reals:=WilsonOriginalPointCompactSalary.stocks owner grades sites T A charge σ0 w (fun _=>pos)
    unit order seats shelf qorder slots gradesFit
  have initial:=WilsonOriginalPointCompactSalary.stocks owner grades sites T A charge σ0 raw (fun _=>rad)
    unit order seats shelf qorder slots gradesFit
  have width (s:(J).Mode) : (∑v∈s.val,grades v)+1 ≤ (pole):=by
    have sub:∑v∈s.val,grades v ≤ ∑v:Fin 3,grades v:=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=>Nat.zero_le _)
    omega
  have gross:=WilsonMarkedFixedPoleGross.landed M raw grades p initial fund (pole) width
  exact ⟨fun _=>rad,one,fun _=>pos,final.trans used,fun _=>inverse,reals,
    by simpa only [price,fee,mul_assoc] using gross,afford⟩

end YM.Integration.WilsonOriginalThreeCompactWallet
