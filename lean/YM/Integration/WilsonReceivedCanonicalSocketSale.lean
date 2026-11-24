import YM.Integration.WilsonReceivedCanonicalSocketRows
import YM.Integration.WilsonMarkedFixedPoleGross
import YM.Integration.WilsonOriginalPointCompactCash
import YM.Integration.WilsonOriginalThreeCompactWallet
import YM.Integration.WilsonOriginalPointCompactVoter

/-! One before-test price for the chosen unit or raw socket at each real birth. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCanonicalSocketSale
open Function Filter Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Earn QuadraticLocal.Affinity
open PhysicalNext.Repeat.Legato AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP ConnectedActivityE6
open Integration.LocalComparison Advent.Sycamore XSpace QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder.Ink QuadraticLocal.Sunrise
open Push Push.AbsoluteSums Paths Animals
open WilsonOriginalThermometerPalette WilsonThermometerDeclaredSeeds WilsonOriginalStarSceneWords
open WilsonReceivedCanonicalSocketRows (row price charge)
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ)(q:(j:Fin 3)→Choice R d j)(hd:∀j,d j ≤ levels j)
    {n:Side}(o:Fin 3→Site n)(σ:ℝ)
local notation "M" => row R d q hd o σ
local notation "C₀" => WilsonReceivedCanonicalSocketRows.ceiling R d σ
local notation "fee" => WilsonOriginalThreeCompactWallet.fee
local notation "rankQ" j:max => rank R d (entry R d j (q j))

theorem voter {w:Fin 3→ℝ}(pos:∀j,0<w j)(order seats stage vac shelf book:ℕ)
    (fit:∀j,rankQ j ≤ order)(three:3 ≤ seats)(room:14 ≤ shelf)(start:order+1 ≤ stage)(budget:order+14 ≤ Burn.horizon vac+2)
    (ord:order ≤ book)(grade:6 ≤ book):Cruise.Voter M σ order seats stage vac book:=by
  have stock:=WilsonReceivedCanonicalSocketRows.fleet R d q hd o σ w pos order seats shelf fit three room
  refine ⟨fun j=>?_,fun s=>?_,start,fun s=>?_⟩
  · exact ⟨stock.honor j,stock.purchases.1 j,(Nat.sub_le _ _).trans ((fit j).trans ord),
      (WilsonOriginalThermometerGradedPalette.ceiling j).trans grade⟩
  · exact s.val.card_le_univ.trans (by simpa using three)
  · rw [Press.tall _ s levels stock.purchases.2]
    rw [←WilsonOriginalThermometerGradedPalette.total] at budget
    exact (Nat.add_le_add_left (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>Nat.zero_le _)) order).trans budget

theorem cash_nonneg:0 ≤ C₀:=sum_nonneg fun j _=>sum_nonneg fun c _=>WilsonReceivedCanonicalSocketRows.nonneg R d σ j c

theorem constant (a:ℝ):charge R d q σ (fun _=>a)=a*charge R d q σ (fun _=>1):=by
  simp only [charge,one_mul,Finset.mul_sum]

theorem sale (P:BudgetPoint){g U ξ cap:ℝ}(bp:0<cap)(order seats shelf:ℕ)
    (fit:∀j,rankQ j ≤ order)(three:3 ≤ seats)(room:14 ≤ shelf)
    (fund:Invoice.Supports P U (P.supportExponent+1) g σ ξ):
    let cost:=fee G P U g ξ order seats shelf 15
    let raw:=fun _:Fin 3=>cap/(1+C₀)
    let shrink:=1+|cost| * cap/Willow.haloSlack P.B
    let w:=fun v=>raw v/shrink
    (∀v,0<raw v) ∧ 1 ≤ shrink ∧ (∀v,0<w v) ∧
    (∀v,(w v)⁻¹=(1+C₀)*(cap⁻¹+|cost|/Willow.haloSlack P.B)) ∧
    charge R d q σ w ≤ cap ∧ Scene.Armada M w levels σ (charge R d q σ w) order seats shelf ∧
    WilsonRootedKioskOccupiedSlip.Gross (rendered M P g) raw P.B (P.supportExponent+1) (cost*charge R d q σ raw) ∧
    shrink⁻¹*(cost*charge R d q σ raw) ≤ Willow.haloSlack P.B:=by
  intro cost raw shrink w
  have size:=cash_nonneg R d σ
  have Rp (j:Fin 3):0<raw j:=div_pos bp (by linarith)
  have used:0 ≤ charge R d q σ raw:=sum_nonneg fun j _=>mul_nonneg (Rp j).le (WilsonReceivedCanonicalSocketRows.nonneg ..)
  have bound:charge R d q σ raw ≤ cap:=by
    rw [show charge R d q σ raw=cap/(1+C₀)*charge R d q σ (fun _=>1) from constant R d q σ _]
    calc
      _  ≤  cap/(1+C₀)*(1+C₀) := mul_le_mul_of_nonneg_left ((WilsonReceivedCanonicalSocketRows.one R d q σ).trans (by linarith)) (Rp 0).le
      _ = cap := div_mul_cancel₀ _ (by linarith)
  obtain ⟨one,pos,paid,inv⟩:=WilsonOriginalPointCompactCash.restored (gross:=cost) bp size (Willow.spare_pos P.B) used bound
  have small:charge R d q σ w  ≤  charge R d q σ raw:=by
    apply sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right (div_le_self (Rp j).le one) (WilsonReceivedCanonicalSocketRows.nonneg ..)
  have initial:=WilsonReceivedCanonicalSocketRows.fleet R d q hd o σ raw Rp order seats shelf fit three room
  have rents (s:(Stock.census (Fin 3)).Mode):(∑j∈s.val,levels j)+1 ≤ 15:=by
    have b:(∑j∈s.val,levels j) ≤ ∑j,levels j:=sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>Nat.zero_le _)
    rw [WilsonOriginalThermometerGradedPalette.total] at b
    omega
  have gross:=WilsonMarkedFixedPoleGross.landed M raw levels P initial fund 15 rents
  refine ⟨Rp,one,fun _=>pos,fun _=>inv,small.trans bound,
    WilsonReceivedCanonicalSocketRows.fleet R d q hd o σ w (fun _=>pos) order seats shelf fit three room,?_,paid⟩
  simpa only [cost,WilsonOriginalThreeCompactWallet.fee,mul_assoc] using gross

end YM.Integration.WilsonReceivedCanonicalSocketSale
