import YM.Integration.WilsonOriginalThreeCompactProduct
import YM.Integration.WilsonOriginalThreeCompactWallet
import YM.Integration.WilsonRootedKioskCompleteFiling

/-! The original filed term salaries justify all countable series in the three stored fields. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFundedCompactProduct
open Function Finset Lattice Laurent RG Wilson Marker Gauge
open Push Push.AbsoluteSums Paths Animals ConnectedActivityE6 QuadraticLocal QuadraticLocal.Sunrise
open QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder AllOrder.Ink QuadraticLocal.Affinity
open WilsonOriginalPointCompactRoster WilsonOriginalPointCompactFaces
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{I:Type}[Fintype I]{q:ℕ}{σ:ℝ}
  (owner:I→Fin 3) (grades:Fin 3→ℕ) (sites:Fin 3→Site n)
  (T:(i:I)→WilsonOlderFreshGraphSlate.Copy G (grades (owner i)) q σ)
  (A:Fin 3→Set ℂ) (charge:I→ℂ)
local notation "J" => Stock.census (Fin 3)
local notation "M" => rows owner grades sites T A charge
local notation "own" i:max => (T i).rows (home sites (owner i)) (alone A (owner i))

theorem current (p:BudgetPoint) {g U ξ b:ℝ} {w:Fin 3→ℝ}
    (earned:WilsonRootedKioskOccupiedSlip.Gross (rendered M p g) w p.B (p.supportExponent+1) b)
    (hw:∀v,0<w v) (σ0:0 ≤ σ) (unit:∀v (t:ℂ),t∈A v→‖t‖ ≤ 1)
    (order seats shelf:ℕ) (qo:q ≤ order) (size:3 ≤ seats) (room:(∑v:Fin 3,grades v) ≤ shelf)
    (fund:Invoice.Supports p U (p.supportExponent+1) g σ ξ) (t:Wallet A) (u:Config G n) :
    Poly.pass (Spill.Foundry.uncut M g t u)=
      ∏v:Fin 3,(1+Poly.send ((J).fire v) (WilsonOriginalThreeCompactProduct.value owner
        (fun i=>amount owner grades sites T A charge i g t u) v)) := by
  have ha:0 ≤ p.supportExponent+1:=by linarith [p.exponent_pos]
  apply WilsonOriginalThreeCompactProduct.original owner grades sites T A charge g t u
  · exact (WilsonRootedKioskCompleteFiling.sums _ hw ha earned t u).1
  intro i
  have localFee:=budget_nonneg (WilsonOriginalPointCompactSalary.original_salary owner grades sites T A i σ0)
  have localStock:Scene.Armada (own i) (fun _=>1) (fun _=>grades (owner i)) σ
      (1+(T i).cost (home sites (owner i))) order seats shelf:=by
    apply (T i).earnings (home sites (owner i)) (alone A (owner i)) σ0 _
    · exact zero_lt_one
    · linarith
    · simp
    · exact qo
    · omega
    · exact (Finset.single_le_sum (f:=grades) (fun _ _=>Nat.zero_le _) (Finset.mem_univ (owner i))).trans room
    · intro t'
      exact unit (owner i) (t' ()).val (t' ()).property
  have tag (s:(Stock.census Unit).Mode) :
      (∑_v∈s.val,grades (owner i))+1 ≤ grades (owner i)+1:=by
    have bound:(∑_v∈s.val,grades (owner i)) ≤ ∑_v:Unit,grades (owner i):=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=>Nat.zero_le _)
    simpa using add_le_add_right bound 1
  have paid:=WilsonMarkedFixedPoleGross.landed (own i) (fun _=>1) (fun _=>grades (owner i))
    p localStock fund (grades (owner i)+1) tag
  exact (WilsonRootedKioskCompleteFiling.sums _ (fun _=>zero_lt_one) ha paid (subject A (owner i) t) u).1

end YM.Integration.WilsonOriginalFundedCompactProduct
