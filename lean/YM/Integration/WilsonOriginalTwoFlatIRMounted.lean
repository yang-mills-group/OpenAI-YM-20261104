import YM.Integration.WilsonOriginalTwoFlatIRRowFields
import YM.Integration.WilsonIndependentCollarSlateIntensity
import YM.Integration.WilsonOriginalMixedBlockTable

/-! At common capture the independent rooted copies, including scalar
copies on nonempty modes, are the literal unmasked ordinary polynomial.
Their centerwise salary funds the derivative and the full group wage. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRMounted
open Function Filter Finset Lattice Wilson RG Marker Ac Gauge QuadraticLocal QuadraticLocal.Earn
open Push Push.AbsoluteSums QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Affinity
open WilsonRootedKioskOccupiedSlip WilsonOlderFreshGraphSlate WilsonRegisteredPairUnaryWallet
open WilsonOriginalMixedBlockRows
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:Side}{V I:Type}[DecidableEq V][Fintype V][Fintype I]
variable {P:Passport n V}(B:I→Earn.Binder P (Stock.census V))(t:V→ℕ){σ:ℝ}{q:ℕ}
variable (T:∀i:I,Copy G (∑v∈(B i).mode.val,t v) q σ)
local notation "X" => (fun i:I=>(T i).rows (WilsonOlderFreshGraphPointWallet.point (B i).center) disk)
local notation "M" => mounted B (X)
local notation "one" => (fun _:V=>(1:ℝ))
local notation "cash" => (fun i:I=>WilsonIndependentCollarSlateIntensity.amount (T i) (B i).center)
local notation "q₀" => ∑i:I,Real.exp (σ*(B i).length)*(cash i)
local notation "marks" => Stock.census V
local notation "load" => (∑v:V,t v)+1
local notation "ink" i:max g:max U:max => ∑'a:(T i).Roster,WilsonGeneralArityCopyAccount.term (T i) (B i).center g U a
local notation "F" g:max x:max U:max =>
  ∏i:I,(1+Poly.send (B i).mode ((∏v∈(B i).mode.val,(x v).val)*(ink i g U)))

def value (g:ℝ)(x:Wallet (room V))(U:Config G n):Poly (Stock.census V):= F g x U

theorem original {g:ℝ} {ord seats shelf E:ℕ}{K U ξ:ℝ}
    (hs:0 ≤ σ)(dep:q ≤ ord)(oc:1 ≤ seats)(slots:Fintype.card V ≤ seats)(fit:(∑v,t v) ≤ shelf)
    (p:BudgetPoint)(fund:Invoice.Supports p U (p.supportExponent+2) g σ ξ)
    (fare:Invoice.price p U (ord+shelf+1) seats (p.supportExponent+2) ξ G ≤ 
      (2:ℝ)^(ord+shelf+1)*(3*g⁻¹)^2)(paid:(q₀) ≤ K*(3*g⁻¹)^E):
    let L:=rendered (M) p g
    let h:=((2:ℝ)^(ord+shelf+1))^2*max 1 K
    let e:=(load)+2+E
    (∀(x:Wallet (room V))(U':Config G n),Poly.pass (bare L x U')=value B t T g x U') ∧
    ∃C₀ C₁:ℝ,0 ≤ C₀ ∧ 0 ≤ C₁ ∧ C₀ ≤ h*(3*g⁻¹)^e ∧ C₁ ≤ h*(3*g⁻¹)^e ∧
      L.Paid (one) p.B (p.supportExponent+2) C₀ ∧ Gross L (one) p.B (p.supportExponent+2) C₁:=by
  have sub(s:(marks).Mode):(∑v∈s.val,t v) ≤ ∑v,t v:=sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _=>Nat.zero_le _
  have offers(i:I):=WilsonGeneralArityCopyAccount.original (T i) (B i).center hs dep oc ((sub _).trans fit)
  have incomes(i:I):=WilsonIndependentCollarSlateIntensity.original (T i) (B i).center hs dep oc ((sub _).trans fit)
  have actual:=WilsonOriginalMixedBlockIncome.funded B (X) (fun i=>(offers i).2.1) t σ (cash) incomes
    (one) (fun _=>zero_lt_one) slots fit
  have amount(i:I):0 ≤ cash i:=budget_nonneg (WilsonIndependentCollarSlateIntensity.spent (T i) (B i).center hs)
  have less:WilsonOriginalMixedBlockIncome.bill B σ (cash) (one) ≤ (q₀):=by
    apply sup'_le
    intro site _
    apply sum_le_sum
    intro i _
    unfold WilsonOriginalMixedBlockIncome.weight
    split_ifs
    · simp [Poly.toll]
    · exact mul_le_mul_of_nonneg_right (Real.exp_pos _).le (amount i)
  refine ⟨?_,WilsonOriginalTwoFlatIRRows.board fund.1 fund.2.1 (M) (one) t p actual fund
    (fun s=>Nat.add_le_add_right (sub s) _) (less.trans paid) fare⟩
  intro x U'
  change Poly.pass (Spill.Foundry.uncut (M) g x U')=_
  exact (WilsonOriginalMixedBlockTable.original B (X) g x U' _ (fun i=>(offers i).2.2.2 g _ _)).2

end YM.Integration.WilsonOriginalTwoFlatIRMounted
