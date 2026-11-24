import YM.Integration.WilsonOlderFreshGraphPointWallet
import YM.Integration.WilsonEmittedFiledCatalogue
import YM.Integration.WilsonEmittedLongInvoice

/-! Reopen a previously issued unary group-word catalogue on its original
receiving wallet. The small source radius is fixed by its before-test
income; all-group summability includes the zero-angular marked term. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphCatalogueIncome
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn
open AllOrder AllOrder.Ink QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Sunrise.Aviary
open WilsonOlderFreshGraphSlate WilsonOlderFreshGraphArmada WilsonEmittedGroupWallet
open scoped Classical BigOperators

variable {G:Gauge}{n:Side}{d Q:ℕ}{σ:ℝ} (T:Copy G d Q σ)
variable {P:Passport n Unit}{H:Census Unit}(S:Binder P H)(A:Unit→Set ℂ)
variable {B:BudgetPoint}{g K θ:ℝ}(scope:Invoice.Supports B K (B.supportExponent+2) g σ θ)
variable {w b:ℝ}{ord seats shelf:ℕ}
local notation "M" => (T.rows S A)
include scope in
theorem posted (old:Scene.Armada M (fun _=>w) (fun _=>d) σ b ord seats shelf)
    (t:Affinity.Wallet A)(U:Config G n) : Summable (fun i=>Spill.raw M g t i U):=by
  let h:=ceiling g ord shelf
  have money:=WilsonOlderFreshGraphVote.before_tests S T.roll T.fare σ T.paid T.legal T.positive (value A) scope.2.2.2.2.1
  have bank:Summable (fun i:T.Roster=>(M i).height σ):=money.2.1
  have h0:0 ≤ h:=by unfold h ceiling; positivity [scope.1]
  apply Pi.summable.mpr
  intro s
  apply Summable.of_norm_bounded (bank.mul_left h)
  intro i
  change ‖(Poly.send (M i).mode ((M i).nominal g t U)).part s‖ ≤ h*(M i).height σ
  rw [Poly.part_send]
  have grow:(M i).salary ≤ (M i).height σ:=le_mul_of_one_le_right (M i).sound.le
    (Real.one_le_exp (mul_nonneg scope.2.2.2.2.1 (Nat.cast_nonneg _)))
  split_ifs
  · exact (WilsonEmittedGroupWallet.full M (fun _=>w) (fun _=>d) old B scope i t U).trans
      (mul_le_mul_of_nonneg_left grow h0)
  · rw [norm_zero]
    exact mul_nonneg h0 ((M i).sound.le.trans grow)

include scope in
theorem original (y:Site n) {mass:ℝ}(bill:(∑j,T.fare j) ≤ mass)
    (cap:∀ t, ‖value A t‖ ≤ 1)(order:Q ≤ ord)(width:1 ≤ seats)(height:d ≤ shelf):
    ∃w:ℝ,0<w ∧ w⁻¹ ≤ 1+mass ∧
      Scene.Armada (T.rows (WilsonOlderFreshGraphPointWallet.point y) A) (fun _=>w) (fun _=>d) σ 1 ord seats shelf ∧
      ∀(t:Affinity.Wallet A)(U:Config G n),Summable (fun i=>Spill.raw (T.rows (WilsonOlderFreshGraphPointWallet.point y) A) g t i U):=by
  let S₀:=WilsonOlderFreshGraphPointWallet.point y
  obtain ⟨c,w,_,small,_,pos,funded,cost⟩:=WilsonOlderFreshGraphPointWallet.original T y bill 1 zero_lt_one
  have old:=T.earnings S₀ A scope.2.2.2.2.1 cap w 1 pos zero_lt_one (funded.trans small) order width height
  exact ⟨w,pos,by simpa using cost,old,posted T S₀ A scope old⟩

end YM.Integration.WilsonOlderFreshGraphCatalogueIncome
end
