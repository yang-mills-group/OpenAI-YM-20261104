import YM.Integration.WilsonOriginalMixedBlockRows
import YM.Integration.WilsonOriginalFreshRosterWallet

/-! The real rooted salary for independently printed connected blocks on their original
source names. The actual binder connecting their sites is charged once, at its own root. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMixedBlockIncome
open Function Finset Lattice Laurent RG Wilson Marker Multi Gauge
open Push Push.AbsoluteSums Push.Local Paths Animals ConnectedActivityE6 QuadraticLocal
open QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder AllOrder.Ink QuadraticLocal.Affinity
open WilsonRegisteredPairUnaryWallet WilsonOriginalMixedBlockRows
open scoped Classical BigOperators

variable {V I:Type} [Fintype V] [DecidableEq V] [Fintype I] {O:I→Type}
  {G:Gauge} {n:Side} {P:Passport n V} (B:I→Earn.Binder P (Stock.census V))
  (X:(i:I)→O i→Earn.Row (Passport.point (fun _:Unit=>(B i).center)) (Stock.census Unit) G (Wallet disk))
  (rooted:∀(i:I)(z:O i),(X i z).binder=WilsonOlderFreshGraphPointWallet.point (B i).center)
variable (d:V→ℕ) (σ:ℝ) (cash:I→ℝ)
  {order seats shelf:ℕ}
  (earned:∀i,Scene.Armada (X i) (fun _:Unit=>1) (fun _:Unit=>∑v∈(B i).mode.val,d v)
    σ (cash i) order seats shelf)

def weight (base:V→ℝ)(x:Site n)(i:I):ℝ:=if (B i).center=x then
  Poly.toll base (B i).mode*Real.exp (σ*(B i).length) else 0

def bill (base:V→ℝ):ℝ:=Finset.univ.sup' Finset.univ_nonempty fun x:Site n=>
  ∑i, weight B σ base x i*cash i

local notation "M" => mounted B X
include rooted earned in
theorem funded (base:V→ℝ)(positive:∀v,0 < base v)
    (count:Fintype.card V ≤ seats)(crew:(∑v,d v) ≤ shelf):
    Scene.Armada M base d σ (bill B σ cash base) order seats shelf:=by
  have oldPay(i:I):SumBudget (fun z:O i=>(X i z).height σ) (cash i):=by
    have prev:=(earned i).suggests (B i).center
    apply sumBudget_mono prev (fun z=>mul_nonneg (X i z).sound.le (Real.exp_pos _).le) _ le_rfl
    intro z
    change _ ≤ if (X i z).center=(B i).center then Poly.toll (fun _:Unit=>1) (X i z).mode*(X i z).height σ else 0
    rw [if_pos (show (X i z).center=(B i).center from rfl)]
    simp [Poly.toll,Row.height]
  refine ⟨⟨fun s=>(Finset.card_le_univ _).trans count,fun _=>(?_:_ ≤ ∑v,d v).trans crew⟩,
    positive,?_,⟨fun z=>(earned z.1).purchases.spend z.2,?_⟩,
    fun z t=>(earned z.1).honor z.2 (project (B z.1).mode t)⟩
  · exact sum_le_sum_of_subset_of_nonneg (f:=d) (subset_univ _) fun _ _ _=>Nat.zero_le _
  · intro x
    let f(z:(i:I)×O i):ℝ:=if (M z).center=x then Poly.toll base (M z).mode*(M z).height σ else 0
    have pos(i:I):0 ≤ weight B σ base x i:=ite_nonneg
      (mul_nonneg (Poly.worth positive _).le (Real.exp_pos _).le) le_rfl
    have equal(i:I)(z:O i):f ⟨i,z⟩=weight B σ base x i*(X i z).height σ:=by
      change (if (B i).center=x then Poly.toll base (B i).mode*(M ⟨i,z⟩).height σ else 0)=_
      rw [WilsonOriginalMixedBlockRows.height B X rooted,weight]
      split_ifs <;> ring
    have paid(i:I):SumBudget (fun z:O i=>f ⟨i,z⟩) (weight B σ base x i*cash i):=by
      simp_rw [equal]
      exact budget_scale (pos i) (oldPay i)
    apply sumBudget_sigma paid (budget_finite (fun i=>budget_nonneg (paid i)) _)
    exact Finset.le_sup' (fun y:Site n=>∑i,weight B σ base y i*cash i) (mem_univ x)
  · intro z
    have covered:=(earned z.1).purchases.usable z.2
    have score:=covered.2
    rw [show (X z.1 z.2).mode=(Stock.census Unit).fire () from congrArg Earn.Binder.mode (rooted z.1 z.2)] at score
    refine ⟨covered.1,?_⟩
    change (X z.1 z.2).lamp.toll=∑v∈(B z.1).mode.val,d v
    simpa [Census.fire] using score

end YM.Integration.WilsonOriginalMixedBlockIncome
end
