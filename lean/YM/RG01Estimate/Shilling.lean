import YM.RG01Estimate.Arms
import YM.Pert.Kinetic.Panel
/-! # projection comparison buys full padding plus wraps in ALL n. Quantum
 scales with H (before reset) then admits as arbitrary fixed coupling power. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Censor.Toft
open Function Filter Set Lattice Wilson RG Progress.DirectedRecipe AnalyticBridge VerifiedReset Collection Averaging Ovens Ovens.Pipes
   Payments Extra.Iteration Pilgrim Push.BetaTransport Push Push.AbsoluteSums
open Quotes Fresco
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}{p:BudgetPoint}(g:G.Simple) {hn:20<n.val} {Δ H:ℝ}

def stock (G:Gauge) (p:BudgetPoint) := (1+turnFee p)* |factor| * (2:ℝ)⁻¹ * (Fintype.card PlaqAxes) * pairBill G p
lemma stock_nn : 0 ≤ stock G p:=by unfold stock; have hp:=turnFee_pos p; have hx:= pair_nonneg G p; positivity

def cash (G:Gauge)(p:BudgetPoint)(n:Side) := Fintype.card (Seat n) * stock G p * Real.exp ((p.supportExponent+1)*81)
def reserve (G:Gauge)(p:BudgetPoint)(hn:20<n.val):=2 * (1+cash G p n)*huge n * Real.exp (-(coin p n hn:ℝ))

lemma checkin (hp: Real.exp ((p.supportExponent+3)*(coin p n hn:ℝ))*(p.threshold^2*|Δ|) ≤ huge n * (2*H)) :
    p.threshold^2*|Δ| + priceWrap G p Δ hn ≤ Toft.reserve G p hn * H:=by
    let q:=p.threshold^2*|Δ|
    let k:ℝ:= coin p n hn; let X:=Real.exp ((p.supportExponent+1)*k)
    have he : priceWrap G p Δ hn = cash G p n * X * q:= by
       have hh : (coin p n hn:ℝ)=k:= rfl; unfold priceWrap intake toll cash stock -- stock after
       unfold X q; rw [abs_mul,hh,mul_add,Real.exp_add]; ring
    have hc : 0≤cash G p n:= by unfold cash; have he:0 ≤ stock G p:=stock_nn; positivity
    have hk : 1≤ X:= Real.one_le_exp (mul_nonneg (by have hz:=p.exponent_pos; linarith) (Nat.cast_nonneg _))
    have hX : X ≤ Real.exp ((p.supportExponent+3)*k) * Real.exp (-k):= by unfold X; rw [← Real.exp_add]; apply Real.exp_monotone; have hc:0≤k:=Nat.cast_nonneg _; linarith only [hc]
    have hY: X*q ≤ Real.exp (-k) * (huge n*(2*H)):=
       calc
           _ ≤ Real.exp ((p.supportExponent+3)*k)* Real.exp (-k)*q := mul_le_mul_of_nonneg_right hX (by unfold q; positivity)
           _ = Real.exp (-k)*(Real.exp ((p.supportExponent+3)*k)*q):= by ring
           _ ≤ _:= mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)
    rw [he]; unfold Toft.reserve; rw [show (coin p n hn:ℝ)=k from rfl]; change q+_ ≤ _
    nlinarith only [hY, mul_le_mul_of_nonneg_left hY hc, le_mul_of_one_le_left (show 0 ≤ q from mul_nonneg (sq_nonneg _) (abs_nonneg _)) hk]

lemma coin_floor (hn:20<n.val): n.val≤ 10*(4*p.B + 2)*(1+coin p n hn):=by
    obtain ⟨a,h,hP⟩:= left_min p n hn
    obtain ⟨x,hx⟩ := Classical.not_forall.mp (show ¬∀ x∈expand a,10*separation x a.site<n.val from h)
    obtain ⟨hx,hU⟩:= Classical.not_forall.mp hx
    rw [← hP]; exact (Nat.not_lt.mp hU).trans ((Nat.mul_le_mul_left 10 (Geo.enlarged_dist p a x hx)).trans_eq (mul_assoc _ _ _).symm)
lemma card_n (n:Side): (Fintype.card (Site n):ℝ)=(n.val:ℝ)^4:=by
   exact_mod_cast (show Fintype.card (Site n)=n.val^4 by simp [Site,Four,Per])
lemma acclivity (hn:20<n.val):
    Toft.reserve G p hn = 2*(1+(Fintype.card Signed:ℝ)*(n.val:ℝ)^4 * stock G p * Real.exp ((p.supportExponent+1)*81)) *
        ((n.val:ℝ)^2*3*((n.val:ℝ)^4)^2)*Real.exp (-(coin p n hn:ℝ)):=by unfold Toft.reserve cash huge; simp
end YM.RG01Estimate.Censor.Toft
