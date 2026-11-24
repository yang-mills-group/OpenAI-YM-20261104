import YM.QuadraticLocal.Campaign.Math
import YM.QuadraticLocal.Rates
/-! # Actual scheduled ledger of THIS Holder STEP

 Pure arithmetic. Above polynomial post-block growth & restore.K projections multiply
 outside; hit bound applies at earned radius and retains linear older error factor.
 `Y` publication costs in the smaller Book.Sh.C cardinal. Warm.Actor.Resource.Space`
 build from Cursor.Calendar contract in renewal. Empty allow case `b=0`: no mark needed,
 Shape Energy.Γ may still emit. Horizon.Key.Verm.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn.Earnings
open Function Filter Finset Lattice RG Wilson Marker Ac Push Push.AbsoluteSums Paths Animals
open QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Echo AllOrder AllOrder.Ink AllOrder.Ink.Money QuadraticLocal.Shelter
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable (E:Earnings)(G:Gauge) (L:Side)(P P':BudgetPoint)(k W g:ℝ)
-- some earnings can be negative (notably input at x prior.L.Clock via unreliable d,b), keep only necessary
structure Cashier (P P':BudgetPoint) (k W g:ℝ) :Prop where
    strong : 4 ≤ k
    wage : E.inFee G P ≤ k
    quote : E.outFee G P' ≤ k
    earns : E.produce L ≤ k
    past_small : Real.exp (-E.limitF)^P.B ≤ g^E.stage
    breeze : Invoice.Supports P E.liquid P.supportExponent g E.before E.limitF
    soon : Invoice.Supports P' E.mist (P'.supportExponent+1+1) g E.afterwards E.limitC
    price : 0 ≤ E.merchant
    shape : Earn.Width.fuelCuts L P.B E.top P'.B E.helmet
    schedule : Width.Memento E.count L E.before E.afterwards E.width
    tenor : g^E.stage ≤ E.fidelity ∧ E.fidelity ≤ 1
    fame : E.lost L P ≤ E.fidelity
    director : E.supervisor ≤ k
    manages : E.payroll ≤ k
    near : E.school L P' ≤ k
    velocity : E.flow P' ≤ k
    passGap : Earnings.past L P' ≤ k
    reserve : k⁻¹ ≤ W
-- not spell positivity budget.B_ Θ.Health. Warm as required.
section actual
variable {E G L P P' k W g}
variable (X0:Cashier E G L P P' k W g)
include X0
namespace Cashier
lemma cool : 1≤k:= le_trans (by norm_num) X0.strong
lemma paysAbove : 0<k:= zero_lt_one.trans_le X0.cool
local notation "K"=> k^5
lemma bloom : 0<E.fidelity:= (pow_pos X0.breeze.1 E.stage).trans_le X0.tenor.1
lemma minted : 0<E.outFee G P':= Invoice.positive P' E.mist E.cap X0.soon.2.2.1 E.count X0.soon.2.2.2.2.2.2.1 _
lemma frost (v:BudgetPoint): 0<E.flow v:= by unfold Earnings.flow Shelter.Deck.crewCost; exact mul_pos (Real.exp_pos _) (Nat.cast_pos.mpr (neighbors_ge _))
lemma capG {b:ℝ}(h:0≤b)(he:b≤1) : E.grow G L P' b ≤ k^2:=by
   have hh:= X0.earns; unfold Earnings.grow; exact (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right hh h).trans (mul_le_of_le_one_right X0.paysAbove.le he)) X0.minted.le).trans ((mul_le_mul_of_nonneg_right X0.quote X0.paysAbove.le).trans_eq (pow_two k).symm)
lemma pack {b:ℝ}(h:0≤b)(he:b≤1): E.pay L P' b ≤ k*E.fidelity:=by
    unfold Earnings.pay; exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right X0.near h).trans (mul_le_of_le_one_right X0.paysAbove.le he)) X0.bloom.le
local notation "R"=> E.grow G L P'
lemma converted {b:ℝ} (h:0≤b)(he:b≤ k⁻¹) : E.Valid G L P P' b g (k^5) W:=by
   have hb:= he.trans (inv_le_one_of_one_le₀ X0.cool); have hp:= X0.paysAbove; have hf:E.pay L P' b≤k:= (X0.pack h hb).trans (mul_le_of_le_one_right hp.le X0.tenor.2)
   refine ⟨hb, (mul_le_mul X0.wage he h hp.le).trans_eq (mul_inv_cancel₀ hp.ne'),X0.past_small,X0.breeze,X0.soon,X0.price,X0.shape,X0.schedule,X0.bloom.le,one_le_pow₀ X0.cool,le_trans ?_ X0.reserve⟩
   unfold shrinkTest; apply (inv_mul_le_iff₀ (pow_pos hp 5)).mpr; rw [pow_succ k 4] -- inv_mul_le says RHS ?
   have hB:E.payroll+R b+E.pay L P' b≤ k^3:= ((add_le_add (add_le_add X0.manages (X0.capG h hb)) hf)).trans (by change k+k^2+k≤ k^3; have :=X0.strong; nlinarith only [hp,this,mul_nonneg hp.le (show 0≤ (k-4)^2 from sq_nonneg _)]) -- polynomial proof: nlinarith test
   apply (mul_le_mul_of_nonneg_left hB (X0.frost P').le).trans; rw [mul_assoc, mul_inv_cancel₀ hp.ne', mul_one]; exact (mul_le_mul_of_nonneg_right X0.velocity (pow_pos hp _).le).trans_eq (by ring)
lemma spend {b d e:ℝ} (h:0≤b)(hh:b≤1)(he:0≤e)(hd:0≤d): E.hitPrice G L P P' b d e g≤8*k*(d+e+E.fidelity):=by
    let p:=E.hitPrice G L P P' b d e g; let v:= E.fidelity; have hk:= X0.cool; have hp:0≤k:= X0.paysAbove.le; let g':=g^E.stage; have hs':g'≤v:= X0.tenor.1; have hζ:0≤v:= X0.bloom.le; have h':0≤g':= (pow_pos X0.breeze.1 E.stage).le
    have hm:= X0.pack h hh; have hy: E.miss G L P P' b ≤ k*v:= (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right X0.fame h).trans (mul_le_of_le_one_right hζ hh)) X0.minted.le).trans (mul_le_mul_of_nonneg_right X0.quote hζ)
    have he₁ := (mul_le_mul_of_nonneg_right X0.passGap hd); have hf₁ : E.fail d e g ≤ 2*v+(d+v)*k+k*e+v:=by
       apply add_le_add _ hs'; exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hs' zero_le_two) ((mul_le_mul_of_nonneg_left X0.manages (add_nonneg hd h')).trans (mul_le_mul_of_nonneg_right (add_le_add_right hs' _) hp))) (mul_le_mul_of_nonneg_right X0.director he) -- add_le_add_right may expect left? check
    refine le_trans (show p≤k*d+(2*v+(d+v)*k+k*e+v)+k*v+k*v from add_le_add (add_le_add (add_le_add he₁ hf₁) hy) hm) (?_); change k*_+_ +_ +_≤ 8*k*(d+e+v); linarith only [mul_nonneg hp hd,mul_nonneg hp he,mul_nonneg hp hζ,le_mul_of_one_le_left hζ hk]
end Cashier
end actual
end YM.QuadraticLocal.Earn.Earnings
