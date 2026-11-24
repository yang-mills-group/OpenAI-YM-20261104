import YM.QuadraticLocal.HaloMix.Yield
import YM.Push.RELAY_DIFFERENCE.RawTop
import YM.Bid.Fuels
import Mathlib.Analysis.Complex.ExponentialBounds
set_option autoImplicit false
noncomputable section
/-!
# Reuse the re-anchoring estimates of Acanthus on this state

 The re-anchoring estimates include conversion back to the readout norm with a supremum over all origins. Theta-space rooting also requires occupancy constraints. Counts here only for thermometer weights.
-/
namespace YM.QuadraticLocal.Neighborhood
open Finset Function Filter Lattice RG Wilson Push Ac Marker Extra.Trajectories 
open Local Labels
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side} {I J V:Type} {P:BudgetPoint}{X Y : I→Support n}
   {f g h e:ℝ} (x y: Site n)
open AbsoluteSums Next.Foundations
lemma pitch {Y:Support n}{F:Config G n→ℂ}(h:P.supBounds x Y F g): P.supBounds y Y F (((1+(separation x y:ℝ))^P.power)^P.order*g) := by
    let b:= (1+(separation x y:ℝ))^P.power; have hp:1 ≤ b:= one_le_pow₀ (by simpa only [le_add_iff_nonneg_right] using (Nat.cast_nonneg (α:=ℝ) (separation x y))); have hv:=zero_lt_one.trans_le hp
    have he (A:Directions G n)(h:P.dirBound y A): P.dirBound x (b⁻¹ • A):=by
       intro i; have hn: 1+(separation i.1 y:ℝ) ≤ (1+(separation x y:ℝ))*(1+ (separation i.1 x:ℝ)):=by
           have ht : (separation i.1 y:ℝ) ≤ (separation i.1 x:ℝ) + (separation x y:ℝ):=by exact_mod_cast separation_triangle i.1 x y
           nlinarith [show 0 ≤ (separation i.1 x:ℝ)*(separation x y:ℝ) from (by positivity)]
       change ‖b⁻¹ • A i‖ ≤ _; rw [norm_smul_of_nonneg (inv_pos.mpr hv).le]; apply (mul_le_mul_of_nonneg_left (h _) (inv_pos.mpr hv).le).trans
       have hh:= pow_le_pow_left₀ (by positivity:0 ≤ 1+(separation i.1 y:ℝ)) hn P.power
       apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh P.threshold_pos.le) (inv_pos.mpr hv).le).trans; rw [mul_pow]; change b⁻¹*(P.threshold*(b*_))≤_; rw [mul_left_comm P.threshold, inv_mul_cancel_left₀ hv.ne']
    refine ⟨mul_nonneg (pow_nonneg hv.le _) h.1,fun U hu l hl hh=> ?_⟩
    let q:=l.map fun A=> b⁻¹ • A; have ht:q.length ≤ P.order:=by simpa [q] using hl
    rw [← show q.map (fun A=> b • A)=l from (by simp [q,Function.comp_def,hv.ne']), RelayDifference.left_dilate,norm_smul_of_nonneg (pow_nonneg hv.le _)]
    exact mul_le_mul (pow_le_pow_right₀ hp ht) (h.2 U hu q ht fun i hi=> by obtain ⟨k,hk,rfl⟩:= List.mem_map.mp hi; exact he _ (hh _ hk)) (norm_nonneg _) (pow_nonneg hv.le _)
private lemma snow (x:ℝ) (r:ℕ) (hx:0 ≤ x): x^r ≤ r.factorial*Real.exp x:=by
    have HH : HasSum (fun i:ℕ=>x^i/i.factorial) (Real.exp x):=by
        convert! NormedSpace.expSeries_div_hasSum_exp x using 1
        rw [Real.exp_eq_exp_ℝ]
    rw [mul_comm]; apply (div_le_iff₀ (by positivity : (0:ℝ)<r.factorial)).1; rw [← HH.tsum_eq];exact (HH.summable).le_tsum r (fun _ _=> by positivity)
def scarf (P:BudgetPoint) : ℝ:= ((3*(4*P.B+2):ℝ))^(P.power*P.order) * (P.power*P.order).factorial
lemma lap {Y:Support n}(hx:x∈Y)(hy:y∈Y): ((1+(separation x y:ℝ))^P.power)^P.order ≤ scarf P*Real.exp (coverNumber P.B Y):=by
    let d:ℝ:= coverNumber P.B Y; have hd: 1≤d:=by
        apply Nat.one_le_cast.mpr
        by_contra h; have hu: coverNumber P.B Y=0:=by omega
        obtain ⟨Z,h,hP⟩:=coverNumber_realized P.B Y; have hV:= h.1 hx; rw [card_eq_zero.mp (hP.trans hu), halo] at hV; simp at hV
    have hh: (separation x y:ℝ) ≤ d*(4*P.B+2)+2*P.B:=by unfold d; exact_mod_cast Corona.extent _ P.B hx hy -- edit
    have hp: 1+(separation x y:ℝ) ≤3*(4*P.B+2)*d:=by nlinarith
    rw [← pow_mul]; refine (pow_le_pow_left₀ (by positivity) hp (P.power*P.order)).trans ?_; rw [mul_pow,scarf,mul_assoc]; exact mul_le_mul_of_nonneg_left (snow d _ (zero_le_one.trans hd)) (by positivity)
lemma scarf_pos (P:BudgetPoint):0<scarf P:= by unfold scarf; positivity
lemma cost (Y:Support n) (hx:x∈ Y)(hy:y∈ Y){F:Config G n→ℂ} (hf:P.supBounds x Y F f): P.supBounds y Y F ((scarf P*Real.exp (coverNumber P.B Y))*f):=
       bound_weaken (pitch x y hf) (mul_le_mul_of_nonneg_right (lap x y hx hy) hf.1)

-- `grain` counts EACH length to order, in FACTORIAL norm. Need convert to the native
-- supplier-worker norm tournament AND back at same stencil. It's not necessary to
-- pay the dimensions π or any volume. Only pay order factorial (pre-L prepared).
variable {V Y:Type}{Z:Support n}{k:ℕ}(F:Config G n→ℂ)
lemma inBound (h:Mix.grain P Z F x g) : P.supBounds x Z F (P.order.factorial*g):=by
    obtain ⟨v,hv,hG,hp⟩:= h; have hn : 0 ≤ g:= le_trans (Finset.sum_nonneg (fun i _=> div_nonneg (hv i) (by positivity))) hG
    refine ⟨mul_nonneg (by positivity) hn, fun U hi l hl hx=>?_⟩; refine le_trans (hp l hl hx U hi) ?_
    let i:=l.length; have he : v i/(i.factorial:ℝ) ≤ g:= le_trans (Finset.single_le_sum (f:=fun i=> v i/(i.factorial:ℝ)) (fun i _=>div_nonneg (hv i) (by positivity)) ( Finset.mem_range.mpr ( Nat.lt_succ_of_le hl ))) hG
    refine le_trans ((div_le_iff₀ (by positivity:(0:ℝ) < i.factorial)).1 he) ?_; rw [mul_comm]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hl) hn -- lemma?
lemma outBound (h:P.supBounds x Z F g): Mix.grain P Z F x (3*g):=by
    -- from checkpoint4 score3
    refine ⟨fun _=> g,fun _=> h.1,?_,fun k h₁ h₂ U hU=> h.2 _ hU _ h₁ h₂⟩
    let t (n:ℕ):ℝ:= 1 / n.factorial; have hS: HasSum t (Real.exp 1) :=by rw [Real.exp_eq_exp_ℝ]; simpa [t] using NormedSpace.expSeries_div_hasSum_exp (1:ℝ)
    let S:=Finset.range (P.order+1); change ∑ i ∈ S,(g/_ :ℝ) ≤ _; have h0: g* Real.exp 1 ≤ 3*g:= (mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le h.1).trans_eq (mul_comm ..)
    have hm := hS.mul_left g; rw [← hm.tsum_eq] at h0
    refine le_trans (le_of_eq ?_) ((hm.summable.sum_le_tsum S (fun i _=> mul_nonneg h.1 (by unfold t; positivity))).trans h0)
    congr 1; simp [t,div_eq_mul_inv]
end YM.QuadraticLocal.Neighborhood
