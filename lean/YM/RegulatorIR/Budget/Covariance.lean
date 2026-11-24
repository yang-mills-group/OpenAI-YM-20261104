import YM.RegulatorIR.Budget.Trace

/-! Lifts vs periodizing and lifting again (winding and inversion
contraction budget). At a conditional step where the required position
moments of the fluctuation covariance hold, an image discrepancy in one loop
only contributes near orbifold singularities. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Budget
open Function Tuple Motion Spatial Layer
open scoped Topology BigOperators ENNReal NNReal Classical
variable {P : ℝ} {X Y : Type}(A:Deck P X Y)

/-- Back to deck-compatible arrays, in general *not* a decaying kernel now. -/
def repeatK (Z:Layer Y Y)(x y:X):= Z (A.orbit x) (A.orbit y)*(A.orient x*A.orient y)
lemma repeat_norm (Z:Layer Y Y)(x y:X): ‖repeatK A Z x y‖ₑ = ‖Z (A.orbit x) (A.orbit y)‖ₑ:=by unfold repeatK;rw [enorm_mul,enorm_mul,A.over_sign,A.over_sign, one_mul,mul_one]
lemma repeat_sym (Z:Layer Y Y): Layer.Sym A A (repeatK A Z):=by
 intro d x y; unfold repeatK; rw [A.projected,A.projected,A.retreat,A.retreat,mul_mul_mul_comm,Motion.sign_sq,one_mul]
lemma repeat_cap {Z:Layer Y Y}{a:ℝ≥0∞}(hh:Layer.height Z a): Layer.height (repeatK A Z) a := fun _ _=>(repeat_norm ..).trans_le (hh _ _)

section Gap
variable {l : ℝ}{K : Layer X X} {a:ℝ≥0∞} (h:Sym A A K) (hl:0<l) (u:ℕ)
local notation "R" => Tariff.native l hl u
variable (hs: Layer.row K (Tariff.native l hl u) A.pos A.pos a)(c:a≠⊤)

/-- Expose all wrong images. `if` form convenient for arbitrary orbit sizes. -/
def missed (A:Deck P X Y) (K:Layer X X) x y (v:Stalk A.orbit (A.orbit y)):= if v.val=y then 0 else paint A A K x v.val
lemma repeat_agreement (Z : Layer Y Y)(x y : X): paint A A (repeatK A Z) x y = Z (A.orbit x) (A.orbit y):=by
 unfold paint repeatK; rw [mul_assoc,mul_mul_mul_comm (A.orient x), A.sign_sq,A.sign_sq,one_mul,mul_one]
include hl u h hs c
lemma uncovered (x y:X) : paint A A (repeatK A (wrapL A A K) - K) x y = ∑' v, missed A K x y v:=by
 let f (v:Stalk A.orbit (A.orbit y)):= paint A A K x v.val
 have H₀ : Summable (paint A A K x) := by
   apply quota_summable (w:=fun j=> (R).road (A.pos x) (A.pos j)) (fun i=>(R).unit _ _)
   rw [quota_eq _ (K x) _ (fun _=>shade ..)]; exact ne_top_of_le_ne_top c (hs x)
 have H: Summable f:= H₀.comp_injective Subtype.val_injective
 rw [show paint A A (repeatK A (wrapL A A K)-K) x y= wrapL A A K (A.orbit x) (A.orbit y)-paint A A K x y from by rw [← repeat_agreement A (wrapL A A K)]; unfold paint; rw [Pi.sub_apply,Pi.sub_apply,sub_mul],← from_proj A A K h x (A.orbit y)]
 let v₀:Stalk A.orbit (A.orbit y):= ⟨y,rfl⟩
 let g (v:Stalk A.orbit (A.orbit y)):= if v=v₀ then f v₀ else 0
 have hc : HasSum g (f v₀) := hasSum_ite_eq v₀ (f v₀)
 change (∑' v,f v) - f v₀ = _
 calc
    _ = ∑' v, (f-g) v := (H.hasSum.sub hc).tsum_eq.symm
    _ = _:= tsum_congr fun v=>by
      change f v - g v= if v.val=y then 0 else f v
      by_cases he:v=v₀
      · subst v; unfold g; simp [v₀]
      have hv:v.val ≠ y:= fun hi => he (Subtype.ext hi)
      rw [if_neg hv,show g v=0 from if_neg he,sub_zero]

lemma wrong_image (hp:0<P) (x y : X): ‖(repeatK A (wrapL A A K)-K) x y‖ₑ * Tariff.amount l u (singular P (A.pos y))≤ a * (R).road (A.pos x) (A.pos y) := by
 let B := (repeatK A (wrapL A A K)-K)
 let o:= Tariff.amount l u (singular P (A.pos y)); let M:=(R).road (A.pos x) (A.pos y)
 let Z:=Stalk A.orbit (A.orbit y)
 change ‖B x y‖ₑ*o≤a*M
 rw [← Layer.shade A A B,uncovered A h hl u hs c]
 apply (mul_le_mul_left enorm_tsum_le_tsum_enorm o).trans
 let w (z:X):= (R).road (A.pos x) (A.pos z)
 have hz : quota (fun v:Z=>K x v.val) (fun v:Z=>w v.val)≤ a:= (Stalk.over_le A.orbit (K x) w _).trans (hs x)
 apply le_trans _ (mul_le_mul_left hz M)
 unfold quota; simp_rw [← ENNReal.tsum_mul_right]
 apply ENNReal.tsum_le_tsum; intro v; change ‖missed A K x y v‖ₑ * o ≤ ‖K x v.val‖ₑ*w v.val*M
 by_cases ht:v.val=y
 · simp [missed,ht]
 rw [missed,if_neg ht,shade A A K, mul_assoc]
 apply mul_le_mul_right
 exact Tariff.amount_tri ((A.remote hp v.property.symm (Ne.symm ht)).trans ((dist_triangle (A.pos y) (A.pos x) _).trans_eq (by rw [dist_comm (A.pos y),add_comm]))) hl u dist_nonneg dist_nonneg
end Gap
end YM.RegulatorIR.Budget
