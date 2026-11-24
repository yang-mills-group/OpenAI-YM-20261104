import YM.RegulatorIR.Centered.View

/-! Explicit finite order bound with ext uniform polynomial formulation. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Centered
open Topology Lattice MeasureTheory Set Metric Function Motion Spatial
open Budget Budget.Packet Budget.Tariff Budget.Layer Budget.Tuple Budget.Deck Uniform Uniform.Post Ledger Ledger.Sky Step Diagram Gradient
open scoped ENNReal NNReal BigOperators Classical
variable {W: Type} {M:W→ℕ}{X Y:Page M→Type} (S:Sky X Y)(T:S.Accounts){m:ℕ}
variable (R:(movie T (film W)).Report m)(F:Margins Y)
variable {e u b q p h α:ℕ}{γ:ℝ}{c:Flap M→ℝ≥0∞} {k j:Choice M}{L:Meter W}

-- some reusable conversion tools
lemma Carry_rt {g w: W→ℝ} (h:∀ i,0≤w i) (hp:Carry L (fun i=> ENNReal.ofReal (w i)) fun i=> ‖g i‖ₑ) : ∃ K:ℝ, ∃ t:ℕ, 0≤ K ∧ ∀ i, ‖g i‖ ≤ K*(L.val i).toReal^t*w i:=by
 obtain ⟨f,⟨K,t,hK,G⟩,H⟩:= hp;refine ⟨K.toReal,t,by positivity,fun i=> ?_⟩
 have h' := le_trans (H i) (mul_le_mul_left (G i) _)
 have h'' := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top hK (ENNReal.pow_ne_top (L.below i))) ENNReal.ofReal_ne_top) h'
 simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (h i), ENNReal.toReal_pow, toReal_enorm] using h''

variable (H: Seated S T R F L u b q p h α γ c k)
include H
lemma allC (he:e ≤ p)(hj:k.age≤j.age): ∃ K:ℝ,∃ t:ℕ, 0≤K ∧ ∀ w x, ‖medium S T R j e w x‖≤ K*(L.val w).toReal^t:=by
 have ht:Carry (L.us (film W)) (fun _=>ENNReal.ofReal (1:ℝ)) fun w:plane W=> ‖medium S T R j e w.1 w.2‖ₑ:= by simp only [ENNReal.ofReal_one]; exact Carry.regular (fading S T R F H he hj)
 obtain ⟨K,t,hK,H⟩:= Carry_rt (fun _=>by exact zero_le_one) ht
 exact ⟨K,t,hK,fun w x=> by simpa only [mul_one] using! H (w,x)⟩

variable [∀ w,Fintype (Y w)]
lemma window_gap (he:e ≤ p) (hj:k.age≤j.age) : ∃ K:ℝ, ∃ t:ℕ, 0≤K ∧ ∀ w x, x∈court (S.P w) → ‖outlook S T R F (w,x) e-medium S T R j e w x‖ ≤ K*(L.val w).toReal ^ t * S.modifyErr h b γ j w := by
 have hp (i:Face S):0 ≤ S.modifyErr h b γ j ((introF S i).1):= by
    apply add_nonneg (S.transfer_pos _).le; have hh:= S.hl (j.choose (introF S i).1); exact inv_nonneg.mpr (Real.rpow_nonneg hh.le _)
 obtain ⟨K,t,hK,H⟩:= Carry_rt hp (at_cube S T R F H he hj)
 exact ⟨K,t,hK,fun w x hx=>H ⟨(w,x),hx⟩⟩

/-- Finite-top, centered and terminated. Neither the primitive hypotheses nor
the rate estimate depend on a scale-independent side bound. All integrations
on half-open boxes in the real center coordinates. -/
theorem integrated (he:e≤p)(hj:k.age≤j.age)
   (hg:∀ w, Rhythm (S.l (j.choose w)) (medium S T R j e w))
   (hi:∀ w,IntegrableOn (medium S T R j e w) (court (S.P w)))
   (hv:∀ w,IntegrableOn (fun x=>outlook S T R F (w,x) e) (court (S.P w))) : ∃ K:ℝ, ∃ t:ℕ, 0≤K ∧ ∀ w,
   ‖bright S T R F e w - diffuse S T R j e w‖ ≤ K*(L.val w).toReal ^ t * (S.modifyErr h b γ j w + S.l (j.choose w)/ S.P w) := by
 obtain ⟨A,p,hA,G⟩:= allC S T R F H he hj
 obtain ⟨C,q,hC,Q⟩:=window_gap S T R F H he hj
 refine ⟨C + 128*A,p+q, by positivity,fun w=> ?_⟩
 let F':= medium S T R j e w
 let P:= S.P w; let l:= S.l (j.choose w); let k:= (L.val w).toReal; let x:=P/8
 let v:= weigh (same x) x F'
 let Z:= bright S T R F e w; let S':= diffuse S T R j e w; let d:= S.modifyErr h b γ j w
 have hP:0<P:= S.hp _
 have hx:0<x:= by unfold x; positivity
 have hL:1≤k:= by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono (L.below w) (L.above w)
 have hl: 0<l := S.hl _
 have hz: 0< k:= zero_lt_one.trans_le hL
 have he: ‖Z-v‖≤ C*k^q*d:=by change ‖weigh _ _ _-weigh _ _ _‖ ≤ _; rw [minusW (hv w) (hi w)]; exact worth hx (Q w)
 have hv: ‖v-S'‖≤128*A*k^p*(l/P):= by
    refine le_trans (stretch (C:=A*k^p) (hg w) hl hx (hi w) (by positivity) (fun _ _=> G _ _) (fun _ _=> G _ _)) ?_
    change 16*(A*k^p)*(l/(P/8)) ≤ _; apply le_of_eq; ring
 have h' (i:ℕ)(hi:i ≤ p+q): k^i ≤ k^(p+q):=pow_le_pow_right₀ hL hi
 have hd:0≤d:= add_nonneg (S.transfer_pos w).le (by exact inv_nonneg.mpr (Real.rpow_nonneg hl.le _))
 change ‖Z-S'‖≤(C+128*A)*k^ (p+q)*(d+l/P)
 calc
    _= ‖(Z-v)+(v-S')‖:=by rw [show Z-v+(v-S')=Z-S' by abel]
    _ ≤ _:= norm_add_le _ _
    _ ≤ _:= add_le_add he hv
    _ ≤ (C+128*A)*k^ (p+q)*(d+l/P):= by
       rw [mul_add]; gcongr <;> first | positivity | omega | linarith only [hC,hA]
end YM.RegulatorIR.Centered
