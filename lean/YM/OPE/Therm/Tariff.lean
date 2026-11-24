import YM.OPE.Therm.Ardent
/-!
# Finite measures entropy-DLG for successful small-window mean-zero tests
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm.Portolan
open Function Set Filter RG Lattice Wilson MeasureTheory Cells House Cradle
open scoped BigOperators Classical Topology ENNReal Matrix.Norms.Frobenius
variable {G:Gauge} {A:History G}(H:A.Selected) {k N p r q:ℕ} {t τ C e L:ℝ}
local notation "n"=> A.S.side k p
local notation "𝒞"=> Config G n
local notation "R"=> A.rep N p k
local notation "D"=> scene A N p k
variable (T:Tiling (A.S.side k p)) (hv:T.kind=.site)
local notation "ν"=> Fintype.card T.Cell
local notation "M"=> (T.side.val:ℝ)
local notation "a"=> parcel R r q
variable {f:Config G (A.S.side k p)→ℝ} {z:Site (A.S.side k p)} {X:Finset (Edge (Site (A.S.side k p)))}
include H hv
set_option maxHeartbeats 500000 in
private lemma chance (hi:k ≤ N)(h:Stove.Chart R r C e)(hs:safeCost G n T.side (Stove.haloFee R r) q C e t L)(hx:4*t+τ≤ (R).p.threshold)(hβ :4*t≤τ)
    (hP:∀ x: Face (Per n),(D).real (trigger x τ) ≤ (L⁻¹)^200) (he:Attempt R r τ q z f X) :
    (∫ U,f U∂ D) ≤ L⁻¹:=by
   letI:=probability (p:=p) H hi; let c:=L⁻¹; have hp:= safe_min (T:=T) hs; have hL:= zero_lt_one.trans_le hp
   have hh:c*L=1:= inv_mul_cancel₀ hL.ne'; have hc:0<c:= inv_pos.mpr hL; have hz: c≤1:= by nlinarith only [hp,hh,hc]
   choose J hJ hb hw using fun i:T.Cell=> issue T i a q
   let u(y:Site n):=lines y z X; let W(y:Site n) U:= f (pull 1 (y-z) U); let P:= fare T J c
   let F (i:T.Cell) U:= value T W J c i U
   have hE i:= attempt_slides i z h he; have ha : Programs T R r τ F P:= lodge T u W hv h c hE J hJ hb
   have hm: 1≤ M:= (one_le_pow₀ hp).trans hs.least; have hm':2 ≤ T.side.val:=by
       exact_mod_cast (show (2:ℝ) ≤ M from le_trans (le_trans (by norm_num) hs.unit) (le_trans (by simpa only [pow_one] using pow_le_pow_right₀ hp (by decide:1 ≤ 14)) hs.least))
   have hU:=lint (T:=T) hs; have hvy: 0 ≤ (M+1)^4+premium T R r t C:=add_nonneg (by positivity) hU.1
   have hK (i:T.Cell) (U:𝒞): F i U ≤ (M+1)^4:=by
      have hp (j:Site n) : W j U≤ 1:=(le_abs_self ..).trans ((hE j).unitBound U)
      change (∑ j∈J i,c* W j U) ≤ _; apply (Finset.sum_le_sum (fun j _=> (mul_le_mul_of_nonneg_left (hp j) hc.le).trans_eq (mul_one _))).trans
      rw [Finset.sum_const,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg (J i).card)).trans; rw [mul_one]; exact_mod_cast ((Finset.card_le_card ((hJ _).trans (fun i hi=> hall_leased T hi))).trans_eq (hall_size ..))
   let B i:ℝ:= (J i).card; let Z:= ∫ U,f U∂D
   have hS: (∑ i,B i*(c*Z)) ≤ (∑ i,B i*(c^2/2))+ ν*M^3*L^3:= by
      have ht:= credit H T hv hi h ha hs.narrow hs.temp hx hβ hm' (pow_nonneg hc.le 200) hP hK hvy
      have hi(i:T.Cell): (∫ U,F i U∂ D)=B i*(c*Z):= by
         have H(i): Envelope (W i):= ⟨(hE i).hb,1,(hE i).unitBound⟩; unfold F value
         rw [integral_finsetSum (J i)]; simp_rw [integral_const_mul]; have ht (j): (∫ U, W j U∂ D)=Z:= retune ‹_› 1 (j-z) hi f; simp_rw [ht,Finset.sum_const,nsmul_eq_mul]; rfl
         exact fun j _=> ((H j).integrable (D)).const_mul _
      simp_rw [hi] at ht; exact ht.trans (weather (T:=T) hs hv P)
   by_contra! ht; apply (not_lt_of_ge hS); change c < Z at ht
   have hh' (i:T.Cell): B i*(c^2/2)+ M^3*L^3 < B i*(c*Z):=by
      have hr0:0<B i:= pos_of_mul_pos_left (lt_of_lt_of_le (pow_pos (zero_lt_one.trans_le hm) _) (hotParcel hs i (J i) (hw i))) (pow_nonneg hL.le 6)
      have hPay: 4*M^3*L^5 ≤ B i:= by
         apply le_of_mul_le_mul_right _ (pow_pos hL 6); have hx:= hotParcel hs i (J i) (hw i); change M^4 ≤ B i*_ at hx
         apply le_trans ?_ hx; have h : 4*L^11 ≤ M:=by
            have hz':= mul_le_mul_of_nonneg_right hs.unit (pow_nonneg hL.le 11); have hh:= (pow_le_pow_right₀ hp (by decide:12≤14)).trans hs.least; linarith only [hz',hh,pow_nonneg hL.le 11]
         have hk:=mul_le_mul_of_nonneg_left h (pow_nonneg (zero_le_one.trans hm) 3); linarith only [hk]
      have hPay':4*M^3*L^3 ≤ B i*c^2:= by
         apply le_of_mul_le_mul_right _ (pow_pos hL 2); rw [mul_assoc (B i),←mul_pow,hh,one_pow,mul_one]; refine Eq.trans_le ?_ hPay; ring
      have hG := mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left ht hc) hr0; have ht' :0≤ M^3*L^3:=by positivity
      linarith only [hPay',hG,ht']
   have hh := Finset.sum_lt_sum_of_nonempty (ι:=T.Cell) Finset.univ_nonempty (fun i _=> hh' i); rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Finset.card_univ] at hh; rwa [← mul_assoc (ν:ℝ)] at hh
lemma patches (hi:k ≤ N)(h:Stove.Chart R r C e)(hs:safeCost G n T.side (Stove.haloFee R r) q C e t L)(hx:4*t+τ≤ (R).p.threshold)(hβ :4*t≤τ)(hP:∀ x: Face (Per n),(D).real (trigger x τ) ≤ (L⁻¹)^200) (he:Attempt R r τ q z f X) :
    ‖∫ U,f U∂ D‖ ≤ L⁻¹:=by
   have hY:=chance H T hv hi h hs hx hβ hP (neg_form z f he); rw [integral_neg] at hY; exact abs_le.mpr ⟨neg_le.mp hY,chance H T hv hi h hs hx hβ hP he⟩
end YM.OPE.Therm.Portolan
