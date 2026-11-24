import YM.OPE.Therm.PackPatch
/-!
# Cost polynomial simplification
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm.Portolan
open Function Set Filter RG Lattice Wilson MeasureTheory Cells House Cradle
open scoped BigOperators Classical Topology ENNReal Matrix.Norms.Frobenius
variable {n:Side} {G:Gauge} {U V : Config G n}
local notation "𝒞" => Config G n
variable {T:Tiling n}
variable {R:Rep G n}{r q:ℕ}{C e τ t L K:ℝ}
local notation "V"=> (Fintype.card T.Cell:ℝ)
local notation "p₀a"=> (parcel R r q)
local notation "M"=> (T.side.val :ℝ)
local notation "K₀"=> Stove.haloFee R r
local notation "K*"=> (premium T R r t C)
local notation "Ω"=> (touchW (G:=G) t)
local notation "F"=> (Fintype.card PlaqAxes:ℝ)

structure safeCost (G:Gauge)(n f:Side)(k q:ℕ)(C e u L:ℝ) : Prop where
   bare : Fintype.card PlaqAxes≤ L
   field : touchW (G:=G) u 1 ≤ L
   unit : 10000 ≤ L
   home : k+1 ≤ L
   feat : q ≤ L
   temp : u≤1
   narrow : u>0
   heat : 0 ≤ C
   powerK : C ≤ L
   low : e*L^15 ≤1
   least : L^14 ≤ f.val
   most : (f.val:ℝ) ≤ L^16
-- note G shadow F not used (P cost) n parameter spare
variable (h:safeCost G n T.side (Stove.haloFee R r) q C e t L)
include R r h
lemma safe_min :1 ≤ L:= le_trans (by norm_num) h.unit
lemma fuel : 0≤Ω 1:= by
   have hh:0<t:=h.narrow; unfold touchW; apply mul_nonneg (by positivity); apply Real.log_nonneg; exact (one_le_div hh).mpr (h.temp.trans (by norm_num)) -- lemma check
lemma hotParcel (i:T.Cell) (A:Finset (Site n))(he: (gx T p₀a)^4 ≤ A.card*(4*q+1)^4):
    M^4 ≤ A.card * L^6:=by
   have hl:=zero_lt_one.trans_le (safe_min h)
   let x:=M; let j:= (gx T p₀a:ℝ); let u:= (K₀:ℝ); let a:= (q:ℝ)
   have hP: (p₀a:ℝ) ≤ 4*L:= by unfold Portolan.parcel; push_cast; linarith only [h.home,h.feat,h.unit]
   have hT:20*L≤ x:=by
      apply le_trans ?_ h.least; have hu:= h.unit; have hh:= pow_le_pow_right₀ (safe_min h) (by decide: 2≤14); linarith only [mul_le_mul_of_nonneg_right hu hl.le, hh,hl]
   have hx:x ≤ j+2*(p₀a:ℝ):=by unfold x j; exact_mod_cast (by unfold gx; omega : T.side.val ≤ gx T p₀a + 2*p₀a)
   have ht : x ≤ 2*j:=by linarith only [hx,hP,hT]
   have hz :j^4 ≤ (A.card:ℝ)*(4*a+1)^4:=by unfold j a; exact_mod_cast he
   have hh := pow_le_pow_left₀ (show 0 ≤ 4*a+1 by unfold a; positivity) (show 4*a+1≤ 5*L by linarith only [show a≤L from h.feat, h.unit]) 4 -- param duplicate
   refine le_trans (pow_le_pow_left₀ (show 0≤x from Nat.cast_nonneg _) ht 4) (le_trans ?_ (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (safe_min h) (by decide:5≤6)) (Nat.cast_nonneg _)))
   have hN: 10000*L^4 ≤ L^5:= by have hh:=mul_le_mul_of_nonneg_right h.unit (pow_nonneg hl.le 4); linarith only [hh];
   linarith only [hz,mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg A.card),mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg A.card)]

lemma lint : 0≤ K* ∧ K* ≤ 10*L*(M+1)^4:=by
    let A:=gx T (K₀+1); let i:=T.side.val; let Y:=A -- number of legal centers.Need bound edges via suite
    let x:ℝ:=Ω 1; let W:=edges T 0; have hi:x≥0:=fuel h
    let t:=T; have hz: W.card≤ (i+1)^4*4:=by
       have hp : W⊆ suite T 0 ×ˢ Finset.univ (α:=Axis):=by
          intro x hx; exact Finset.mem_product.mpr ⟨(host T).mpr ((lin_room T).mp (House.holds T hx)).1,Finset.mem_univ _⟩
       apply (Finset.card_le_card hp).trans_eq; rw [Finset.card_product,hall_size]; simp [Axis,i]
    have H:x≤L:= h.field; have hm : (A:ℝ) ≤ (M+1):=by exact_mod_cast (by unfold A gx; omega : A ≤ T.side.val+1)
    have hs : Ω W.card=W.card*x:=by simp only [x,touchW,Nat.cast_one,one_mul,mul_assoc]
    unfold premium; change 0 ≤ 2*((A:ℝ)^4*C)+Ω W.card ∧ _; rw [hs]; have hc:0≤C:= h.heat
    refine ⟨by positivity,?_⟩; change 2*((A:ℝ)^4*C)+(W.card:ℝ)*x ≤ _; have hα:=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity :0≤ (A:ℝ)) hm 4) hc
    let z:ℝ:= M+1; have hβ:=mul_le_mul_of_nonneg_left h.powerK (pow_nonneg (by positivity :0≤ M+1) 4)
    have hχ:= mul_le_mul (show (W.card:ℝ) ≤ (M+1)^4*4 by exact_mod_cast hz) H hi (by positivity); have hh:=mul_nonneg (hi.trans H) (pow_nonneg (by positivity:0≤ M+1) 4)
    linarith only [hα,hβ,hχ,hh]
set_option maxRecDepth 3000 in
private lemma frost : ((M+1)^4 + K*)*((M+1)^4*F)*(L⁻¹)^200 ≤ 1:=by
    have hl : 1≤ L:= safe_min h; have hh:=zero_lt_one.trans_le hl; let x:= (M+1)^4
    have ha:x ≤ 16*L^64:=by
       have H:= pow_le_pow_left₀ (show 0 ≤ M+1 by positivity) (show M+1≤2*L^16 by linarith only [one_le_pow₀ (n:=16) hl,h.most]) 4
       apply H.trans_eq; ring
    have hz : x+ K* ≤11*x*L:=by have hx:= (lint h).2; change K*≤ _*x at hx; have ht:=mul_le_mul_of_nonneg_left hl (by unfold x; positivity : 0≤x); rw [mul_one] at ht; linarith only [ht,hx]
    have hα:1≤L^200:= one_le_pow₀ hl
    change (x+ K*)*(x*F)*_≤_; rw [inv_pow,mul_inv_le_iff₀ (zero_lt_one.trans_le hα), one_mul]; have hN :=mul_le_mul hz (mul_le_mul ha h.bare (by positivity) (by positivity)) (by unfold x; positivity) (by unfold x; positivity)
    have he' : (11*x*L)*(16*L^64*L) ≤ 10000*L^130:=by
       have hu:=mul_le_mul_of_nonneg_right ha (by positivity :0≤L^66); linarith only [hu,pow_nonneg hh.le 130]
    refine hN.trans (he'.trans (le_trans ?_ (pow_le_pow_right₀ hl (by decide: 131≤200)))); have he' := mul_le_mul_of_nonneg_right h.unit (pow_nonneg hh.le 130); linarith only [he']
omit R r h in
lemma allowance {G:Gauge}(u:ℝ)(p₀:ℕ): touchW (G:=G) u p₀=p₀*touchW (G:=G) u 1:= by simp only [touchW,Nat.cast_one,one_mul,mul_assoc]
lemma weather (hv:T.kind=.site)(P:T.Cell→ℝ) : graphRate T R r t C e P + V*((M+1)^4+ K*)*((M+1)^4*F)*(L⁻¹)^200 ≤ (∑ i,P i)+ V*M^3*L^3:=by
    have hmin:=safe_min h; have hl:=zero_lt_one.trans_le hmin; have hm:1 ≤ M:= (one_le_pow₀ (n:=14) hmin).trans h.least
    let x:ℝ:= V; let N:=T.side.val; let u:=K₀+1; let W:ℝ:=M; have hx: 0 ≤ x:= Nat.cast_nonneg _
    have he : edgeLoss T R r C e ≤ x*W^3*(10*L^2):=by
       let p:ℝ:= (Fintype.card (Site n):ℝ); let a:ℝ:= (vacant T u).card; have ha:a ≤ x*(8*L*W^3):= by
          have he : (u:ℝ) ≤ L:= by simpa only [u,Nat.cast_add,Nat.cast_one] using h.home
          refine (outsideFee T hv (show 1≤u by unfold u; omega)).trans ?_; change x*(8*(u:ℝ)*W^3) ≤ _; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num)) (pow_nonneg (by unfold W; positivity) _)) hx
       have hP : p=x*W^4:=by unfold x W p; exact_mod_cast (by rw [site_card,site_card,T.units.exact_size,mul_pow] : Fintype.card (Site n)=Fintype.card T.Cell *N^4)
       have ht : W*e ≤ L:= by
          apply le_of_mul_le_mul_right _ (pow_pos hl 15); have he:= mul_le_mul_of_nonneg_left h.low (show 0≤W from Nat.cast_nonneg _); linarith only [he,show W ≤ L^16 from h.most]
       have h₁:=mul_le_mul ha h.powerK h.heat (by have hh:0≤W:= Nat.cast_nonneg _; positivity); have h₂:=mul_le_mul_of_nonneg_left ht (show 0≤x*W^3 by have hh:0≤W:= Nat.cast_nonneg _; positivity); have h₃:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hmin (by decide: 1≤2)) (show 0≤x*W^3 by have hh:0≤W:= Nat.cast_nonneg _; positivity)
       change a*C + p*e ≤ _; rw [hP]; linarith only [h₁,h₂,h₃,mul_nonneg (show 0≤x*W^3 by have hh:0≤W:= Nat.cast_nonneg _; positivity) (sq_nonneg L)]
    have hc:Ω (seam T).card ≤ 64*x*W^3*L:=by rw [allowance]; exact (mul_le_mul (seamCount T hv) h.field (fuel h) (by positivity)).trans_eq (by unfold x W; ring)
    have hh : ((V*(((M+1)^4+ K*)))*((M+1)^4*F))*(L⁻¹)^200 ≤ x:=by
       change (x* _)*_*_ ≤ x; rw [mul_assoc x _ _,mul_assoc x _ _]; calc
          _ ≤ x*1:= mul_le_mul_of_nonneg_left (frost h) hx
          _ =x:=mul_one x
    unfold graphRate; apply (add_le_add_right hh _).trans; unfold x W at *; have hL:Real.log 3≤3:=Real.log_le_self (by norm_num)
    have hB : V*((3:ℝ)+1)+ V*M^3*(64*L+20*L^2) ≤ V*M^3*L^3:=by
       have hA:4+64*L+20*L^2 ≤ L^3:=by have hP:= mul_le_mul_of_nonneg_right h.unit (sq_nonneg L); nlinarith only [hP, one_le_pow₀ (n:=2) hmin, mul_le_mul_of_nonneg_right hmin hl.le]
       rw [mul_assoc V, ← mul_add,mul_assoc V]; apply mul_le_mul_of_nonneg_left _ hx; linarith only [mul_le_mul_of_nonneg_left hA (pow_nonneg (zero_le_one.trans hm) 3), one_le_pow₀ (n:=3) hm]
    linarith only [hB,mul_le_mul_of_nonneg_left hL hx,he,hc]
end YM.OPE.Therm.Portolan
