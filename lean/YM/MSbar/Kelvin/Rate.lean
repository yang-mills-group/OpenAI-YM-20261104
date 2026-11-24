import YM.MSbar.Bakery.Plate
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Kelvin
open Function Filter MeasureTheory Cacao PowerSeries Finset Whisk
open scoped Topology BigOperators Classical
open Lattice Matrix
variable {ι σ τ:Type} [Fintype σ][Fintype ι][Fintype τ][DecidableEq σ] [DecidableEq ι]
    {l':ι→σ}{n:Side}{v : σ→ Site n}{k s: Matrix σ σ ℝ} {B : Matrix ι ι ℝ}
    (u : ι→σ)
-- injection from Active domain, following actual rotor. Est growth contracts.V
noncomputable def imbed (u:ι→σ):Matrix σ ι ℝ:=Matrix.of (fun i j=> if u j=i then 1 else 0)
noncomputable def extendM (u:ι→σ)(k: Matrix ι ι ℝ): Matrix σ σ ℝ:= imbed u*k*(imbed u).transpose
noncomputable def pinch (u:ι→σ)(k:Matrix σ σ ℝ): Matrix ι ι ℝ:= k.submatrix u u
local notation "ι!"=> imbed u
local notation "p!"=> pinch u k
local notation "e!"=> extendM u
variable (h:Injective u)
lemma trimmed (x:View σ): (imbed u).transpose*ᵥ x=fun i=>x (u i):=by ext i; simp [mulVec,imbed,dotProduct,ite_mul]
lemma stem_map (u:ι→σ)(g:Matrix σ τ ℝ): (imbed u).transpose*g=Matrix.of fun i j=> g (u i) j:=by ext i j; simp [Matrix.mul_apply, imbed,ite_mul]
lemma clipped : pinch u k=(imbed u).transpose*k*imbed u:=by rw [stem_map];ext i j; simp [Matrix.mul_apply,imbed,pinch,mul_ite]
include h
lemma both : (imbed u).transpose*imbed u=1:=by rw [stem_map]; ext i j; simp [imbed, h.eq_iff, Matrix.one_apply,eq_comm]
lemma shares (p:View ι) : (ι! *ᵥ p)∘u=p:=by rw [← show (imbed u).transpose*ᵥ(ι! *ᵥ p)= (ι! *ᵥ p) ∘u from trimmed u _,mulVec_mulVec,both u h,one_mulVec]
local notation "η!"=>View σ
omit h in
lemma inactive (i:σ)(hi:i ∉ Set.range u)(x:View ι): (imbed u*ᵥ x) i=0:=by
   apply Finset.sum_eq_zero; intro j _; change (if u j=i then (1:ℝ) else 0)*_= _; rw [if_neg (fun H=> hi ⟨_,H⟩),zero_mul]
omit h in
lemma squeezed {i j:σ}(hi:i∉Set.range u ∨ j∉Set.range u) : extendM u B i j=0:=by
   rcases hi with h|h
   · rw [extendM,Matrix.mul_assoc]; let V := B * (ι!).transpose; change (ι! *ᵥ fun a=> V a j) i=0; exact inactive u i h _
   unfold extendM; refine Finset.sum_eq_zero ?_; intro p hp; change _*(if u p=j then (1:ℝ) else 0)=0; rw [if_neg (fun hp=> h ⟨_,hp⟩),mul_zero]
-- block entry.DO
lemma embeds (k:Matrix ι ι ℝ) : pinch u (extendM u k)=k:=by
   rw [clipped]; unfold extendM; rw [← Matrix.mul_assoc,← Matrix.mul_assoc, both u h,Matrix.mul_assoc (1*_ : Matrix ι ι ℝ),both u h,mul_one,one_mul]
-- Schur algebra equations
noncomputable def vanish (u:ι→σ)(k: Matrix σ σ ℝ): Matrix σ σ ℝ:= 1-extendM u (pinch u k)⁻¹*k
local notation "v!"=> vanish u k
local notation "dp" =>(pinch u k)⁻¹
variable (hp: k.PosDef)
include hp
lemma planted : v! * imbed u=0:=by
    unfold vanish extendM; rw [Matrix.sub_mul, Matrix.one_mul]; apply sub_eq_zero.mpr; have ht:= (hp.submatrix h) -- args inspect
    suffices H: extendM u (pinch u k)⁻¹*k* imbed u=ι! from H.symm
    unfold extendM; rw [Matrix.mul_assoc (ι! * dp), ← Matrix.mul_assoc (ι! * dp) _ _, Matrix.mul_assoc (ι! * dp),Matrix.mul_assoc (ι! * dp),← clipped] -- try
    rw [Matrix.mul_assoc, (pinch u k).nonsing_inv_mul (isUnit_iff_ne_zero.mpr ht.det_pos.ne'),Matrix.mul_one] -- fix
lemma root_out {i:σ}(q:ι): vanish u k i (u q)=0:=by
    let p(q:ι):View σ:= ι! *ᵥ Pi.single q 1
    have hp: (v!)*ᵥ p q=0:=by unfold p; rw [mulVec_mulVec, planted u h hp, zero_mulVec]
    have he:p q=Pi.single (u q) 1:=by unfold p; ext i; simp [mulVec,dotProduct, imbed,Pi.single_apply, ite_mul,eq_comm]
    rw [he] at hp; have hh:= congr_fun hp i; simpa [Matrix.mulVec,dotProduct, Pi.single_apply,mul_ite] using hh -- of_apply danger
lemma van_license : v! * k⁻¹=k⁻¹- extendM u dp:=by unfold vanish; rw [Matrix.sub_mul, Matrix.one_mul,Matrix.mul_assoc _ k,k.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hp.det_pos.ne'),mul_one]
omit hp in
lemma van_solo (i : σ) (hz:i ∉Set.range u) (a:View σ): (vanish u k *ᵥ a) i=a i:=by rw [vanish,Matrix.sub_mulVec,one_mulVec]; simp only [Pi.sub_apply]; rw [extendM]; rw [← mulVec_mulVec,← mulVec_mulVec,← mulVec_mulVec,inactive _ _ hz]; abel
lemma wince : v! * k⁻¹*(v!).transpose + extendM u dp = k⁻¹:=by
    let P:=v!; let B:=extendM u dp; have hb: P*B=0:=by unfold B extendM; rw [← Matrix.mul_assoc,← Matrix.mul_assoc, show P*ι! = 0 from planted u h hp, Matrix.zero_mul,Matrix.zero_mul]
    have ht: (pinch u k).PosDef:= hp.submatrix h
    have hv: (k⁻¹).transpose=k⁻¹:=by simpa [IsHermitian] using hp.inv.1 -- syntax
    have hm: B.transpose=B:=by unfold B extendM; rw [transpose_mul,transpose_mul,transpose_transpose,show ((pinch u k)⁻¹).transpose=dp from by simpa [IsHermitian] using ht.inv.1,Matrix.mul_assoc]
    have he:k⁻¹*P.transpose=k⁻¹-B:=by rw [←hv,←transpose_mul _ k⁻¹,show P*k⁻¹=k⁻¹-B from van_license u h hp, Matrix.transpose_sub,hm]
    change P*k⁻¹ *P.transpose + B=_; rw [mul_assoc,he,mul_sub,hb,sub_zero, show P*k⁻¹ = k⁻¹-B from van_license u h hp,sub_add_cancel]
end YM.MSbar.Kelvin
