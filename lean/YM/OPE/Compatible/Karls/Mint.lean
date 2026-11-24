import YM.OPE.Compatible.Javelin.Trot
/-! # homogeneous crowns, going backwards. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function ContinuousLinearMap
open scoped Topology BigOperators Classical
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{m k i:ℕ}{q:ℝ}(p:E→L[ℝ] E)
local notation "X!"=> E→L[ℝ] E
abbrev KernP (f:E→L[ℝ] E)(u:ℝ)(s:ℕ):Submodule ℝ E:= LinearMap.ker (Ux f u^s).toLinearMap
def portC (q:ℝ)(m:ℕ):KernP p q m →L[ℝ] KernP p q m:= (p ∘L (KernP p q m).subtypeL).codRestrict _ (by
     intro i; change (Ux p q^m) (p i.val)=0; rw [← byway, (Edit p q|>.pow_left m).eq, byway,show (Ux p q^m) i.val =0 from i.property,map_zero])
lemma portables (f:KernP p q m)(i:ℕ): ((portC p q m^i) f).val=(p^i) f.val:=by induction i with | zero=>rfl| succ i ih=> rw [pow_succ',pow_succ',byway,byway]; change p (((portC p q m ^ i) f).val)= _;rw [ih]
lemma offsetA (f:KernP p q m)(i:ℕ): ((Ux (portC p q m) q ^ i) f).val=(Ux p q ^ i) f.val:=by induction i with | zero=>rfl| succ i ih=> rw [pow_succ',pow_succ',byway,byway]; let g:=Ux (portC p q m) q; let a:=(g^i) f; change p a.val-q • a.val=_; rw [show a.val=_ from ih]; rfl
lemma honestC : Ux (portC p q m) q ^ m=0:=by ext1 x; exact Subtype.ext ((offsetA p x m).trans (show (Ux p q ^m) x.val=0 from x.property))
lemma RiseP (h:(Ux p q ^m)=0)(hx:0 ≤ q){s:ℝ}(hv:q<s):∃ c,Hex s (fun i=>p^i) c:=by
     obtain ⟨c,hc,H⟩:= AltE p q m hx hv; refine ⟨c,fun i=>?_⟩; apply (p^i).opNorm_le_bound (by have ht:=hx.trans hv.le; positivity); intro w; exact (H w (by rw [h]; rfl) i).trans_eq (by ring)
-- finite inverse
lemma backward (h:Ux p q^m=0)(hp:0 < q): ∃ X:X!,X*p=1∧p*X=1∧Ux X q⁻¹^m=0:=by
    let G:=Ux p q; let W:X!:=q⁻¹ • p; let H:=1-W; have ht: H^m=0:=by
        have hh:H=(-q⁻¹) • Ux p q:= by
             ext x; change x-q⁻¹ • p x=(-q⁻¹) • (p x-q • x); rw [smul_sub,neg_smul,neg_smul,smul_smul,inv_mul_cancel₀ hp.ne',one_smul]; abel
        rw [hh,smul_pow,h,smul_zero]
    let R:= ∑ i∈Finset.range m,H^i
    have he:R*W=1:=by
         have he:=geom_sum_mul H m; rw [ht,zero_sub, show H-1= -W from by unfold H; abel] at he; exact neg_injective (by rw [←mul_neg];exact he)
    have hy: W*R=1:=by
         have he:=mul_geom_sum H m; rw [ht,zero_sub, show H-1= -W from by unfold H; abel] at he; exact neg_injective (by rw [←neg_mul];exact he)
    let X:=q⁻¹ • R; have hz:X*p=1:=by unfold X; rw [smul_mul_assoc,← mul_smul_comm]; exact he
    have hQ:p*X=1:=by unfold X; rw [mul_smul_comm,←smul_mul_assoc]; exact hy
    refine ⟨X,hz,hQ,?_⟩; have hP: Ux X q⁻¹ =(-q⁻¹) • (X*G):=by
         unfold Ux; rw [show G=p-q • 1 from rfl,mul_sub,mul_smul_comm,mul_one,hz,neg_smul,smul_sub,smul_smul,inv_mul_cancel₀ hp.ne',one_smul]; abel
    have hc:Commute X G:=by change X*G=G*X; unfold G Ux; rw [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc q 1 X,one_mul,mul_one,hQ,hz]
    rw [hP,smul_pow,hc.mul_pow,show G^m=0 from h,mul_zero,smul_zero]
def Fleet (q:ℝ)(m:ℕ)(hp:0 < q):KernP p q m→L[ℝ] KernP p q m:= Classical.choose (backward _ (honestC p) hp)
lemma wineP (hp:0 < q): Fleet p q m hp * portC p q m=1 ∧ portC p q m * Fleet p q m hp=1 ∧ Ux (Fleet p q m hp) q⁻¹^m=0:= Classical.choose_spec (backward _ (honestC p) hp)
end YM.OPE.Hark
