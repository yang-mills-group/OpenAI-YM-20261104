import YM.RG05Readout.Nuclear.Strings
/-! Finite bank around ball u: reexpress a translation through jet entries,
 not a global Fourier expansion. Coefficients measurable from the patch data.
 Active bank remembers any nonzero report envelope.Morph inherited by bumps.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Nuclear
open Tensor Analysis Function Filter Set MeasureTheory Native Pulse Push.FiniteDetection.Kelvin
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {n m d k:ℕ}{E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
variable {V J:Type}[Fintype V][DecidableEq V]
local notation "U"=>Cloud V
local notation "W"=> Wave V
abbrev Column (V:Type)[Fintype V][DecidableEq V](t:ℕ):= Σ i:Fin (t+1),Σ j:Ticket V i, ((fibre V i j).support)
abbrev popV (i:Column V d): V→Body:=i.snd.snd.val
abbrev deep (i:Column V d):ℕ:=i.fst.val
def print (v: W)(x:Column V d):ℂ:= (page V x.fst (Tensor.coeff v.val (deep x) 0) x.snd.fst)* ((fibre V x.fst x.snd.fst) x.snd.snd.val)
lemma stringer (v:W)(d:ℕ) : port v d= ∑ i:Column V d,print v i • joint Finset.univ (popV i):=by
   have ht(i:Fin (d+1))(j:Ticket V i): layD (Quill V i j)= ∑ k:((fibre V i j).support),((fibre V i j) k.val) • joint Finset.univ k.val:= by rw [unravel]; exact (Finset.sum_coe_sort _ (fun k=>((fibre V i j) k) • joint Finset.univ k)).symm
   let u:= fun i:ℕ=>layD (Tensor.coeff v.val i 0)
   rw [show port v d= ∑ i:Fin (d+1),u i from Subtype.ext (by simp only [AddSubmonoidClass.coe_finsetSum]; exact (Fin.sum_univ_eq_sum_range (fun i=> (u i).val) (d+1)).symm)]
   rw [Fintype.sum_sigma]; refine Finset.sum_congr rfl (fun i _=> ?_); unfold u; rw [song,Fintype.sum_sigma]; refine Finset.sum_congr rfl (fun j _=> ?_); rw [ht i j,Finset.smul_sum]; exact Finset.sum_congr rfl fun k _=>(mul_smul ..).symm
omit [DecidableEq V] in
lemma fork_zero (v:W): fork 1 0 v=v:=Subtype.ext <| funext fun y=>by change v.val (0+1 • y)=_; rw [zero_add,one_smul]
lemma converted (p:W)(hp:iteratedFDeriv ℝ (d+1) p.val=0) (r:ℝ)(x:U): fork r x p= ∑ i:Column V d,print (fork r x p) i • joint Finset.univ (popV i):=by
    let z:= fork r x p; have ht: iteratedFDeriv ℝ (d+1) z.val=0:= by funext y; unfold z; rw [shoots,hp, Pi.zero_apply,smul_zero];rfl
    have he:=abroad 0 z ht; unfold package at he; rw [neg_zero,fork_zero,fork_zero] at he; exact he.trans (stringer z d)
noncomputable def patchShift (x:E4)(r:ℝ) (f:Body):Body:= Native.pull (-r⁻¹ • x) r⁻¹ f
lemma backshift (r:ℝ)(hr:r ≠0)(x:E4)(f:Body) : Native.pull x r (patchShift x r f)=f:= Subtype.ext <| funext fun y=>by change f.val (-r⁻¹ • x+r⁻¹ • (x+r • y))=_; rw [smul_add,smul_smul,inv_mul_cancel₀ hr,neg_smul,one_smul,neg_add_cancel_left]
lemma print_local (v: W)(hp:iteratedFDeriv ℝ (d+1) v.val=0)(r:ℝ)(hr:r≠0)(x:U): v= ∑ i:Column V d,print (fork r x v) i • joint Finset.univ (fun j=> patchShift (x j) r (popV i j)):=by
    let l:= fork r x; let Q:=fork r⁻¹ (-r⁻¹ • x); have h: LeftInverse Q l:=by
        intro p; apply Subtype.ext; funext y; change p.val (x+r • (-r⁻¹ • x+r⁻¹ • y))=_; rw [smul_add,neg_smul,smul_neg,smul_smul,smul_smul,mul_inv_cancel₀ hr,one_smul,one_smul,add_neg_cancel_left]
    apply h.injective; change fork r x v=l _; rw [map_sum]; nth_rw 1 [converted v hp]; apply Finset.sum_congr rfl; intro k _; rw [map_smul]; apply congr_arg; apply Subtype.ext; funext y; change (∏ i:V,_)=∏ i:V,_; exact Finset.prod_congr rfl fun i _=> (congr_fun (congr_arg Subtype.val (backshift r hr (x i) (popV k i))) (y i)).symm -- arguments

lemma press_cost (x:Column V d)(v:W)(a:ℝ)(y:U){C:ℝ}(h:0<a)(hv: ‖iteratedFDeriv ℝ (deep x) v.val y‖≤ C) :
    ‖print (fork a y v) x‖ ≤ ‖(page V (deep x):Tensor.T U ℂ (deep x)→L[ℂ] _)‖* ((deep x).factorial:ℝ)⁻¹ * a^(deep x) * C* ‖(fibre V x.fst x.snd.fst) (popV x)‖ :=by -- edit
     let i:=deep x; let X:Tensor.T U ℂ i:= Tensor.coeff (fork a y v).val i 0; let A:=page V i; let z:=fibre V i x.snd.fst; have hp: ‖X‖≤((i.factorial:ℝ)⁻¹)*(a^i*C):=by
         unfold X Tensor.coeff; rw [shoots,smul_zero,add_zero,norm_smul,norm_smul]; rw [Real.norm_of_nonneg (pow_nonneg h.le _),Real.norm_of_nonneg (by positivity)]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv (pow_nonneg h.le _)) (by positivity)
     unfold print; rw [norm_mul]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
     exact (norm_le_pi_norm (A X) _).trans ((A.le_opNorm X).trans ((mul_le_mul_of_nonneg_left hp (norm_nonneg A)).trans_eq (by change ‖A‖*_=_; ring)))
noncomputable def mortar (V : Type)[Fintype V][DecidableEq V](K D:ℕ)(i:Column V K):ℝ:= 1+ ‖page V (deep i)‖* ((deep i).factorial:ℝ)⁻¹ * (D:ℝ)^(K+1-deep i)*‖fibre V i.fst i.snd.fst (popV i)‖
lemma mortar_pos (D:ℕ)(i:Column V k): 0 < mortar V k D i:= by unfold mortar; positivity
lemma palace (r:ℝ)(hr:0<r)(p:W)(D:ℕ)(x y:U)(z:Column V d){C:ℝ}(hc:0≤C)(hv:∀ u, ‖iteratedFDeriv ℝ (d+1) p.val u‖≤ C)(hx:‖y-x‖≤ D*r):
    ‖print (fork r x (package d y p-package d x p)) z‖ ≤ mortar V d D z*r^(d+1)*C:=by
    let i:=deep z; have h:i≤ d:=Nat.le_of_lt_succ z.fst.isLt
    have hp:= press_cost z (package d y p-package d x p) r x hr (congr_site x y p h (D*r) C (by positivity) hc hv hx); refine le_trans hp (le_trans (le_of_eq (b:= ‖page V (deep z)‖* ((deep z).factorial:ℝ)⁻¹ * (D:ℝ)^(d+1-deep z)* ‖fibre V z.fst z.snd.fst (popV z)‖*r^(d+1)*C) ?_) ?_)
    swap
    · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (show ‖page V (deep z)‖ * ((deep z).factorial:ℝ)⁻¹ * (D:ℝ)^(d+1-deep z)* ‖fibre V z.fst z.snd.fst (popV z)‖ ≤ mortar V d D z from le_add_of_nonneg_left zero_le_one) (pow_nonneg hr.le _)) hc)
    have hr : r^(d+1)= r^(deep z)*r^(d+1-i):= by rw [← pow_add, show deep z+(d+1-i)=d+1 from Nat.add_sub_of_le (h.trans d.le_succ)];
    rw [hr,mul_pow]; unfold i; ring
end YM.RG05Readout.Nuclear
