import YM.MSbar.Cacao.Gloss
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Cacao
open PowerSeries Finset Function Polynomial
open scoped BigOperators Classical
section
variable {R:Type*}[CommRing R][Algebra ℝ R] {p n j:ℕ} {a f g:PowerSeries R}
local notation "χ"=> PowerSeries.X
local notation "H"=> PowerSeries R
noncomputable def Scan (r:ℕ) (f:PowerSeries R): PowerSeries R:= PowerSeries.mk fun i=> PowerSeries.coeff (r+i) f
lemma sprig (r:ℕ)(t:H)(ht: ∀ i,i<r→ PowerSeries.coeff i t=0) : t=χ^r*Scan r t:=by
    apply PowerSeries.ext; intro i; rw [PowerSeries.coeff_X_pow_mul']; split
    next he=> rw [Scan,PowerSeries.coeff_mk]; congr;omega
    next h=> exact ht i (by omega)
lemma ribbon (r:ℕ) (a:H) (i:ℕ)(h:i<r): PowerSeries.coeff i (χ^r*a)=0:=by
   rw [PowerSeries.coeff_X_pow_mul'];split; next hx=>omega
   next h=>rfl
lemma teen (a g:H)(hr:n < p+p)(j:ℕ) : Lap n ((a+χ^p*g)^(j+1)) (a^(j+1)+(j+1:ℝ) • (χ^p*g*a^j)):=by
    let G:=χ^p*g
    induction j with |zero=> simp; exact fun _ _=> rfl|succ k ih=>
       intro i hi; let b:= a^k; let t:=(k+1:ℝ); have hm:= (Lap.rises ih (g':=a+G) (fun _ _=>rfl) i hi); rw [pow_succ _ (k+1)]
       apply hm.trans
       have he: (a^(k+1)+t • (G*b))*(a+G)=(a^(k+2)+(t+1) • (G*a^(k+1)))+t • (χ^(p+p)*(g^2*a^k)):=by
            unfold G b; rw [add_mul,smul_mul_assoc,mul_add,mul_add,smul_add]; rw [pow_add (n:=p) (a:=χ) (m:=p),show _*(g^2 * a^k)=(χ^p*g*a^k)*(χ^p*g) from (by ring)]; rw [add_smul t,one_smul]; rw [show (χ^p*g*a^k)*a=χ^p*g*a^(k+1) by ring,pow_succ _ (k+1),mul_comm (a^(k+1)) (χ^p*g)]; abel
       rw [he,map_add, PowerSeries.coeff_smul,ribbon (p+p) _ _ (hi.trans_lt hr),smul_zero,add_zero]; unfold G t; push_cast; rfl
lemma lap_sub (h:Lap n (Spring f) (Spring g))(hh:Kind f)(hg:Kind g): Lap n f g:=by
    induction n with |zero=> intro i hi;rw [Nat.eq_zero_of_le_zero hi,hh,hg]|succ n ih=>
       specialize ih (fun i hi=> h i (hi.trans (Nat.le_succ n))); intro i hi; by_cases hx:i ≤ n; exact ih _ hx
       have hz:i=n+1:=by omega
       have hT:=gains hh hg ih; rw [←hz,h i hi, sub_self] at hT; exact sub_eq_zero.mp hT.symm
lemma ripple (hf:Kind f)(a:H)(T:ℕ)(ht:0<T): Kind (f+χ^T*a) := by unfold Kind; rw [map_add,hf,ribbon T a 0 ht,zero_add]
lemma column (r:ℕ) (hf:Kind f) (a:H) (hi: 0<r)(ht: n<r+r) : PowerSeries.coeff n (Spring (f+χ^r*a) -Spring f) = PowerSeries.coeff n (χ^r * a * Spring f) :=by
    let g:=χ^r*a; have he:= ripple hf a r hi; have hh:Kind g:=ribbon _ _ 0 hi
    let Hf(i:ℕ):= (i.factorial:ℝ); have hM : Lap n (Spring f) (Aroma f n):= fun i hi=>issues hf hi
    unfold g at hh; rw [_root_.map_sub,issues he (Nat.le_add_right n 1), issues hf (Nat.le_add_right n 1),(Lap.rises (f:=χ^r*a) (fun _ _=> rfl) hM n le_rfl)]
    unfold Aroma; rw [map_sum,map_sum,Finset.mul_sum, map_sum, ← Finset.sum_sub_distrib, Finset.sum_range_succ']; nth_rewrite 1 [pow_zero]; rw [pow_zero,sub_self, add_zero]; refine sum_congr rfl fun i _=>?_
    rw [PowerSeries.coeff_smul,teen f a ht i _ le_rfl,map_add,smul_add,PowerSeries.coeff_smul, PowerSeries.coeff_smul,add_sub_cancel_left, smul_smul,from_1 (0:ℝ→ₗ[ℝ]ℝ) (by simp) i,mul_smul_comm, PowerSeries.coeff_smul] -- order
end
open MeasureTheory Matrix MvPolynomial Further.GaussianScalar
variable {σ ι :Type} [Fintype ι][Fintype σ][DecidableEq ι][DecidableEq σ]
local notation "χ"=> PowerSeries.X
local notation "P"=> Pot σ
local notation "H"=> PowerSeries (Pot σ)
variable (v: Matrix σ ι ℝ) (x: View σ) {g: Matrix ι ι ℝ} (h:g.PosDef) (f F:PowerSeries (Pot σ))
local notation "p!"=>PowerSeries.coeff
set_option quotPrecheck false
local notation "L!"=> v*g*v.transpose
local notation "μ!"=>fieldLaw g
variable (k:σ→σ→ℝ)
def growP (r:ℕ) := Scan r (confect k (f+PowerSeries.X^r*F)-confect k f)
local notation "P0"=>Spring f
local notation "χG"=>confect k f
local notation "θ"=> growP
variable {n p r :ℕ}
lemma vac_merge (hf:Kind f)(hh:0<r): confect k (f+χ^r*F)= χG+χ^r*growP f F k r:=by
   let A':=f+χ^r*F; let t:=confect k A'; let d:=χG; let e:=(t-d); have hx:= ripple hf F r hh
   have hL(i:ℕ)(he:i<r): p! i t=p! i d:=by
       have hC: Lap i A' f:=fun n hn=> by unfold A'; rw [_root_.map_add,ribbon r F n (hn.trans_lt he),add_zero]
       have hG: Lap i (normalized k A') (normalized k f):=by
           apply lap_sub _ (airy hx).1 (airy hf).1; rw [(airy hx).2,(airy hf).2]; exact fun j hk=>by rw [Gallery,Gallery, PowerSeries.coeff_mk,PowerSeries.coeff_mk,hC.boots j hk]
       unfold t d confect; rw [PowerSeries.coeff_map,PowerSeries.coeff_map,hG i le_rfl]
   have hv:= sprig r e (fun i hi=>by unfold e; rw [_root_.map_sub,hL _ hi,sub_self]); change t=χG+_; rw [show χ^r* growP f F k r=e from hv.symm]; unfold e d; abel
-- polynomial mark-source height: R arbitrary.Scale note.Numeric volume independent. True normalized quotient at fixed finite size
include h
lemma aromaEval {r:ℕ} (hf:Kind f) (hp:r>n) :
   MvPolynomial.eval x (p! n (growP f F (v*g*v.transpose) r * Spring (confect (v*g*v.transpose) f))) = ∫ z:View ι, MvPolynomial.eval (x+v *ᵥ z) (p! n (F* Spring f))∂fieldLaw g :=by
   have hr:0<r:=by omega
   let k:=v*g*v.transpose; let m:=f+χ^r*F; have ht:=ripple hf F r hr; let L:=L!; let q:= confect k f; let X:= confect k (f+χ^r*F)
   have hp₀:=column r hf F hr (show r+n<r+r by omega)
   let v₀:=growP f F k r; have hX:X=q+χ^r*v₀:=vac_merge f F k hf hr; have hx: p! (r+n) (Spring X-Spring q)=p! n (v₀*Spring q):=by rw [hX,column r (sugar _ hf) v₀ hr (show r+n<r+r by omega), mul_assoc,Nat.add_comm r n,PowerSeries.coeff_X_pow_mul]
   -- hp₀ should simplify
   rw [mul_assoc,Nat.add_comm r n,PowerSeries.coeff_X_pow_mul] at hp₀; rw [Nat.add_comm n r] at hp₀
   rw [show p! n _=_ from hx.symm, _root_.map_sub,_root_.map_sub,show p! n _=_ from hp₀.symm,_root_.map_sub] -- inspect
   simp_rw [_root_.map_sub]; rw [show MvPolynomial.eval x (p! (r+n) (Spring X))=_ from goodie v x h ht _,show MvPolynomial.eval x (p! (r+n) (Spring q))=_ from goodie v x h hf _,MeasureTheory.integral_sub ((grille v h _ x 1 (by norm_num)).integrable le_rfl) ((grille v h _ x 1 (by norm_num)).integrable le_rfl)]
end YM.MSbar.Cacao
