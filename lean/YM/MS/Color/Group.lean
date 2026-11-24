import YM.MS.Local.Coh
import YM.MS.Color.Only
/-!
# Color rotation as pointwise finite multilinear operations

Works in full Q kernels and on local jets; $G$ includes its other components.
This is an actual action so averaging over the compact group is available.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Color
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor Submodule -- MatrixLet later
open Landau
open Complex (I)
open scoped Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {P D : Type}
def wc (u:G.El) (i j : CI G):ℂ:= weight u i j
lemma weight_group (k l:G.El) (i j:CI G) : weight (k*l) i j=∑ c:CI G, weight l i c*weight k c j:=by
   unfold weight; rw [Gauge.adjoint_mul]; let f:=G.adjoint l (eb G i)
   have ht : ∑ c:CI G,weight l i c • eb G c=f:=color_sum f; change G.adjoint k f j= _; rw [← ht,map_sum]; simp only [WithLp.ofLp_sum,Finset.sum_apply, map_smul, PiLp.smul_apply, smul_eq_mul]; rfl
lemma weight_adj (k:G.El) (i j:CI G): weight k i j=weight k⁻¹ j i:= by
   let u:G.Color →ₗᵢ[ℝ] G.Color:= ⟨G.adjoint k, G.norm_adjoint k⟩
   let V := G.adjoint k⁻¹ (eb G j)
   have hv : u V=eb G j:= by change G.adjoint k _=_; unfold V; rw [← G.adjoint_mul]; simp
   have hs : inner ℝ (eb G j) (G.adjoint k (eb G i))=inner ℝ (eb G i) V:= by
       change inner ℝ _ (u _)=_; rw [← hv,u.inner_map_map]; exact real_inner_comm ..
   simpa  [eb,weight,V,← OrthonormalBasis.repr_apply_apply, EuclideanSpace.inner_single_left] using hs
@[simp] lemma wc_start (i j : CI G): wc 1 i j= if i=j then 1 else 0:=by classical simp [wc,weight,PiLp.single_apply,eq_comm]; split <;> simp_all
lemma wc_conjugate (g:G.El) (i j:CI G): wc g i j= wc g⁻¹ j i:=congr_arg _ (weight_adj g i j)
lemma wc_group (g h:G.El) (i j:CI G): wc (g*h) i j=∑ k:CI G,wc h i k*wc g k j:= by push_cast [wc, weight_group]; rfl
@[simp] lemma star_weight (b:G.El) (i j:CI G): star (wc b i j)=wc b i j:=by simp [wc]

-- shim notation.
abbrev setLeg (d : Note G D P) (i: CI G) : Note G D P:= ((d.1.1,i),d.2)
variable (k l:G.El) (F : Score G D P)

def repeatC (k:G.El): Score G D P→ₗ[ℂ] Score G D P where
   toFun f w:= Landau.solo k w f
   map_add' f g:=funext fun x=> Landau.solo_add (f:=f) (g:=g) k x
   map_smul' c f:= funext fun x=> Landau.solo_mul (f:=f) k c x
lemma rep_book l : repeatC k F l= solo k l F:=rfl
@[simp] lemma rep_nil : repeatC k F []=F []:=rfl
lemma c_prefix (d: Note G D P): Koszul.D d (repeatC k F)=∑ i:CI G,wc k d.1.2 i • repeatC k (Koszul.D (setLeg d i) F):= by
   rcases d with ⟨⟨i,c⟩,p⟩; ext l; simp only [at_D,rep_book,solo,Finset.sum_apply, Pi.smul_apply]; rfl
lemma repeat_cons (d:Note G D P) l : repeatC k F (d::l) = ∑ i:CI G,wc k d.1.2 i*repeatC k (Koszul.D (setLeg d i) F) l:= by rw [D_eval _ (repeatC k F),c_prefix]; simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
lemma walk_comp : repeatC k (repeatC l F) = repeatC (l*k) F:= by
    ext v; induction v generalizing F with
    | nil=> simp
    | cons i v ih=> rw [repeat_cons,repeat_cons]; simp_rw [c_prefix,map_sum,map_smul,Finset.sum_apply, Pi.smul_apply,smul_eq_mul, ih,wc_group,Finset.mul_sum,Finset.sum_mul, mul_assoc]; rw [Finset.sum_comm]
lemma walk_id : repeatC 1 F=F:= by
   ext v; induction v generalizing F with
   | nil=> simp
   | cons i v IH=> rw [repeat_cons]; simp [ite_mul,IH,setLeg]

-- symm of kernels at all legs (local)
lemma repeat_sym (k : G.El) {F : Score G D P} (hf : Koszul.Symm (field parity) F) : Koszul.Symm (field parity) (repeatC k F):= by
   intro l i j r; induction l generalizing F with
   | nil=> rw [List.nil_append, List.nil_append, repeat_cons, repeat_cons]; simp_rw [repeat_cons, Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a _=> ?_; refine Finset.sum_congr rfl fun b _=> ?_; rw [hf.commute (setLeg j a) (setLeg i b),map_smul]; dsimp [field,parity]; ring
   | cons a l ih => simp only [List.cons_append,D_eval a (repeatC k F),c_prefix,Finset.sum_apply,Pi.smul_apply, smul_eq_mul]; simp_rw [ih (hf.drop (setLeg a _)),Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_; ring
end YM.MS.Color
