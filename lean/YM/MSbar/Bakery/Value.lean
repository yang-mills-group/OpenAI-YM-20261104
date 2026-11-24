import YM.MSbar.Bakery.Glance
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bakery
open Function Filter Finset Cacao MeasureTheory Whisk
open scoped Topology BigOperators Classical ContDiff
variable {σ ι :Type}[Fintype σ] [DecidableEq σ]
open Lattice MvPolynomial Analysis Set Metric
local notation "P"=>Pot σ
local notation "V"=>View σ
variable {x y:View σ}{f g: View σ→ℝ}{F:Pot σ}{X:Set (View σ)}{p m k q :ℕ}{u t a r b:ℝ} {n:Side}{l:σ→Site n}{Y W:Finset (Site n)}
def value (l:σ→ Site n)(W:Finset (Site n))(a:ℝ)(p:ℕ)(x:View σ)(f: View σ→ℝ)(L:List σ):ℝ:= spread l W a p L *|glance f L x|
-- Sensitivity on closed product log boxes.Unity anchors.L.O.
def Phase (l:σ→Site n)(W:Finset (Site n))(a:ℝ)(p k:ℕ)(f: View σ→ℝ) (X:Set (View σ))(t:ℝ): Prop:= 0 ≤ t ∧ ∀ H:List σ → View σ,(∀ L:List σ,H L∈X)→Yarn k (fun L=> value l W a p (H L) f L) ≤ t
structure Seed (l:σ→Site n)(W:Finset (Site n))(a:ℝ)(p k:ℕ)(f:View σ→ℝ)(X:Set (View σ))(t:ℝ) :Prop where
   alive (x:View σ): x∈X→ ContDiffAt ℝ (k:ℕ∞ω) f x
   bill (j:ℕ): j≤ k → Phase l W a p j f X t
-- track root δ difference x to y.D.Main fee bound.S.
lemma banker (x:View σ):x=∑ i:σ,x i • Pi.single i (1:ℝ):=by
    ext1 j; rw [Finset.sum_apply]; simp [Pi.single_apply, mul_ite]
-- line parameter.Pa.Y.P. 
lemma lamp (f:V→ℝ)(x y:View σ)(a:ℝ) (hf:DifferentiableAt ℝ f (x+a • y)): HasDerivAt (fun t:ℝ=> f (x+t • y)) (∑ i,y i * D (Pi.single i 1) f (x+a • y)) a:=by
   let L:=fderiv ℝ f (x+a•y); have hk :HasDerivAt (fun z:ℝ=> x+z•y) y a:=by simpa using (((hasDerivAt_id' a).smul_const y).const_add x)
   rw [show (∑ i:σ,y i*_)=L y from ?_]; exact hf.hasFDerivAt.comp_hasDerivAt a hk
   conv_rhs => rhs;rw [banker y]
   rw [_root_.map_sum];exact Finset.sum_congr rfl fun i _=> (L.map_smul _ _).symm
-- field MVT form.Health.Conv x.Global Pay deposits.Required.O.No uniform angular norms.
lemma smiled (x y:View σ) (X:Set (View σ))(ht:Convex ℝ X)(hx:x∈X) (hy:x+y∈X): ∀ t:ℝ,t ∈Icc (0:ℝ) 1 →x+t • y∈X:=by
   intro t hk; have he:(1-t)+t=1:=by ring
   have hv:= ht hx hy (sub_nonneg.mpr hk.2) hk.1 he
   rw [smul_add,← add_assoc,← add_smul,he,one_smul] at hv; exact hv
lemma cutAt (L:List σ)(ht :Convex ℝ X)(hx:x∈X)(hy:y∈X)(ha:∀ z∈X,ContDiffAt ℝ ((L.length+1:ℕ):ℕ∞ω) f z): ∃ z∈X,
    glance f L y- glance f L x= ∑ i:σ,(y i - x i)* glance f (L++[i]) z:= by
   let u:= y-x; have hv:x+u=y:= add_sub_cancel ..; let F(a:ℝ):=x+a • u; let v(a:ℝ):= glance f L (F a); let e(a:ℝ):=∑ i:σ,(y i-x i)* glance f (L++[i]) (F a); have hi t (h:t∈Icc (0:ℝ) 1):F t∈X:=smiled x u X ht hx (hv ▸ hy) t h -- ▸ error
   have h t (he:t∈Icc (0:ℝ) 1): HasDerivAt v (e t) t:=by
       have hh: DifferentiableAt ℝ (glance f L) (F t):= (glow L (ha _ (hi t he)) (n:=1) (by omega)).differentiableAt (by norm_num)
       unfold v e; simp_rw [glance_end]; exact lamp (glance f L) x _ _ hh
   obtain ⟨c,hc,hF⟩:= exists_deriv_eq_slope v (a:=0) (b:=1) zero_lt_one (fun _ he=> (h _ he).continuousAt.continuousWithinAt) (fun _ he=> (h _ (Ioo_subset_Icc_self he)).differentiableAt.differentiableWithinAt)
   have hvx:= Ioo_subset_Icc_self hc; refine ⟨F c, hi c hvx,?_⟩; rw [(h c hvx).deriv] at hF; simp only [v,F,one_smul,hv,zero_smul,add_zero,sub_zero,div_one] at hF; exact hF.symm
-- sup assignment with budget.Point.Order.K
lemma costMove (ha:0 ≤ a) (ht :Convex ℝ X) (hy:k ≤m)(hg: ∀ z∈X,ContDiffAt ℝ ((m+1:ℕ):ℕ∞ω) f z)
    (v w:List σ→ View σ)(hv:∀ i,v i∈X)(hw:∀ i,w i∈X)(hc:∀ i,‖v i-w i‖≤r) (hx : Phase l W a p (k+1) f X b) :
    Yarn k (fun L=>spread l W a p L *|glance f L (v L)-glance f L (w L)|) ≤ r*b :=by
    have hr:0 ≤ r:=(norm_nonneg _).trans (hc []);
    have hL (L:List σ):∃ z∈X,(L.length=k → |glance f L (v L)-glance f L (w L)|≤ ∑ i:σ, r*|glance f (L++[i]) z|):=by
       by_cases he:L.length=k; swap; · exact ⟨_, hv L,fun h=>(he h).elim⟩
       obtain ⟨z,hz,hP⟩:= cutAt L ht (hw L) (hv L) (fun z hk=> (hg z hk).of_le (by exact_mod_cast (show L.length+1≤m+1 by omega)))
       rw [hP]; refine ⟨z,hz,fun h=> (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum fun i _=> ?_)⟩; rw [abs_mul]; exact mul_le_mul_of_nonneg_right ((norm_le_pi_norm (v L-w L) i).trans (hc L)) (abs_nonneg _)
    choose z hZ H using hL
    have he(L:List σ)(hi:L.length=k): spread l W a p L *|glance f L (v L)-glance f L (w L)|≤ r* ∑ i:σ,value l W a p (z L) f (L++[i]):=by
       refine (mul_le_mul_of_nonneg_left (H L hi) (effect ..|>.le)).trans ?_; rw [Finset.mul_sum,Finset.mul_sum]; apply Finset.sum_le_sum; intro i _; unfold value; rw [mul_left_comm]; refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)) hr; apply w_more _ ha; apply intr; unfold zone; simp [Finset.union_assoc,Finset.subset_iff]; grind
    refine (shiny k he).trans ?_; rw [sheen k,scarves (ι:=σ)]; apply mul_le_mul_of_nonneg_left _ hr
    let Z (i:List σ):=z i.dropLast; have hw(i:σ)(L:List σ): value l W a p (z L) f (L++[i])= value l W a p (Z (L++[i])) f (L++[i]) :=by unfold Z; simp
    conv_lhs => arg 2; ext; arg 2; ext; rw [hw]
    exact (bothEnds k (fun L=> value l W a p (Z L) f L)).trans_le (hx.2 Z fun i=> hZ _)
end YM.MSbar.Bakery
