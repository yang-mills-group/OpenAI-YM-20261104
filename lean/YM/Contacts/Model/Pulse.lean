import YM.Contacts.Model.Egress
/-! Assess annulus templates of positive charged model coefficients at links. No confidences kept. -/
noncomputable section
namespace YM.Contacts.Model
open Function Lattice Finset Filter Set PhysicalNext.Repeat Pressure Wilson MeasureTheory RG
open Slide (Stars)
open Trio (froth Mirrors Offer)
open AnalyticBridge VerifiedReset Push.AbsoluteSums Animals YM.Stationary Milling PertExtension.Series Exterior Precision Ion
open Pulse Spine Garf Steam Bloch Radial House
open scoped Topology NNReal InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n m c:Side}{k w r z:ℕ} (w)
def tap (v:Node (Loc G 1))(U:Links ℤ G.El):ℝ:= G.plog (G.mat (U (v.1,axisEquiv.symm v.2.1))) v.2.2
def cutF (F : Field (Fin (r+1)) (Node (Loc G 1))) : Story G:= fun U=> ∑ i∈ season w, F (stencil w i)*∏ j,tap (stencil w i j) U
lemma cutF_loc (q:Field (Fin (r+1)) (Node (Loc G 1))) : LocalOn (Lattice.box (w+1)) (cutF w q):= by
   intro x y he; refine sum_congr rfl fun i hi=> congr_arg _ (prod_congr rfl fun j _=>?_); unfold tap; let p:=stencil w i j; let v:Cover:=p.1; let a:=axisEquiv.symm p.2.1; have hx : v∈Lattice.box w:=(i j).1.2
   apply congr_arg (fun U:G.El=> G.plog (G.mat U) p.2.2); apply he (v,a) ?_ ?_ <;> apply box_test.mpr <;> constructor <;> intro k <;> have hw:= (box_test.mp hx).1 k <;> have hy:=(box_test.mp hx).2 k <;> simp only [Pi.add_apply,step_apply,Nat.cast_add,Nat.cast_one] <;> omega
variable (q: Field (Fin (r+1)) (Node (Loc G 1))) (h:∀ i, Mirrored (backpack i) q)
lemma element (i:Site c) : pass (cutF w q) c i ∘ input G c=ᶠ[𝓝 0] fun x=> occupied w q x i := by
   filter_upwards [input_encodes (m:=c) (G:=G)] with x hx
   have h (a:Node (Loc G 1)): tap a (expandAt i (input G c x))= x (road a i):= by
      obtain ⟨v,y,t⟩:= a; obtain ⟨y,rfl⟩:= axisEquiv.surjective y; let u:= wrap c v+i; let V:=input G c x; change G.plog (G.mat (V (u,axisEquiv.symm (axisEquiv y)))) t=x (u,coord y,t); rw [axisEquiv.symm_apply_apply,←content_at]; change content _ _= _; exact congr_fun hx (u,coord y,t)
   change cutF w q _= _; apply sum_congr rfl fun u _=> congr_arg _ (prod_congr rfl fun i _=> h _)
lemma cut_adopts (i:Site c): altitude (pass (cutF w q) c i):= AnalyticAt.congr (f:=fun x=>occupied w q x i) (show AnalyticAt _ _ _ from (by unfold occupied; apply ContDiffAt.analyticAt; fun_prop)) ((element ..).symm)
include h
lemma resonates : plays (pass (cutF w q) c)=ᶠ[𝓝 0] design (printShadow (blockR w q) c):= by
   filter_upwards [eventually_all.mpr (element w q (c:=c))] with x hx; exact (sum_congr rfl (fun i _=>hx i)).trans (evaluates w h x).symm

section budgets
-- per-tile vs all. no exp collapse. Goal tilt allow difference from roots costs times polynomial volume.
variable {b:ℝ}{s:ℝ≥0}(hg:Rooted (terrain s _) q b)
omit h in
lemma tail_price {α:Type}[Fintype α](P:Range α){f:Field (Fin (r+1)) α}(v:Dir α)(h:Rooted P f b): ‖design f v‖ ≤ (Fintype.card α:ℝ)*b*‖v‖^(r+1):= by
    letI : DecidableEq (Fin (r+1)):= fun _ _=> Classical.propDecidable _; let i:Fin (r+1):=0; rw [design_spec]; refine (norm_sum_le ..).trans ?_
    let f' x:= ‖f x*∏ i,v (x i)‖; change (∑ x,f' x) ≤ (Fintype.card α:ℝ)*b*‖v‖^(r+1); erw [←Finset.sum_fiberwise univ (fun x:Fin (r+1)→α=>x i) f']; refine le_trans (b:=∑ k:α,b*‖v‖^(r+1)) (sum_le_sum (fun y _=> ?_)) ?_; swap; · rw [Finset.sum_const,nsmul_eq_mul,card_univ,mul_assoc]
    let g:Finset (Locked α i y):=univ; have he : ∑ x ∈ univ.filter (fun x=>(fun (t:Fin (r+1)→α)=> t i) x=y), f' x = ∑ u:Locked α i y, f' u.val:= by
       symm; exact Finset.sum_bij (fun u _=> u.val) (fun u _=> mem_filter.mpr ⟨mem_univ _,u.property⟩) (fun _ _ _ _ he=>Subtype.ext he) (fun v hv=>⟨⟨_,(mem_filter.mp hv).2⟩,mem_univ _,rfl⟩) (fun _ _=>rfl)
    rw [show (∑ x ∈ _, _)= _ from he]; have hb := budget_sum (h.raw i y) g
    calc _ ≤ ∑ u:Locked α i y,‖f u.val‖*‖v‖^(r+1):= by
           apply sum_le_sum; intro u hu; rw [show f' u.val= _ from norm_mul _ _, norm_prod]; -- specify
           apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); convert prod_le_prod (s:=univ) (f:=fun j=> ‖v (u.val j)‖) (fun i _=> norm_nonneg _) (fun i _=>norm_le_pi_norm v (u.val i)) using 1; simp
         _ ≤ _:= by rw [←sum_mul]; exact mul_le_mul_of_nonneg_right hb (pow_nonneg (norm_nonneg v) _)
omit h in
lemma shape_invoice (s : Signed)(x:Link G m): ‖orderTurn s x‖ ≤ ‖x‖:= by exact le_trans ((orderTurn s).le_opNorm x) (mul_le_of_le_one_left (norm_nonneg x) (nor_turn _))
omit h in
lemma design_power {α:Type}[Fintype α](q:Field (Fin k) α)(x:Dir α)(s:ℝ): design q (s • x)=s^k*design q x:= by rw [design_spec,design_spec]; simp only [Pi.smul_apply,smul_eq_mul, Finset.prod_mul_distrib,Finset.prod_const, Finset.card_univ,Fintype.card_fin]; rw [mul_sum]; exact sum_congr rfl fun i _=> mul_left_comm ..
omit h
include h hg
lemma sensing (x:Link G m)(hi:∀ s:Signed, design (printShadow q m) (orderTurn s x)= design (printShadow q m) x)(j:ℕ) : ‖jet (plays (pass (hue (cutF w q)) m)) j x - jet (design (printShadow q m)) j x‖ ≤ if j=r+1 then (Fintype.card (Lines G m 1):ℝ)*(Real.exp (-(s:ℝ)*w)*b)*‖x‖^j else 0 := by
  set F := printShadow q m; let t:= blockR w q; let P:= printShadow t m; let V:= design F
  have hm i (x:Link G m): jet (plays (pass (cutF w q) m)) i x= jet (design P) i x:= by unfold jet; rw [((resonates w q h (c:=m)).iteratedFDeriv ℝ _).eq_of_nhds]
  rw [breeze (cut_adopts w q)]; simp_rw [hm, radiant (design_ana P 0) _ _ (design_power P), radiant (design_ana F 0) _ _ (design_power F)] -- orientation of pow
  split; next hh=>
    subst j; rw [show VerifiedReset.factor * _- design F x= VerifiedReset.factor * (∑ i:Signed,(design P (orderTurn i x)- design F (orderTurn i x))) from ?_]; swap; · simp_rw [hi]; rw [sum_sub_distrib,sum_const,nsmul_eq_mul,card_univ,mul_sub,← mul_assoc,VerifiedReset.factor_card,one_mul]
    rw [norm_mul,Real.norm_of_nonneg VerifiedReset.factor_pos.le]; refine (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (g:=fun _=>(Fintype.card (Lines G m 1):ℝ)*(Real.exp (-↑s*w)*b)*‖x‖^(r+1)) (fun i _=>?_))) VerifiedReset.factor_pos.le).trans_eq ?_
    · rw [norm_sub_rev,←Convoy.parcel_sub]; apply (tail_price (Range.cheap _) _ (drops w hg h)).trans; refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (shape_invoice i x) _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Real.exp_pos _).le hg.cash))
    rw [sum_const,nsmul_eq_mul,card_univ,←mul_assoc, VerifiedReset.factor_card,one_mul]
  next h=> simp
end budgets
end YM.Contacts.Model
