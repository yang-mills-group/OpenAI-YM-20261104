import YM.MS.Orbit.Skein
/-!
# Reading projected insertions including anchored-with-bulk cancellation. Factor half extensive and Vol reciprocal.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit.Cog
open Set Filter Function Finset Metric MeasureTheory Koszul Plane Heat
open scoped Topology ContDiff
variable {A I:Type}{p:Sector A}{S:Cog p}{K H:Grain A}{F G:Raw A ℂ}
def Head (p:Sector A)(x y:A) (F G: Raw A ℂ): Raw A ℂ:= product p ( Koszul.sign p (p y) (D x F)) (D y G)
lemma double_head (x y:A)(he:p x=p y): link (diffPair x y) false p F G= Head p x y F G +(cross (p x) (p y):ℂ) • Head p y x F G:= by rw [ link_pair x y ( by simp [he]),sign_D,map_smul,LinearMap.smul_apply ]; rfl -- order sign_D term2.Use HP
lemma head_R (i j) (w:Legs A): Head p i j F G w=scatter p w (fun l r=> cross (p j) (degree p l)* F (i::l)* G (j::r)) := scattered ..
variable [Fintype A]
lemma pair_line (h:Clear p K)(he:Sym p K) (F G: Raw A ℂ): conn p K F G= ∑ x:A,∑ y:A, (2*K x y) • Head p x y F G:= by
    have hx(x y:A): K x y • link (diffPair x y) false p F G= K x y • Head p x y F G+ K y x • Head p y x F G:= by
       by_cases hv: K x y=0; · rw [ hv,he y x, hv]; simp
       rw [ double_head _ _ (h _ _ hv), he y x, smul_add ]; rw [← mul_smul (K x y), show K x y*(cross (p x) (p y))= cross (p y) (p x)* K x y from (by rw [cross_comm]; exact mul_comm ..)]
    have hv(x y:A):2*K x y=K x y+K x y:=two_mul _; unfold conn frame; simp_rw [link_sum,link_scale, hx,hv, add_smul,Finset.sum_add_distrib]; congr 1; exact Finset.sum_comm
lemma fr_pure (h:Clear p K)(b:Bool)(hp:Pure p b F): Pure p b (frame K F):= by
   unfold frame; simp_rw [LinearMap.sum_apply,LinearMap.smul_apply,diffPair_apply]; refine Pure.sum _ fun i _=> Pure.sum _ fun j _=>?_ ; by_cases hx: K i j=0; rw [hx,zero_smul]; exact Pure.zero; apply Pure.smul; obtain he:= h i j hx; convert (hp.drop i).drop j using 1; simp [he]
lemma fr_comm (h:Pure p false F)(hp:Pure p false G): conn p K F G= conn p K G F:= link_commute (b:=false) _ h hp
omit [Fintype A] in
lemma C_Head (u v:ℂ)(x y:A)(F G:Raw A ℂ): S.wheel u v ( Head p x y F G )= product p ( sign p (p y) ( S.wheel u v ( D x F))) ( S.wheel u v ( D y G )):= by unfold Head; rw [rotate_p,roll_sign]
omit [Fintype A] in
lemma mirrorHead (X:S.Invar F)(x y:A): S.spin x • S.look ( Head p ( S.mode x ) y F G )= S.look ( Head p x y F G ):= by rw [ C_Head, C_Head,show (S.wheel (2:ℂ)⁻¹ (2:ℂ)⁻¹) (D x F)= S.spin x • (S.wheel (2:ℂ)⁻¹ (2:ℂ)⁻¹) (D (S.mode x) F) from slide S X x, map_smul,map_smul,LinearMap.smul_apply ] -- argument order X
lemma shift_join (h:Clear p K)(hp: Sym p K)(he:S.phase K)(hf:S.Invar F)(G): S.look ( conn p (imageW S K) F G )= S.look ( conn p K F G ):= by
   rw [ pair_line ( clear_i h ) ( sym_i he hp ), pair_line h hp ]; simp only [map_sum,map_smul]; rw [ ← Equiv.sum_comp S.axis (fun x=> ∑ y:A,(2*K x y) • S.look ( Head p x y F G ))]; apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _; change _= (2*K ( S.mode x ) y) • S.look ( Head p ( S.mode x ) y F G ); rw [ image_u he, ← mirrorHead hf, ← mul_assoc, mul_smul ]; funext z; simp only [Pi.smul_apply,smul_eq_mul]; linear_combination (norm:=ring_nf) 2*K (S.mode x) y*(S.look (Head p ( S.mode x ) y F G) z)*S.holo x -- order region to adjust S.look...
-- quotient operator package. cost half normalization unmarked. Relations
variable (S:Cog p) (b:Bool) (K)
abbrev readerV (S:Cog p)(b:Bool): Op A ℂ:= if b then S.look else LinearMap.id
abbrev pay (b:Bool): ℂ:= if b then (2:ℂ)⁻¹ else 1
variable {K:Grain A}
lemma read_pc (h:S.phase K)(F:Raw A ℂ): frame (imageV S b K) (readerV S b F)= readerV S b ( frame (imageV S b K) F ):= by
   cases b; · rfl
   exact direct_read (Cc S K) (Rc h) F
lemma read_tree (hp:S.phase K) (F H:Raw A ℂ) : conn p (imageV S b K) (readerV S b F) (readerV S b H)= readerV S b ( conn p (imageV S b K) F H ):= by
   cases b; · rfl
   exact direct_link (Cc S K) (Rc hp)
lemma read_plain (X:S.Invar F)(he:S.phase K)(h:Clear p K)(hv: Sym p K) : readerV S b ( conn p (imageV S b K) (pay b • F) G )= readerV S b ( conn p K F G ):= by
   cases b; · rw [show pay false=1 from rfl, one_smul]; rfl
   change S.look ( link _ _ _ (pay true • F) G)=S.look (conn _ _ _ _); rw [ pay,if_pos rfl, link_smul_left ]; change S.look (( (2:ℂ)⁻¹) • (conn p ( S.Cascade _ ) F G))=_; rw [show conn p _ _ _= conn p K F G + conn p ( imageW S K ) F G from ?tx]; swap; · unfold conn Cascade; rw [frame_add, Koszul.link_plus ]; -- hp convert.S
   rw [map_smul,map_add,shift_join h hv he X G,← two_smul ℂ,smul_smul, inv_mul_cancel₀ (by norm_num : (2:ℂ)≠0),one_smul ]
end YM.MS.Orbit.Cog
