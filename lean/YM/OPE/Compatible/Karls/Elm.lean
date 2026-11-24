import YM.OPE.Compatible.Karls.Vox
/-! # homogeneous crowns, going backwards. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function ContinuousLinearMap
open scoped Topology BigOperators Classical
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{m k i:ℕ}{q:ℝ}(p:E→L[ℝ] E)
local notation "X!"=> E→L[ℝ] E
open Filter Finset
open Quit.PriceZ
local notation "A!"=> Dice E
variable {G:Type}[NormedAddCommGroup G][NormedSpace ℝ G]
-- `thick` Pal stationary.H
variable (G:ℕ→ℕ→ Dice E) (L:ℕ→ E→L[ℝ] E)(Y:ℕ→Dice E) (T:E→L[ℝ] E) {b v u w:ℝ} {a d:ℕ}
omit [NormedSpace ℝ E] in lemma nzp :‖(0:E)‖=0:=norm_zero
lemma fareEnd (f:ℕ→Dice E)(F: Dice E){r q a:ℝ}(hr:0 < r)(ht: r<1)(hx:0 < q)(ha:0 ≤ a)(hq:a<q)(hh:∃ c, Hex r (fun i=> f i-F) c)(x y z t:ℕ→E)(h:∃ c,Hex a (x-z) c)(hv:∃ c,Hex a (y-t) c)(hX:∀ k:ℝ,q<k→∃ c,Hex k z c)(hY:∀ k:ℝ,q<k→∃ c, Hex k t c): Thick (q*q) (fun i=> f i (x i) (y i)-F (z i) (t i)):=by
     let A(i j:ℕ)(g:ℕ→Dice E):Dice E:= if j=0 then g i else 0; let B(j:ℕ):Dice E:= if j=0 then F else 0; let D:= q*q/2; have hD:0<D:=by unfold D;positivity
     obtain ⟨c,H⟩:= hh; let v:=c+‖F‖; have hv':0 ≤ v:=add_nonneg H.price (norm_nonneg F); have he:∀ i j:ℕ,‖A i j f‖≤v*D^j:=by
          intro i j; cases j; · rw [show A i 0 f=f i from if_pos rfl,pow_zero,mul_one]; apply le_trans _ (le_of_eq rfl); nth_rw 1 [show f i=f i-F+F from (sub_add_cancel (f i) F).symm]; exact (norm_add_le (f i-F) F|>.trans (add_le_add_left (le_trans (H i) (mul_le_of_le_one_right H.price (pow_le_one₀ hr.le ht.le))) _))
          rw [show A i (_+1) f=0 from if_neg (Nat.succ_ne_zero _), show ‖(0:Dice E)‖=0 from nzp (E:=Dice E)]; positivity
     have hw:∀ i j:ℕ,‖A i j f-B j‖ ≤ c*D^j*r^i :=by
          intro i j; cases j; · apply le_trans (H i); rw [pow_zero,mul_one]
          have hz':0 ≤ c:=H.price; rw [show A i (_+1) f-B (_+1)=0 from (by simp only [A,B,Nat.add_one_ne_zero, if_false]; exact sub_self (0:Dice E)),show ‖(0:Dice E)‖=0 from nzp (E:=Dice E)] -- replace lemma
          positivity
     have he': D<q*q:=by unfold D; nlinarith
     obtain ⟨⟨w,hw',w',z',hp⟩⟩:=fareStep (fun i j=>A i j f) B hx he' hD hr.le ht ha hq ⟨v,he⟩ ⟨c,hw⟩ h hv hX hY
     apply Thick.hex _ hw' w'; refine ⟨z'*w,fun i=> ?_⟩; apply le_trans (le_of_eq ?_) (hp.forward i); apply congr_arg; simp only [Nat.add_sub_cancel]; rw [sum_range_succ]; simp only [tsub_self,A,B, if_pos]; rw [sum_eq_zero _,zero_add]; intro j hj; have ht:i-j ≠ 0:=(by have h: j < i:= mem_range.mp hj; omega); rw [if_neg ht, if_neg ht]; change (0:ℝ)-0= _; ring
namespace Punch
variable (Q:Punch G L Y T u b w)(hq:0<q)
abbrev Tone:=(KernP T q d)
noncomputable def Folio (m:ℕ): Dice (KernP T q m):= pullD (KernP T q m).subtypeL (Y 0) + rear (KernP T q m).subtypeL (Fleet T q m hq) (coreE Y T) 0
-- corner.Final pledge normalized asym for same layer
include Q
lemma Shelter (hh:w < q*q){a:ℝ}(he:0 ≤ a)(hv:a<q)(x y:ℕ→ E)(hX:∀ i,x (i+1)=L i (x i))(hY:∀ i,y (i+1)=L i (y i))(p t:KernP T q m)
   (hx:∃ c,Hex a (x-tale T p.val) c)(hy:∃ c, Hex a (y-tale T t.val) c):
    Thick (q*q) (fun i=> G 0 i (x 0) (y 0)-Folio Y T hq m ((portC T q m^i) p) ((portC T q m^i) t)):=by
     let X:=Fleet T q m hq; let A:=portC T q m; let B:=coreE Y T; let g(i:ℕ):= (A^i) p -- parentheses
     let j(i:ℕ):=(A^i) t; let ι:=(KernP T q m).subtypeL; let e:= ErrS G L; let z:=tale T p.val; let t':= tale T t.val
     obtain ⟨c,hc,H⟩:= Q.fees; have h(a':ℝ)(hp:q<a')(p:KernP T q m):∃ c,Hex a' (tale T p.val) c:=by obtain ⟨b,hb,H⟩:= AltE T q m hq.le hp; exact ⟨_,H _ p.property⟩
     obtain ⟨σ,b₁,hσ,hs,hz,hb₁,c₁,hc₁,H₁⟩:= Q.sugar G L Y T (q*q) hh
     let v:= max w b₁; have hV:v<q*q:=max_lt hh hb₁; have he' : 0 < v:= lt_of_lt_of_le Q.west (le_max_left ..); obtain ⟨x',hq'⟩:= Q.bill; have hh':0 ≤ x':=by have ht: 0 ≤ x'*w^0:= (norm_nonneg (e 0 0)).trans (hq' 0 0); simpa using ht
     let S(i:ℕ):= ∑ j∈range i, (e j (i-1-j) (x j) (y j) - B (i-1-j) (z j) (t' j))
     have ha:Thick (q*q) S:=fareStep e B hq hV he' hσ.le hs he hv ⟨x',fun i j=>(hq' i j).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Q.west.le (le_max_left ..) _) hh')⟩ ⟨c₁,fun i j=>(H₁ i j).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz.le (le_max_right ..) _) hc₁) (pow_nonneg hσ.le _)) ⟩ hx hy (fun i a=>h i a p) (fun i a=>h i a t)
     obtain ⟨r,hr,hr'⟩:= surge_h q⁻¹ (fun i:ℝ=> w*i*i) (by fun_prop) (show w*q⁻¹*q⁻¹<1 from (by rw [mul_assoc,← mul_inv,← div_eq_mul_inv,div_lt_one (mul_pos hq hq)]; exact hh)); have hE: X*A=1∧ A*X=1 ∧ Ux X q⁻¹ ^ m=0:= wineP T hq; obtain ⟨c',hc',B'⟩:=rearF ι X B (Q.edgeV G L Y T) (RiseP X hE.2.2 (inv_nonneg.mpr hq.le) hr) ((inv_pos.mpr hq).trans hr).le Q.west.le hr'
     let U:=fun i=> rear ι X B i (g 0) (j 0); have hLife : Thick (q*q) U:=Thick.hex ⟨c'*‖g 0‖*‖j 0‖,fun i=>(InvokeB ..|>.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hc' i) (norm_nonneg _)) (norm_nonneg _)).trans_eq (by ring)))⟩ Q.west.le hh -- hx shadows
     let K:= fun i=> G i 0 (x i) (y i)-Y 0 (z i) (t' i); have hM: Thick (q*q) K:= fareEnd _ (Y 0) Q.pu Q.hu hq he hv ⟨c,fun i=>(H i 0).trans_eq (by rw [pow_zero,mul_one])⟩ _ _ z t' hx hy (fun r h'=>h r h' p) (fun r h'=>h r h' t)
     rw [show (fun i=> _ - Folio Y T hq m _ _)= K+S-U from ?_]; swap
     · funext i; have ht: G 0 i (x 0) (y 0)= _:= FarS G (ErrS G L) L (fun _ _=>rfl) x y hX hY 0 i; have hz:= behind ι A X B hE.1 B' g j (fun i=>by unfold g; rw [pow_succ',byway]) (fun i=>by unfold j; rw [pow_succ',byway]) 0 i; simp only [Nat.zero_add] at ht hz; have hg(i):ι (g i)= z i:=portables T p i; have hv(i):ι (j i)= t' i:=portables T t i; simp_rw [hg,hv] at hz; change G _ _ _ _ - (Y 0 (ι (g i)) (ι (j i))+ rear ι X B 0 _ _) = _; rw [show ((K+S-U) i)= (K i+ S i-U i) from rfl, show ι (g i)= _ from hg i,show ι (j i)=_ from hv i]; change G _ _ _ _-(Y 0 (z i) (t' i)+rear ι X B 0 (g i) (j i))= (K i+ S i-U i); unfold K S U e; rw [hz,ht,sum_sub_distrib]; ring
     exact (Thick.add hM ha).sub hLife
end Punch
end YM.OPE.Hark
