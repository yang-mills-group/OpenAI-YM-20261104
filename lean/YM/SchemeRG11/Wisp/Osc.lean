import YM.SchemeRG11.Wisp.Hushed
/-! Color charge commutes with cover subtraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.North
open Function Lattice Pert Maxwell Flock Bare Tree Bark Haze Pile Atoll Crest Labels MvPolynomial RawLabels Outlook
open scoped Classical
variable {G:Gauge}
def tide (u:G.El)(a:Shaft G):Touch G:= ∑ i:G.ColorIndex,Finsupp.single (a.1,i) (G.adjoint u (unitColor G i) a.2)
lemma tide_p(u:G.El)(x:Shaft G)(A:trunk G ℤ): sense (cant A) (tide u x)=cant (recolor u A) x:=by
 unfold tide; rw [map_sum]; unfold recolor cant comp
 conv_rhs=> rw [←Triangle.sum_color (A x.1)]
 rw [map_sum]; simp only [sense,Finsupp.linearCombination_single,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,map_smul,smul_eq_mul]; apply Finset.sum_congr rfl; intro i _; ring
lemma tides (u:G.El): (land G).pull (tide u)= land G:=by
 apply Dose.strict; intro i j
 change (land G).bed _ _=_; unfold Dose.bed; rw [sense,tide,tide
 ]; simp only [_root_.map_sum, Haze.Dose.windfall,Finsupp.linearCombination_single, Finset.sum_apply,Pi.smul_apply, smul_eq_mul, Atoll.land]
 by_cases h:i.1.2=j.1.2
 · have he(U:G.El)(x y:G.Color):inner ℝ (G.adjoint U x) (G.adjoint U y)=inner ℝ x y:=by simp only [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,←map_add,G.norm_adjoint]
   have H (a b:G.ColorIndex): G.adjoint u (unitColor G a) b = G.adjoint u⁻¹ (unitColor G b) a:=by rw [←Align.to_color,← Align.to_color,real_inner_comm,← he u (G.adjoint u⁻¹ _) (unitColor _ _),←G.adjoint_mul];simp
   simp only [h,eq_self,and_true,mul_ite,mul_zero, Finset.sum_ite_eq',Finset.mem_univ, if_true,H,←mul_assoc,← Finset.sum_mul]
   rw [←color_inner,he, Align.to_color,unitPaint]; split<;>simp_all
 simp only [h,and_false,if_false,mul_zero,Finset.sum_const_zero]
lemma tints_eval (u:G.El)(p:vellum G)(A:trunk G ℤ): aeval (cant A) (vary (tide u) p)=aeval (cant (recolor u A)) p:=by rw [varyV]; simp_rw [tide_p]
lemma broiled (u:G.El)(p:vellum G): (land G).heat (vary (tide u) p)= vary (tide u) ((land G).heat p):=by rw [(land G).light,tides]
lemma harvest (u:G.El)(p:vellum G): (land G).neg.heat (vary (tide u) p)= vary (tide u) ((land G).neg.heat p):=by rw [(land G).night,tides]
lemma blast (u:G.El)(p:pLabel G)(h:Neutral p): vary (tide u) (stemZero 1 p)=stemZero 1 p:=by apply viewers; intro A; rw [tints_eval,work,work,soul_color]; exact h _ _
lemma colored_v (u:G.El)(p:pLabel G)(h:Neutral p): vary (tide u) (castZero 1 p) = castZero 1 p:=by rw [castFree,←harvest, blast _ _ h]
-- need neutral for NEG.HEAT p itself, cannot infer from eval on incomplete wave. prove covariance invari on key alternatives via pull star.
def chip (u:G.El)(p:Key G): Stem (Key G) ℝ:= ∑ i,Finsupp.single ⟨p.1,i⟩ ((axes G p.1).coord p.2 (Taylor.paint u ((axes G p.1) i)))
lemma chipped (u:G.El)(p:Key G)(A:Labels.Jet G): sense (rune A) (chip u p)=rune (colored u A) p:=by
 unfold chip; rw [map_sum]; simp only [sense,Finsupp.linearCombination_single,smul_eq_mul]; conv_rhs=> unfold rune colored; rw [← (axes G p.1).sum_repr (A p.1)]
 rw [map_sum,map_sum]; apply Finset.sum_congr rfl; intro i _; rw [_root_.map_smul,map_smul]; exact mul_comm ..
lemma nub (u:G.El)(p:pLabel G)(A:Labels.Jet G): nib A (vary (chip u) p)= nib (colored u A) p:=by unfold nib; rw [varyV]; simp_rw [chipped]
lemma run_inj(p q:pLabel G)(hx:∀ A, nib A p=nib A q):p=q:=by apply solder; apply Labels.eval_ext; intro A; rw [←cabin,←cabin,hx]
lemma clip (u:G.El){p:pLabel G}(h:Neutral p): vary (chip u) p=p:=by apply run_inj; intro A; rw [nub]; exact h _ _
lemma ruby(u:G.El)(p:pLabel G): vary (tide u) (stemZero 1 p)=stemZero 1 (vary (chip u) p):=by apply viewers; intro A; rw [tints_eval,work,work,soul_color]; exact (nub ..).symm
lemma tropic (k i:Key G) (u:G.El):
 (Atoll.unmarked G 1).pulse k i = ((Atoll.unmarked G 1).pull (chip u)).pulse k i:=by
 let D:=land G; let L:= Atoll.unmarked G 1
 have he :D.avg (vary (tide u) (stemZero 1 (X k*X i)))=D.avg (stemZero 1 (X k*X i)):=by rw [Dose.colour,tides]
 have hh (g:Dose (Key G) ℝ): g.avg (X k*X i)=g.pulse k i:=by rw [Dose.release,vent,mkDerivation_X,Haze.Dose.avg_def,Haze.Dose.heat_C,aeval_C,g.beats k i]; rfl
 rw [ruby] at he; change D.avg (vary _ _)=D.avg (vary _ _) at he; simp only [Dose.colour] at he
 exact Eq.trans (hh L).symm (he.symm.trans (hh _))
lemma mirth (p:pLabel G)(h:Neutral p):Neutral ((Atoll.unmarked G 1).neg.heat p):=by
 intro A u; rw [← nub]; let L:=Atoll.unmarked G 1; have he:L=(L.pull (chip u)):= Dose.strict _ _ (fun i j=>tropic i j u) -- check
 change nib A (vary _ (L.neg.heat _))=_
 have hx:=Dose.night L (chip u) p; rw [←he,clip u h] at hx; rw [← hx]
-- tangent line jet
lemma resonate (p:pLabel G)(A:trunk G ℤ): HasDerivAt (fun t:ℝ=> nib (soul A+t • (fun i=> (1/2:ℝ) • starJet true 1 (0:Cover) i A A)) p) (aeval (cant A) (expandW 1 p)) 0:=by
 induction p using MvPolynomial.induction_on with
 | C c=> simp only [nib,aeval_C,expand_C,map_zero]; apply hasDerivAt_const
 | add a b ha hb=> simp_rw [map_add,expand_add,map_add]; exact ha.add hb
 | mul_X a k h=>
    let v:=k.2; let b(t:ℝ):=soul A+t • (fun i=> (1/2:ℝ) • starJet true 1 (0:Cover) i A A)
    have hh:HasDerivAt (fun t:ℝ=>nib (b t) (X k)) (aeval (cant A) (expandW 1 (X k))) 0:=by
       let z:= (1/2:ℝ) * (axes G k.1).coord k.2 (starJet true 1 (0:Cover) k.1 A A)
       unfold nib; rw [expand_x,bud,one_zpow, one_smul,omega_at]; simp_rw [aeval_X]; change HasDerivAt (fun t=>rune (b t) k) z 0; unfold b rune; simp only [Pi.add_apply,Pi.smul_apply,map_add,map_smul,smul_eq_mul]; convert! ((hasDerivAt_id' (0:ℝ)).mul_const z).const_add ((axes G k.1).coord k.2 (soul A k.1)) using 1; simp [z] -- check
    unfold nib; simp_rw [_root_.map_mul]
    rw [expand_mul,map_add, _root_.map_mul,map_mul, work,work]; convert! h.mul hh using 1
    simp only [nib,b,zero_smul,add_zero]; exact add_comm .. 
lemma brace_c (u:G.El)(p:pLabel G)(h:Neutral p): vary (tide u) (expandW 1 p)= expandW 1 p:=by
 apply viewers; intro A; rw [tints_eval]; have hx:= resonate p (recolor u A)
 have he(t:ℝ): soul (recolor u A)+ t • (fun i=> (1/2:ℝ) • starJet true 1 (0:Cover) i (recolor u A) (recolor u A))= colored u (soul A+ t • (fun i=> (1/2:ℝ) • starJet true 1 (0:Cover) i A A)):=by funext i; rw [soul_color]; simp [colored,plodding]
 simp_rw [he,h] at hx; exact hx.unique (resonate p A)
lemma foliate (u:G.El)(p:pLabel G)(h:Neutral p): vary (tide u) (castFirst 1 p)= castFirst 1 p:=brace_c _ _ (mirth p h)
end YM.SchemeRG11.North
