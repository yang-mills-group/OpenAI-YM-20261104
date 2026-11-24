import YM.OPE.Compatible.Assemblage.Fuse
/-!
# Travelling with the singles. Seam covariance of Blade as well as initial canonical sight; retain the budget at intermediate positions where some OTHER marker begins to mix.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Stem
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V I J W : Type}[Fintype V][DecidableEq V]{G:Gauge}{n n':Side} (m m':Motion) (x x':Site n) (f:Config G n→ℂ)(g:Res G n)
lemma moves : stepUp m x (stepUp m' x' f)=stepUp (twist m m') (affine m.1 x x') f:=by
    funext i; unfold stepUp; rw [pull_pull,oper]; rfl
lemma float_moves : floatUp m x (floatUp m' x' g)=floatUp (twist m m') (affine m.1 x x') g:=by
    have he(p:Support n): sky m x (sky m' x' p)=sky (twist m m') (affine m.1 x x') p:=by
       simp_rw [shading,image_image]; refine image_congr (fun i _=>?_); change affine m.1 x (affine m'.1 x' i)=affine (m.1*m'.1) _ i; simp only [affine,Signed.act_add,Signed.act_mul,add_assoc]; rfl
    let a:= puff m x; let b:= puff m' x'; let c:=puff (twist m m') (affine m.1 x x')
    have hb p:a (b p)=c p:=Prod.ext (he _) (he _)
    funext p; obtain ⟨i,rfl⟩:= c.surjective p; unfold floatUp; change stepUp _ _ (stepUp _ _ (g (b.symm (a.symm (c i))))) = stepUp _ _ (g (c.symm (c i))); rw [Equiv.symm_apply_apply, ← hb, a.symm_apply_apply,b.symm_apply_apply,moves]
lemma turn_unit (m:Motion) : twist m (1,false)=m:=by cases m with
   | mk v b=>cases b <;>simp [twist]
lemma flyF : stepUp m x (stepUp (1,false) x' f)= stepUp m (affine m.1 x x') f:=by rw [moves,turn_unit]
lemma flyK : floatUp m x (floatUp (1,false) x' g)= floatUp m (affine m.1 x x') g:=by rw [float_moves,turn_unit]
lemma reverse_F : stepUp (1,false) x (stepUp (1,false) (-x) f)=f:=by rw [flyF]; simp only [affine,Signed.act_one,neg_add_cancel]; exact Ribbons.stepid f
lemma reverse_K : floatUp (1,false) x (floatUp (1,false) (-x) g)=g:=by rw [flyK];simp only [affine,Signed.act_one,neg_add_cancel]; exact Ribbons.floatid g
lemma scale_F (z:ℂ): stepUp m x (z • f)= scalar m z • stepUp m x f:=funext fun _=> Motion.scalar_mul ..
lemma scale_K (z:ℂ): floatUp m x (z • g)= scalar m z • floatUp m x g:=funext fun _=> funext fun _=>Motion.scalar_mul ..

variable {R:Rep G n}{R':Rep G n'} -- rm
lemma bearer {R:Rep G n} {a:Site n}{p:ℂ} {c:ℝ} (π:R.activities.Moves m.1 x)(h:Blade R a f g p c): Blade R (affine m.1 x a) (stepUp m x f) (floatUp m x g) (scalar m p) c:=by
    obtain ⟨i,k,M,s,h⟩:=h; refine ⟨_, k, Leaf.route π ∘ M,fun i=>scalar m (s i),fun i=> ?_, ?_,?_,?_⟩
    · rw [comp_apply,crestSky]; rw [shading]; exact mem_image_of_mem (turnSites m.1 x) (h.sit i)
    · funext U; rw [h.lit]; simp_rw [comp_apply,stepUp,Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul, Motion.scalar_add, pipes,Motion.scalar_mul, climb_p]; rfl
    · funext j U; rw [h.run]; obtain ⟨i,rfl⟩:= (puff m x).surjective j
      unfold floatUp stepUp; simp_rw [Equiv.symm_apply_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul, pipes,Motion.scalar_mul,comp_apply, climb_entry,floatUp,Equiv.symm_apply_apply]; rfl
    simp only [Motion.norm_scalar,comp_apply,fareSky]; exact h.pay
lemma chronicle {R:Rep G n} {K:Rep G n'} {D:GaugeDoor R K}{b:Set Wing} (hp:b.Finite)
    {o:Site n}{x:Site n'}{z:ℂ}{Q:Res G n'}{a u:ℝ}{S:StepData n' n}(h:Tale b o x 1 f g Q z a u D) (he:Tunes D)(hc:SoundDoor S D):Blade R o f g z (2*a):=by
    obtain ⟨I,h,M,s,ψ,h⟩:=h; obtain ⟨J,i',N,hN,ht,hF,hK,-⟩:= narrow1 (Bud Unit) () h hp hc he (w:=fun _=>1) (fun _=>zero_lt_one)
    let x i:=(N i).M; let y i := (N i).charge; refine ⟨J,i',x,y,fun i=> (hN i).2, ?_,?_,?_⟩
    · let F:= Bud Unit; funext U; have he := congr_arg (fun p:Poly (Bud Unit)=>p.part ((Bud Unit).fire ())) (hF U)
      change f U=z+(∑ i,y i • prose (x i)) U; rw [Finset.sum_apply]; simp only [Poly.part_sum,odour,fun i=>(hN i).1,Poly.part_send,if_true] at he
      rw [add_comm, ← sub_eq_iff_eq_add, ← he]; exact Finset.sum_congr rfl fun i _=>mul_comm _ _
    · funext p U; have he := congr_arg (fun p:Poly (Bud Unit)=>p.part ((Bud Unit).fire ())) (hK p U)
      simp only [Poly.part_sum,fragrance,fun i=>(hN i).1, Poly.part_send, if_true] at he
      rw [Finset.sum_apply,Finset.sum_apply, ← he]; exact Finset.sum_congr rfl fun j _=> mul_comm _ _
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _=> ?_)) (show (∑ i,R.p.mass (x i).crest (Menu.fare (N i) (fun _=>1)))≤2*a from by simpa only [x,mul_one] using ht)
    change ‖(N i).charge‖*MergeProof.load (N i).M=_; unfold MergeProof.load BudgetPoint.mass Menu.fare sumFee; rw [(hN i).1,Poly.solo_toll]; unfold x; ring
end YM.MergeProof.Ribbons.ManyCopies.Stem
