import YM.OPE.Compatible.Estuary.Ross
/-! # Tape transfer actual kernels in virgo -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Votive Tree
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n c f:Side}
namespace Script
open Page Virgin Planned.PrimaryIntegral295.Carrier
lemma expH (p:climate G) (T:climate G→L[ℝ] G.Color): HasDerivAt (fun x:ℝ=> G.mat (G.lieExp (T (x • p)))) (G.colorMat (T p)) 0:= by
    simp_rw [map_smul]; exact Stationary.exp_ray _
lemma plogCharge (p:climate G)(i:Axis)(j:G.ColorIndex): fderiv ℝ (vigil G (.inl (i,j))) 0 p= psc G i p j+ups G (step i) p j-ups G 0 p j :=by
   let u:= psc G i; let v:= ups G (step i); let w := ups G 0; let h(t:ℝ):= hut G (t • p) i; have ht:h 0=1:=by unfold h; rw [zero_smul,hut_zero];rfl
   have hh : HasDerivAt (fun t:ℝ=>G.mat (h t)) (G.colorMat (u p+v p - w p)*G.mat (h 0)) 0:=by
      let k: G.Mat:=G.colorMat (u p+v p-w p); rw [ht]; simp_rw [h,hut,G.mat_mul,G.mat_inv]; convert! ((expH p (-w)).mul (expH p u)).mul (expH p (-v)).star using 1
      simp only [Pi.mul_apply,map_zero, G.mat_one,zero_smul,G.mat_lieExp_zero,mul_one,one_mul,map_sub,map_add,star_one, _root_.neg_apply,map_neg,star_neg,G.colorMat_skew,neg_neg,neg_zero]; abel
   have ha:=Push.Loops.delta_rate hh; rw [ht] at ha; have hf : HasDerivAt (fun t:ℝ => G.plog (G.mat (h t))) (u p+v p-w p) 0:=by simpa only [Push.Loops.delta,inv_one,mul_one] using! ha
   have hy:= (EuclideanSpace.proj j).hasFDerivAt.comp_hasDerivAt _ hf; exact (Push.side (vigil G (.inl (i,j))) ((vigilA G (.inl (i,j))).2.differentiableAt (by simp)) p).unique hy
lemma fogStem (p:deck (Blend G) n)(v: Tab (Shade G) n): lac G n (fderiv ℝ (fog G n) 0 p) v=p (starI v)+p (starJ (I:=Shade G) (v.1+ step v.2.1,v.2.2))-p (starJ (v.1,v.2.2)):=by
   let i:=starI (J:=G.ColorIndex) v; let F:= fog G n; let L: deck (Blend G) n→L[ℝ] ℝ:= ContinuousLinearMap.proj i; let Y:=lookS (stave G) v.1; let X:=vigil G (.inl v.2); have ht:= (vigilA G (.inl v.2)).2; have hx: fderiv ℝ (X∘Y) 0 p=fderiv ℝ X 0 (Y p):=by rw [fderiv_comp 0 (Y.map_zero.symm ▸ ht.differentiableAt (by simp)) Y.differentiableAt,Y.fderiv,map_zero]; rfl
   have hh: fderiv ℝ (L∘ F) 0 p=L (fderiv ℝ F 0 p):=by rw [fderiv_comp 0 L.differentiableAt ((fogDial G n).2.differentiableAt (by simp)),L.fderiv]; rfl
   change L (fderiv ℝ F 0 p)= _; rw [←hh,show L ∘ F=X ∘ Y from rfl,hx,plogCharge]; change p (v.1+wrap n 0,i.2)+ notchS G _ _-notchS G _ _ = _; unfold notchS; rw [map_zero,add_zero,dif_pos,dif_pos]; rotate_left; · simp [stave]
   · simp [stave]
   change p (starI v)+p (starJ (v.1+wrap n _,_))-p (starJ (v.1+wrap n _,_)) = _; rw [wrap_step,map_zero,add_zero]
variable (S:StepData c f)
set_option maxHeartbeats 200000 in
lemma heftZ (A:Lines S.ratio.count)(h:Whole A)(Z:Boxes G S.patch S.kernel)(x:Bid.Dir G c)(u:Odd S.ratio.count.val)(hv: installed S.ratio (Z.C.highCross Z.g)=tensor G (extracted S (forest S.ratio u) (installed S.ratio A))):
     let p:= installed S.ratio (kite G S.patch A)*ᵥ spool G c x
     lac G f p=installed S.ratio (chrome G.ColorIndex A)*ᵥ spool G c x ∧ lac G f (fderiv ℝ (fog G f) 0 p)=installed S.ratio (drip G S.ratio.count) *ᵥ (Z.main.acts c*ᵥ spool G c x):=by
     intro p; refine ⟨funext fun i=> kiteX S A (spool G c x) i,funext fun i=> ?_⟩; rw [fogStem p i,spun]
     let P:= installed S.ratio A; let W:=straighten S (forest S.ratio u) P; let Y:= parts G 1 x i.2.2; let j:Body 1 f:=(i.1,coord i.2.1); let q:= W*ᵥ Y; let U:= P*ᵥ Y
     have ht:p (starI i)=U j:=(kiteX S A _ i).trans (chromeRead S.ratio A _ i)
     have hf(l:Site f):p (starJ (l,i.2.2))=q (l,vac):= kiteY S A h x (l,i.2.2)
     rw [ht, hf, hf]
     let K':=extracted S (forest S.ratio u) P
     have he: (installed S.ratio (Z.C.highCross Z.g) *ᵥ flatten x) (lent G f i)=(K'*ᵥY) j:=by erw [hv]; exact congr_fun (component_mul K' (flatten x) i.2.2) j
     erw [he]; change _= ((P+Exterior.d 0 f * W)*ᵥ Y) j; rw [Matrix.add_mulVec,← Matrix.mulVec_mulVec]; change _= U j+(Exterior.d 0 f *ᵥ q) (i.1,coord i.2.1); rw [Exterior.d_sites]; exact add_sub_assoc _ _ _

end Script
end YM.OPE.Flume
