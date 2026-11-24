import YM.OPE.Compatible.Seeds.Twig
/-!
# Opal preserves full gradient Ward. `N=L*c` here n.b.B requires every c -- use positive block mean all c from Woods. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Exterior Matrix FreeResolvent Precision Tree Woody Bloch Work.F08
open scoped Topology BigOperators Classical
variable {r d' j k:ℕ}{U:ℝ}{V I W:Type*}{G:Gauge}{c f:Side}{L:KernelChoices}{P:Flight j k}
namespace Script
open Page
-- extraction uses all fine fibers and fine gradient straightening
variable {S:StepData c f}{F:Forest S.ratio}
lemma firesField (S:StepData c f)(F:Forest S.ratio)(A:Cross S.ratio.count (TypeFace 1) (TypeFace 1))(H:FaceRow)(B:FaceRow)(hp: Inputs S (installed S.ratio A) (H.acts f) (B.acts c)) : baseMatrix S H * extracted S F (installed S.ratio A)= S.kernel.penalty • (probe S).transpose:=by
   let z:=extracted S F (installed S.ratio A); obtain ⟨hx,hh⟩:=stationed F _ _ _ hp; unfold baseMatrix; rw [Matrix.add_mul,Matrix.smul_mul,hh,Matrix.mul_assoc,hx,Matrix.mul_sub,Matrix.mul_one,Matrix.mul_smul,smul_sub,smul_smul,mul_inv_cancel₀ S.kernel.penalty_pos.ne',one_smul]; abel
lemma folded (H:FaceRow)(h:(treeMatrix G S F H).PosDef){w v:Vec G f 1}(he:fullMatrix G S H *ᵥ w= fullMatrix G S H *ᵥ v):∃ u: Vec G f 0,w=v+FreeResolvent.gradient u:=by
    let p(t:Vec G f 1):=representative S F t; let q(t):=reduce G S F *ᵥ p t; let i:= insertion (plant (G:=G) F); have hv(t):p t=i *ᵥ q t:=(projects F _ (onto_slice F t)).symm
    suffices hp:p w=p v by
       let u:= potential (S:=S) F w; let y:=potential (S:=S) F v; have ht: w+FreeResolvent.gradient u=v+FreeResolvent.gradient y:=hp
       refine ⟨y-u,?_⟩; unfold FreeResolvent.gradient at ht ⊢; rw [Matrix.mulVec_sub, ← add_sub_assoc, ← ht, add_sub_cancel_right]
    let M:=treeMatrix G S F H; have hm: IsUnit M.det:= by
       -- inv mat
       exact h.det_pos.ne'.isUnit
    have hx : M *ᵥ q w=M *ᵥ q v:=by
       rw [show M=reduce G S F*fullMatrix G S H*i from (insertion.compress ..).symm]
       simp_rw [← Matrix.mulVec_mulVec, ← hv]
       rw [show fullMatrix G S H*ᵥp w= _ from invariant F H w, show fullMatrix G S H *ᵥ p v=_ from invariant F H v,he]
    have hz:q w=q v:=by
        have he:= congr_arg (fun t=> M⁻¹ *ᵥ t) hx; rw [Matrix.mulVec_mulVec (q w), Matrix.mulVec_mulVec (q v), Matrix.nonsing_inv_mul _ hm,Matrix.one_mulVec, Matrix.one_mulVec] at he; exact he
    rw [hv,hv v,hz]
lemma planes (w:Vec G c 1) (A:Cross S.ratio.count (TypeFace 1) (TypeFace 1)):
    tensor G (extracted S F (installed S.ratio A)) *ᵥ w=tensor G (installed S.ratio A) *ᵥ w+FreeResolvent.gradient (tensor G (straighten S F (installed S.ratio A)) *ᵥ w):=by
      ext ⟨x,i,j⟩; rw [Pi.add_apply]; change component (tensor G _ *ᵥ w) j (x,i)= component (tensor G _ *ᵥ w) j (x,i)+component (FreeResolvent.gradient (tensor G _ *ᵥ w)) j (x,i); rw [component_mul,component_mul,extracted,Matrix.add_mulVec,← Matrix.mulVec_mulVec, Pi.add_apply,FreeResolvent.gradient, component_mul,component_mul]
lemma glide (S:StepData c f)(H B:FaceRow)(F:Forest S.ratio)(h:(treeMatrix G S F H).PosDef)(A:Cross S.ratio.count (TypeFace 1) (TypeFace 1))(hp:Inputs S (installed S.ratio A) (H.acts f) (B.acts c)) (a: Site c × G.ColorIndex→ℝ):∃ v:Site f× G.ColorIndex→ℝ, installed S.ratio (chrome G.ColorIndex A) *ᵥ cliff a=cliff v:=by
   rw [stage_mul]; let x:Vec G c 0:=fun i=>a (i.1,i.2.2); have hx:(deckW G c).symm (cliff a)=FreeResolvent.gradient x:=by rw [← (show deckW G c (FreeResolvent.gradient x)=cliff a from slopeCliff x),LinearEquiv.symm_apply_apply]
   let q:Vec G f 0:=fun i=>a (S.ratio.parent i.1,i.2.2); have ht (j:G.ColorIndex): Precision.centered S (component q j)=component x j:=funext fun i=>congr_arg a (Prod.ext (S.ratio.embed_parent i.1) rfl)
   let s:=FreeResolvent.gradient x; let fV:=tensor G (extracted S F (installed S.ratio A)) *ᵥ s; have hpX:fullMatrix G S H *ᵥ fV= fullMatrix G S H *ᵥ FreeResolvent.gradient q:=by
       ext ⟨x,i,j⟩; change component (fullMatrix G S H *ᵥ fV) j (x,i)=component (fullMatrix G S H *ᵥ FreeResolvent.gradient q) j (x,i); unfold fullMatrix fV; simp_rw [component_mul]; nth_rw 1 [Matrix.mulVec_mulVec]; rw [firesField S F A H B hp]; unfold s FreeResolvent.gradient baseMatrix; simp only [component_mul]; rw [Matrix.add_mulVec, Matrix.mulVec_mulVec _ (Precision.K _),K_kills,Matrix.zero_mulVec,zero_add,Matrix.smul_mulVec, Matrix.smul_mulVec,← Matrix.mulVec_mulVec,root_gradient,ht]
   obtain ⟨u,hu⟩:=folded H h hpX; let y:= tensor G (straighten S F (installed S.ratio A)) *ᵥ s; let t:= q+u-y; have htX:tensor G (installed S.ratio A) *ᵥ s=FreeResolvent.gradient t:=by
      apply add_right_cancel (b:=FreeResolvent.gradient y); erw [← planes (F:=F)]; change fV=_; rw [hu]; unfold FreeResolvent.gradient t; rw [Matrix.mulVec_sub,Matrix.mulVec_add]; abel
   rw [hx,htX,slopeCliff]; exact ⟨_,rfl⟩
end Script
end YM.OPE.Flume
