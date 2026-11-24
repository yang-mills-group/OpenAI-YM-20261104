import YM.OPE.Compatible.Gully.Sane
/-! # Mesoscopic marker pickup -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.StageLight
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir Nestle Balsam Port
open GaussianScore Libra WithLp RG Precision Votive
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {n m:Side}{G:Gauge}{C:RG.KernelChoices}{r:ℕ}{U:Gloam}
variable {X: Type*}[AddCommGroup X]
def stern (x:Axis)(f:Cover→X)(v:Cover):=f (v-step x)-f v
def rain (l:List Axis)(f:Cover→X):= l.foldr stern f
def zine (p:Pose)(f:Axis→Cover→X):X:= rain p.m (stern p.a (f p.b)-stern p.b (f p.a)) (-p.x)
lemma tip_zero (p:Pose)(v:Site n):tip p (0:Axis→Site n→X) v=0:=by unfold tip; simp_rw [Pi.zero_apply,show ∀ i,fwd i (0:Site n→X)=0 from fun i=>funext fun x=>sub_self (0:X),sub_self,zeroKn,Pi.zero_apply]
lemma zine_tent (p:Pose)(v:Site n)(f:Axis→Site n→X): tip p f v=zine p (fun i y=> f i (v-wrap _ y)):=by
    let L(b:Cover):=v-wrap n b; have h(i:Axis)(g:Site n→X)(u:Cover):fwd i g (L u)=stern i (g ∘ L) u:=by unfold fwd stern; simp only [_root_.Function.comp_apply,L,map_sub,wrap_step]; congr 2; abel
    have he(l:List Axis)(b:Cover)(f:Site n→X): Knot l f (v-wrap n b)=rain l (f ∘ L) b:=by induction l generalizing b with
       | nil=>rfl
       | cons i l ih=>change fwd i (Knot l f) (L b)=_; rw [h]; unfold stern; simp only [_root_.Function.comp_apply,L]; rw [ih,ih];rfl
    unfold tip; rw [show v+wrap _ p.x=v-wrap _ (-p.x) from by simp,he]; change _= rain _ _ _; refine congrArg (fun f:Cover→X=> rain p.m f (-p.x)) ?_; funext i; rw [Function.comp_apply,Pi.sub_apply,h,h];rfl
lemma zine_sub (p:Pose)(f g:Axis→Cover→X):zine p (f-g)=zine p f-zine p g:=by
   have he(l:List Axis)(b:Cover)(g h:Cover→X): rain l (g-h) b=rain l g b-rain l h b:=by induction l generalizing b with | nil=>rfl | cons i l ih=>change rain l _ _-rain l _ _=(rain l _ _ -rain l _ _)-(rain l _ _-rain l _ _);rw [ih,ih];abel
   unfold zine; rw [←he]; apply congr_fun; congr 1; funext i; simp only[stern,Pi.sub_apply];abel
variable {d:ℝ}{k:ℕ}{g:ℕ→ Cover→ℝ}
lemma vesture (x:Axis)(hf:Port U d k g): Port U d (k+1) (fun i=> stern x (g i)):=by
    let h:=shutter (-step x) (smear x g); rw [show (fun i=>stern x (g i))= -h from ?_]; exact ((hf.split _).pass _).neg_s; funext i y; unfold stern; change _= -(g i (y+ -step x+step x)-g i (y+ -step x)); simp [sub_eq_add_neg]
lemma v_rain (l:List Axis)(hf:Port U d k g): Port U d (k+l.length) (fun i=>rain l (g i)):=by induction l with |nil=>exact hf|cons x l ih=>rw [List.length_cons,←add_assoc]; exact vesture _ ih
lemma focal {X:Panels}(p:Pose)(hp:∀ i,Port U d k (X i)):∃ c,Bloom U (k+p.heat-1) (fun i=> zine p (fun j=> X j i)) c:=by
    have he(a b'):=vesture a (hp b'); let g(i):= stern p.a (X p.b i)-stern p.b (X p.a i); have hv: Port U d (k+1) g:=port_minus (he _ _) (he _ _); rw [show k+p.heat-1=k+1+p.m.length from by unfold Pose.heat;omega]; exact ((v_rain _ hv).lo).sell _
abbrev GammaSite (U:Gloam)(k:ℕ)(f:ℕ→ℝ):Prop:=Cleared U (fun i=>(U.h i^k)⁻¹*f i)
lemma prom (x y:Crew U)(p q:Pose)(h:x≠y): GammaSite U (p.heat+q.heat) (fun i=> tip q (fun a=>vote p x a i) (y.val i)):=by
    let z:= fun i=>(x.val i)-(y.val i); let V:=vote p x; let g:=peekX y V; have hp:z 0≠0:=fun hh=> h (drum _ _ (sub_eq_zero.mp hh)); let A:=p.cuff (fun D=> ebb D U z); have ht:=p.cuff_far (z:=z) (fdroon x.property y.property) hp; have hm:g=A:=by
         funext b i v; have ha:x.val i-(rumB y i v)+wrap _ p.x=z i+wrap _ (v+p.x):=by dsimp only [z,rumB]; rw [map_add]; abel
         unfold g A V peekX vote paper Pose.Lck; rw [ha]; change _= (((if b=p.b then shutter p.x (ebb (p.a::p.m) U z) else 0)-(if b=p.a then shutter p.x (ebb (p.b::p.m) U z) else 0)) i v); split_ifs <;>rfl
    have he:(fun i=>tip q (fun a=> V a i) (y.val i))=(fun i=> zine q (fun j=>g j i)):=funext fun i=> zine_tent _ _ _
    change GammaSite U _ (fun i=>tip q (fun a=> V a i) (y.val i)); rw [he,hm]; obtain ⟨c,h⟩:= focal (X:=A) q ht.ports; rw [show p.heat+1+q.heat-1=p.heat+q.heat from by omega] at h; exact h.2.1
lemma prom_same (x:Crew U)(p q:Pose)(H:∀ i,Even (U.M i).val):GammaSite U (p.heat+q.heat) (fun i=> tip q (fun a=> vote p x a i) (x.val i)-zine q p.icicle):=by
   let A:=p.cuff (fun D=> flood D U); have ht: ShiftRay U (1/2) (p.heat+1) A:=p.cuff_pin (Eventually.of_forall H)
   have he(i):tip q (fun a=>vote p x a i) (x.val i)- zine q p.icicle=zine q (fun b=>A b i):=by
       rw [zine_tent,←zine_sub]; congr 1; funext b v
       change paper p b _ _-p.icicle b v=A b i v; unfold paper; rw [sub_sub_cancel,←map_add]; unfold Pose.Lck; change _-((if b=p.b then hull (p.a::p.m) (v+p.x) else 0)-(if b=p.a then hull (p.b::p.m) (v+p.x) else 0)) = (((if b=p.b then shutter p.x (flood (p.a::p.m) U) else 0)-(if b=p.a then shutter p.x (flood (p.b::p.m) U) else 0)) i v); split_ifs <;> simp only [Pi.sub_apply,flood,shutter,seam,Pi.zero_apply] <;> ring
   simp_rw [he]; obtain ⟨c,h⟩:=focal q ht.ports; rw [show p.heat+1+q.heat-1=p.heat+q.heat from by omega] at h; exact h.2.1
end YM.OPE.StageLight
