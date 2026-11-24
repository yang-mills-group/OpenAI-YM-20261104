import YM.OPE.Compatible.Vines.Foliage
/-! Cover gradient and variation -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free
open scoped Topology BigOperators Classical
variable {r d m n:ℕ}{c:ℝ}{I T W:Type*}
namespace Script
open Page
lemma ascentStep (x:Cover)(a:Axis): poise m (x+Lattice.step a) ≤ (2:ℝ)^m*poise m x:=by
   have hh: size (x+step a) ≤ size x+1:=by
       have ht : size (step a:Cover)=1:=by simp [size,Lattice.step,Pi.single_apply, apply_ite (fun j:ℤ=>j.natAbs),eq_comm]
       simpa only [← ht] using size_add x (step a)
   have he:notch (x+step a) ≤ 2* notch x:=by unfold notch; omega
   unfold poise; rw [← mul_pow]; gcongr; exact_mod_cast he
def cliff {u:Side} (w:Site u × W→ℝ):deck (Palette W) u:= fun i=>w (i.1+Lattice.step i.2.1,i.2.2)-w (i.1,i.2.2)
def mountain (w:fieldX W):fieldX (Palette W):=fun i=> w (i.1+step i.2.1,i.2.2)-w (i.1,i.2.2)
lemma crest {f:Filter I} {V:I→Side}{x:∀ i:I, Site (V i) × W→ℝ}{w:fieldX W}(h:Realized V f w x d): Realized V f (mountain w) (fun i=>cliff (x i)) d:=by
    have hx(i:I)(p:Cover× Palette W): unfoldX (cliff (x i)) p= mountain (unfoldX (x i)) p:=by simp [cliff,unfoldX,mountain]
    constructor
    · obtain ⟨C,hc,h⟩:=h.Once; refine ⟨C * 2^d+C,by positivity,fun i p=>?_⟩; rw [hx,mountain]; apply (norm_sub_le ..).trans; have ht : ‖unfoldX (x i) (p.1+step p.2.1,p.2.2)‖≤C*(2^d*poise d p.1):=(h i _).trans (mul_le_mul_of_nonneg_left (ascentStep (m:=d) p.1 p.2.1) hc)
      rw [add_mul,mul_assoc]; exact add_le_add ht (h i _)
    intro j; simp_rw [hx,mountain]; exact (h.Onset _).sub (h.Onset _)
-- anchor gradient test. Empty rank vac.
def abides (p:Script (Palette W) r):Prop:=∀ i:Fin r,∀ n:Side,∀ w,∀ s:Site n × W→ℝ, scribe (0:Site n) p (update w i (cliff s))=0
abbrev epochX (i:ℕ):Side:= ⟨i+1,Nat.succ_pos i⟩
lemma crest_zero (p:Script (Palette W) r)(h:p.abides)(hs:soot m p c) (x:Fin r→fieldX (Palette W))(i:Fin r)(w:fieldX W)(k:Fin r→ℕ)(hk:∑ i,k i≤m) (hx:∀ j,j≠i→Quiet (x j) (k j))(hp:Quiet w (k i)):
   wholeX p (update x i (mountain w))=0:=by
   let v j (n:Side):= closeX (x j) n; let q (n:ℕ):=update (fun j=> v j (epochX n)) i (cliff (closeX w (epochX n)))
   have he:= keepX hs q (m:=m) (V:=epochX) (u:=update x i (mountain w)) (k:=k) (f:=atTop) (fun j=> by
       have hv:= (show Tendsto (fun i=>(epochX i).val) atTop atTop from tendsto_add_atTop_nat 1); by_cases ht:j=i
       · subst j; simp only [q,update_self]; exact crest (received hv hp)
       simp only [q,update_of_ne ht]; exact received hv (hx j ht)) hk
   exact tendsto_nhds_unique_of_eventuallyEq he tendsto_const_nhds (Eventually.of_forall fun i:ℕ=> h ..)
-- color coordinate
end Script
end YM.OPE.Flume
