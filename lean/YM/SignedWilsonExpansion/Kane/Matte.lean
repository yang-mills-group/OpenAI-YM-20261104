import YM.SignedWilsonExpansion.Kane.Curb
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.SignedWilsonExpansion.Kane
open Function Filter Set Table Spec Climb Trace Trace.Pilot PhysMS PhysMS.Frame
open Extraction Order Spin Next.UVStress OPE OPE.Orbits Levy
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2 Dframe FVA2.Scale.Level Future
open Belfry Belle Dancer Belfry.Crisis Belfry.Classroom Belfry.ScaleFits Commission
open scoped BigOperators Topology ContDiff Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(W:ℝ→tower S)(L:Leading F W)
variable {b d e j n:ℕ}{ι:Type}{l:Filter ι}{g r ε:ι→ℝ}
namespace Tilted
open Asymptotics Real Belfry.Crisis Commission.Gram Dancer.Shell
open SeatsW
abbrev jump (r η:ι→ℝ)(i:ι):= r i*Real.exp (-η i)
abbrev Locked (r η:ι→ℝ)(l:Filter ι)(d:ℕ):= SeatsW.Discount ℂ l 1 (fun i=> bend W (r i) (jump r η i) d - Dial d ( η i ))
abbrev Sprint (W:ℝ→tower S)(d:ℕ)(l:Filter ι)(r ε g:ι→ℝ):= SeatsW.Discount ℂ l 1 (fun i=>bend W (r i) (ε i) d-Dial d ( g i ))
variable {F W}
omit L
lemma by_abs {α:ι→ℝ}{C:ℝ}(hq:∀ᶠ i in l,|α i|≤C): FO l α:= IsBigO.of_bound C (by simpa using! hq)
variable (p:FO l g)(t:Tendsto r l trail)
include p t
lemma recede : Tendsto (jump r g) l trail:=by
    have ht : Tendsto r l (𝓝 0):= t.mono_right nhdsWithin_le_nhds; refine tendsto_nhdsWithin_iff.mpr ⟨ (isLittleO_one_iff ℝ).mp ( ((isLittleO_one_iff ℝ).mpr ht).mul_isBigO ( bound_comp (S:=fun x=>Real.exp (-x)) (by fun_prop) p ) |>.congr_right fun i=> one_mul _ ), ( t.eventually self_mem_nhdsWithin ).mono fun i hp=> show 0 < r i*Real.exp (-g i) from mul_pos hp (Real.exp_pos _) ⟩
include L
abbrev MergeGeometry (v w:Sec G d)(x:ι→Points 2)(i:ι):= Paar ( PlotW F W none (r i) d 2 (x i)) ( bend W (r i) (jump r g i) d (Dial d (-g i) v) ) w
lemma testimony (d:ℕ)(a:Axis)(x:ι→Points 2)(s:Tendsto x l (𝓝 ( Gram.nodes a ))) (v:∀ u w: Sec G d,Tendsto (MergeGeometry (F:=F) (W:=W) (r:=r) (g:=g) u w x) l (𝓝 (Paar ( GramW G d a ) u w))) : Locked W r g l d:=by
    let A(i):= bend W (r i) (jump r g i) d; let D(i):= Dial d (G:=G) ( g i ); let N(i):=Dial d (G:=G) ( -g i ); let V(i):= PlotW F W none ( r i ) d 2 ( x i ); let X(i):=A i*N i-1;
    let E:= GramW G d a; let q(x:Sec G d × Sec G d): Module.Dual ℂ (FieldEnd G d):= ( Gram.acts E x.2 ).comp (LinearMap.applyₗ x.1); have vP(u w:Sec G d): Tendsto (fun i=> Paar ( V i ) u w) l (𝓝 ( Paar E u w )):= viaPlot L x (Gram.nodes a) (nodes_conf a) t s ( ![u,w]: Tags G d 2 ); have he:Discount ℂ l 1 X:=by
         refine Veto.guard (P:=q) (fun x h=> LinearMap.ext fun v=> onPeak a ( x v ) ( show _ from ( h (v,mirrorB a ( x v )) ))) (fun i j=> (Gram.acts ( V i ) j.2).comp (LinearMap.applyₗ j.1)) (fun i a=> vP ( a i.1 ) i.2) (fun u=>?_); have h:= (v u.1 u.2).sub (vP u.1 u.2); rw [sub_self] at h; refine ((isLittleO_one_iff ℝ).mpr h).congr_left (?_); intro i; simp_rw [MergeGeometry]; change Gram.acts (V i) u.2 _- Gram.acts ( V i ) u.2 _ = Gram.acts ( V i ) u.2 ((X i) u.1); unfold X; rw [LinearMap.sub_apply,map_sub]; rfl
    refine SeatsW.sameSalary ( dueLeft he ( boundD p d ) ) (Eventually.of_forall fun i=>?_ ) (.refl ..); exact PushEq (A i) (D i) (N i) ( FVA2.Scale.Level.spring _ )
where PushEq (A D N:FieldEnd G d)(h:N*D=1): (A*N-1)*D=A-D:=mul_push A D N h
      mul_push {S:Type}[Ring S](A D N:S)(h:N*D=1): (A*N-1)*D=A-D:=by rw [sub_mul,mul_assoc,h,mul_one,one_mul]
lemma PatchLocked {d:ℕ} (p':Locked W r g l d): Admits l (fun i=> Dial d (-g i)*bend W (r i) (jump r g i) d):=by
    let A(i):= bend W (r i) (jump r g i) d; let X(i):= Dial d (G:=G) (-g i); let D(i):= Dial d (G:=G) (g i); let Y(i):=X i*A i; refine ⟨ (?_), ( adm_bend L t ( recede p t ) d ).mono fun i hi=> ( adm.Dial _ d ).mul hi ⟩; let E:S' (L:=l) X:=boundD (θ:=-g) p.neg_left d; have he:= dueRight (x:=X) p' E; refine viaY (x:=1) (by simpa only [zero_add] using addY ( shine.mp he ) (constant (1:FieldEnd G d))) (Eventually.of_forall fun i=>?_); change X i*(A i-D i)+1=Y i; exact Epoch (K:=FieldEnd G d) (X i) (A i) (D i) (FVA2.Scale.Level.spring _)
where Epoch {K:Type}[Ring K](A D N:K)(h:A*N=1): A*( D-N )+1=A*D:=by rw [mul_sub,h,sub_add_cancel]
omit L t
lemma clockRise (d:ℕ)(c:Locked W r g l d): Sprint W d l (jump r g) r (-g) :=by
   let C (i):= bend W (r i) (jump r g i) d; let C'(i):= bend W (jump r g i) (r i) d; let D(i):= Dial d (G:=G) (g i); let D'(i):= Dial d (G:=G) (-g i); let F(i):= D' i*C i; let x(i):=C' i-D' i; let hV:= boundD p d (G:=G); let hp:S' (L:=l) D':= boundD (θ:=-g) p.neg_left d; have hL:Discount ℂ l 1 (fun i=>F i-1):= sameSalary ( dueRight c hp ) (Eventually.of_forall fun i=> Eq.symm ( role1 (D' i) ( C i) (D i) (FVA2.Scale.Level.spring _) )) (.refl ..)
   let A(i:ι):= F i * x i; have hA: Discount ℂ l 1 A:= sameSalary (dueLeft ( hL ) (y:=fun i=> -D' i) (fun T=>(by simp_rw [ map_neg T ]; exact (hp T).neg_left))) (?_) (.refl ..) 
   · have hz:By ℂ l F 1:= viaY (x:=1) (by simpa only [zero_add] using addY ( shine.mp hL ) (constant (1:FieldEnd G d))) (Eventually.of_forall fun i=> sub_add_cancel (F i) 1); refine Veto.guard (P:=fun i:Module.Dual ℂ (FieldEnd G d)=>i) (fun v p=> Veto.zero_guard (K:=ℂ) _ p) (fun i v=> v.comp (LinearMap.mulLeft ℂ (F i))) (fun i v=> by obtain hu:= hz ( i.comp ( LinearMap.mulRight ℂ v ) ); rw [ LinearMap.comp_apply, show (LinearMap.mulRight ℂ v) 1 = v from one_mul v ] at hu; exact hu) hA
   · apply Eventually.of_forall; intro i; have h: C i*C' i=1:=(bend_r ..).trans (bend0 ..); exact role2 ( C i ) (C' i) (D' i) h
where role1 {K:Type}[Ring K](A D N:K)(h:A*N=1): (A*D-1)= A*( D-N ):=by rw [mul_sub,h]
      role2 {K:Type}[Ring K](A D N:K)(h:A*D=1): (N*A-1)*(-N)= N*A*(D-N):=by rw [mul_sub, mul_assoc N A D,h,mul_one, sub_mul, mul_neg,one_mul,sub_neg_eq_add]; abel
omit p
-- Pea budgets addition
lemma until_K (d:ℕ)(p:FO l g)(q:FO l ε)(c:Locked W r g l d)(c': Locked W (jump r g) ε l d): Locked W r (g+ε) l d:= by
    let C (i):= bend W (r i) (jump r g i) d; let N(i):= bend W (jump r g i) (jump (jump r g) ε i) d; let D i:= Dial d (G:=G) (g i); let E i:= Dial d (G:=G) ( ε i ); let hx:S' (L:=l) N := fun T=> (( (c' T).isBigO.add (boundD q d T) ).congr_left (fun i=> by dsimp only; rw [map_sub T,sub_add_cancel] ));
    let he:= SeatsW.aboveCeiling ( dueLeft (y:=N) c hx ) ( dueRight c' (boundD p d)); refine SeatsW.sameSalary he (Eventually.of_forall fun i=>?_ ) (.refl ..)
    change (C i - D i)*N i+D i*(N i-E i)=_; unfold C N D E; rw [ sure (K:=FieldEnd G d), bend_r, FVA2.Scale.Level.group ]; dsimp only[jump,Pi.add_apply]; rw [neg_add,Real.exp_add,mul_assoc]

where sure {K:Type}[Ring K](A B C D:K): (A-B)*C+B*(C-D)= A*C - B*D:=by noncomm_ring
end Tilted
end YM.SignedWilsonExpansion.Kane
