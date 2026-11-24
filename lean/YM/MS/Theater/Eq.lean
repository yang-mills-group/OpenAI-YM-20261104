import YM.MS.Theater.Radium
/-!
# Comparing the one-leg Hessian equation constraint with the zero-set of explicit Shell jets
 Two versions.Dimension S.Body. Fourier signs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Theater
open Set Function Filter Finset MeasureTheory Real Maxwell
open Analysis Tensor Koszul Plane Landau Detect Local.BV InnerProductSpace Submodule Momentum
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G: Gauge}{h:ℕ}{t p:FourP}
local notation "Ω"=> Feet G ( h+1+1 )
variable (G) in
def dia0 (i:ℕ)(u v:Axis) : Feet G (i+1+1)→ₗ[ℝ] Feet G i:= ( stepL G Axis i u ) ∘ₗ (stepL G Axis (i+1) v)
abbrev pairK (X:Feet G (h+2))(a b:Axis): T E4 G.Color h:= ( ( dia0 G h a a X ).val b - ( dia0 G h a b X ).val a ) -- no sum. D(b,b) maybe; b fixed outer
lemma Ω_s (X: Feet G ( h+1+1 ))(a b:Axis): Tensor.Sym (pairK X a b) := by intro x s; unfold pairK; simp only [sub_apply, ( dia0 G h a a X ).property b x s,( dia0 G h a b X ).property a x s]
def Hess (G:Gauge)(h:ℕ): Feet G (h+2) →ₗ[ℝ] Feet G h where
   toFun X:= ⟨fun b=> ∑ a:Axis,pairK X a b, fun b x s=>by simp only [_root_.sum_apply, Ω_s X _ b x s]⟩
   map_add' := fun x y=> by apply Subtype.ext; ext1 i; apply ContinuousMultilinearMap.ext; intro l; simp [pairK, Finset.sum_add_distrib]; abel
   map_smul':= fun c x=> by apply Subtype.ext; ext1 i; apply ContinuousMultilinearMap.ext; intro l; simp [pairK,Finset.smul_sum,smul_sub]
lemma pair_z (X:Ω)(a b:Axis): pairK X a b=( ( dia0 G h a a X ).val b - ( dia0 G h a b X ).val a ):= rfl
local notation "Λ"=> Hess G h
lemma scenic (p:FourP)(a b:Axis) (v:G.Color)(l:Fin h→ E4): ( Λ ( speak (h+2) a p v ) ).val b l=precision a b p • ( speak h b p v ).val b l:= by
    classical
    change (∑ i:Axis,pairK (speak _ a p v) i b) l=_; rw [_root_.sum_apply]; have hx i (j:Axis): dia0 G h i j (speak (h+2) a p v)=(p i*p j) • speak h a p v:= by rw [dia0,LinearMap.comp_apply,step_at,map_smul,step_at,mul_smul,smul_comm]
    simp_rw [ pair_z,hx,sub_apply,Submodule.coe_smul,Pi.smul_apply,smul_apply,Finset.sum_sub_distrib ];
    let u:= amount h • ((∏ i,inner ℝ (fixF p) ( l i )) • v); have he (i:Axis): (speak h a p v).val i l= if i=a then u else 0 := by
       split
       next he=> rw [he, speak, wearing]
       next hx=> rw [speak, away _ _ _ hx]; rfl
    rw [precision,delta, show (speak h b p v).val b l=u from wearing .. ]; simp_rw [ he ]; by_cases hb:a=b
    · simp [hb, Momentum.sq,pow_two,Finset.sum_smul, sub_smul, smul_ite]
    simp [hb,Ne.symm hb,smul_ite]
lemma synth (i:Axis)(v:G.Color) : Λ ( speak (h+2) i p v )= ∑ a:Axis,precision i a p • speak h a p v:= by
    apply Subtype.ext; ext1 j; apply ContinuousMultilinearMap.ext; intro u; rw [AddSubmonoidClass.coe_finsetSum,Finset.sum_apply]; rw [_root_.sum_apply, Finset.sum_eq_single_of_mem j ( Finset.mem_univ _ ) ]; exact scenic p i j v u; intro x hx he; change precision i x p • ( planeC x h _ v ).val j u= _; rw [away h _ _ (Ne.symm he),ContinuousMultilinearMap.zero_apply,smul_zero] 
lemma d2diag (X:Ω)(a b i:Axis): diagonal ((dia0 G h a b X).val i)= grad a ( grad b ( diagonal ( X.val i ) ) ):= by unfold dia0 stepL; rw [LinearMap.comp_apply,workL, workL]; rfl
-- h=0 absent
lemma allG (G:Gauge): onShell G.Color 0=formSpace 0 G.Color:= by
    apply le_antisymm _ _; exact fun i hi=> hi.1; refine fun i hi=> ⟨ hi,fun b x=>?_⟩; refine Finset.sum_eq_zero fun j _=>?_ ; rw [show Tensor.diagonal (i j b)=fun (_:E4)=> i j b (fun _=>0) from funext fun x=>congr_arg ( i j b ) (Subsingleton.elim ..)]; simp [grad,Analysis.D]
lemma paid0 (X: Labels.Taylor G 0): takeCurl X ∈ onShell G.Color 0:= by rw [ allG ]; exact closedCurl X
lemma funS (X:Labels.Taylor G (h+1))(b:Axis)(x:E4): diagonal (( Λ (step_in G _ X )).val b) x= ∑ a:Axis, grad a (diagonal ( takeCurl X a b )) x:= by
    have he: diagonal ((Λ (step_in G (h+1) X)).val b) x=∑ a:Axis, diagonal ( pairK ( step_in G (h+1) X ) a b ) x:= (by unfold Tensor.diagonal; change (∑ a:Axis,pairK (step_in G (h+1) X) a b) _=_; rw [_root_.sum_apply]); rw [ he ]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [takeCurl_diag]; rw [pair_z]; rw [show ∀ (A B:Tensor.T E4 G.Color h), Tensor.diagonal (A-B) x=A (fun _=>x)-B (fun _=>x) from fun A B=> rfl]; -- convert to grad.A.B
    let U:= step_in G (h+1) X; change diagonal ((dia0 G h i i U).val b) x- diagonal (( dia0 G h i b U).val i) x=_; rw [d2diag, d2diag]; unfold grad Analysis.D;
    have hV (a b:Axis): DifferentiableAt ℝ ( grad a ( X.value b )) x:= (grad_smooth (m:=∞) _ ( diag_smooth ( X.val b ) ∞ ).contDiffAt (by simp)).differentiableAt (by simp); change _=fderiv ℝ ( grad i (X.value b)- grad b (X.value i)) x (basis i); rw [fderiv_sub ( hV i b ) ( hV b i )]; rfl
lemma attended (X:Labels.Taylor G (h+1)): takeCurl X∈ onShell G.Color (h+1)↔Λ (step_in G _ X)=0:= by
    constructor; · intro hp; apply absolute; intro i p; rw [ funS ]; exact hp.2 i p
    intro hv; exact ⟨ closedCurl X,fun i x=>by rw [ ← funS,hv ]; rfl⟩ -- indent
lemma centring (X:Labels.Taylor G h): (∃ Y: Shell G h, X = gaugeJet Y) ↔ takeCurl X ∈ onShell G.Color h := by
    refine ⟨?_,?_⟩; · rintro ⟨x,rfl⟩; rw [match_leg]; exact x.property
    intro h; refine ⟨ ⟨ _,h ⟩, ( potential_recover X ).symm ⟩
-- clear gradient list. by plane.s
lemma grad_pays : ( Hess G h ).comp (gradS G (h+2) )=0:= by
    let L:= gradS G (h+2); apply LinearMap.ker_eq_top.mp; refine top_le_iff.mp ?_; rw [ ← termsTop ]; rw [Submodule.span_le]; rintro x ⟨i,c,p,rfl⟩; change Λ (L ( speak (h+2+1) () ( out p ) (cl G c))) = 0; let q:= out p; let v:= cl G c; change Λ (gradS G (h+2) ( speak _ _ q v ))=_; rw [grad_at,map_sum]; simp_rw [map_smul,Theater.synth, Finset.smul_sum, smul_smul ]; rw [ Finset.sum_comm ]; refine Finset.sum_eq_zero fun i _ => ?_; simp_rw [ show ∀ k:Axis,q k* precision k i q= _ from fun k=> mul_comm (q k) ( precision k i q ), ← Finset.sum_smul ]; rw [ Landau.Detect.Mark.kernel_zero,zero_smul ]
end YM.MS.Theater
