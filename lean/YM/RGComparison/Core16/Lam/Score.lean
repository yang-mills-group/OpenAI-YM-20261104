import YM.RGComparison.Core16.Lam.Peak
import YM.RGComparison.Core16.Silk.Kite
/-!
# Kin slope probes & Θ closure

ACTUAL primal torus unconditional density along blocking V fixed, hS.Step. No dropping clipped
flag supports inside here; field rank uses genuine `Forward` ratio including shared tag averaging
on multiply-hit scores. Cumulant correction addresses according to actual Gear stencil.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lam
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity Finset
open Precision Push.BetaTransport Next.Fluctuations Pressure
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S:StepData c f}

abbrev Operand (G:Gauge)(c:Side):= Wire G (Bond c)

-- unwrap calculus collars explicitly so available pointwise at meter. Works even if y=z with different directions. Tensor hyper.
section score
variable {E Q F:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup Q][NormedSpace ℝ Q] (u:E→L[ℝ] Q)
lemma along (f:Q→ℝ)(h:ContDiff ℝ ∞ f)(x y:E) : lend (f ∘ u) x y=lend f (u x) (u y) := by
     let g(t:E):=u t
     have hx: Hess f 0 (u x) (u y)= iteratedFDeriv ℝ 2 f 0 ![u x,u y]:= by rw [iteratedFDeriv_two_apply]; rfl
     have hy: lend (f ∘ u) x y=iteratedFDeriv ℝ 2 (f ∘ u) 0 ![x,y]:=by rw [iteratedFDeriv_two_apply]; rfl
     rw [hy]; change _= Hess f 0 (u x) (u y); rw [hx,u.iteratedFDeriv_comp_right (contDiff_infty.mp h 2) _ le_rfl,ContinuousMultilinearMap.compContinuousLinearMap_apply,map_zero]
     exact congrArg _ (funext fun i:Fin 2=> by fin_cases i <;> rfl) -- dependent?
end score

variable (K:KernelChoices)(x y:G.Color)(p:G.Mat)

def over (p:G.Mat)(v:G.Color) : ℝ:= Lam.arm K (v,p)

lemma over_hot (v:G.Mat):ContDiff ℝ ω (Lam.over K v):=(arm_hot K).comp (f:=fun y:G.Color=>(y,v)) (contDiff_id.prodMk contDiff_const)

lemma swirl : ContDiff ℝ ω (fun p:G.Mat=> line1 (Lam.over K p) 0 x):= (ContinuousLinearMap.apply ℝ ℝ x).contDiff.comp ((by apply ContDiff.fderiv (m:=ω) (f:=fun y u=> arm K (u,y)) (g:=fun _=>0); exact (arm_hot K|>.comp (contDiff_snd.prodMk contDiff_fst)); exact contDiff_const; exact le_top) : ContDiff ℝ ω (fun y:G.Mat => fderiv ℝ (over K y) 0))
lemma tilt : ContDiff ℝ ω (fun p:G.Mat=> lend (Lam.over K p) x y):= by
    let V:= arm (G:=G) K
    let u(L:G.Color × G.Mat):=fderiv ℝ (fun u=> V (u,L.2)) L.1
    have h: ContDiff ℝ ω u := ContDiff.fderiv (m:=ω) (f:=fun (p : G.Color × G.Mat) (q : G.Color)=> V (q,p.2)) ((arm_hot K).comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))) contDiff_fst le_top
    let v i:= fderiv ℝ (fun j:G.Color=>u (j,(i:G.Mat))) 0; have hh : ContDiff ℝ ω v:=ContDiff.fderiv (m:=ω) (f:=fun (v:G.Mat)(w:G.Color)=> u (w,v)) (h.comp (contDiff_snd.prodMk contDiff_fst)) contDiff_const le_top
    let A:=(ContinuousLinearMap.apply ℝ ℝ y).comp (ContinuousLinearMap.apply ℝ (G.Color→L[ℝ] ℝ) x); exact A.contDiff.comp hh
lemma slope_zero (K:KernelChoices)(x:G.Color): line1 (Lam.over K (1:G.Mat)) 0 x=0:= by
    let p:=over (G:=G) K 1; have hx : IsLocalMin p 0:= by
       apply Eventually.of_forall; intro y; change p 0≤p y; unfold p over; rw [← G.mat_one,← installs K (G.lieExp 0) (1:G.El) 0 rfl, ← installs K (G.lieExp y) (1:G.El) y rfl]; rw [G.mat_lieExp_zero, mul_one,G.price_one]; rw [mul_zero]; exact mul_nonneg K.penalty_pos.le (G.price_range _).1 -- mat? equality notation
    rw [line1,hx.fderiv_eq_zero]; rfl

variable (S) (a b:Operand G c)(p:News G c)

def compass (a:Operand G c): Directions G c  := Pi.single a.1 (colors G a.2) -- Lumen.one

def teller (S:StepData c f) (i: Bond c)(p:News G c)(v:Directions G c):= over (S.kernel) (p.2.2 i) (v i)
lemma lights (i:Bond c): ContDiff ℝ ∞ (teller S i p):= ((over_hot S.kernel _) |>.of_le le_top).comp (contDiff_apply ℝ _ _)


lemma sparse (i:Bond c) : line1 (teller S i p) 0 (compass a)= if i=a.1 then line1 (Lam.over S.kernel (p.2.2 i)) 0 (colors G a.2) else 0 := by
    let L: Directions G c →L[ℝ] G.Color := ContinuousLinearMap.proj i; let F:= Lam.over (G:=G) S.kernel (p.2.2 i)
    change fderiv ℝ (F ∘ L) 0 _= _; rw [fderiv_comp 0 ((over_hot _ _).differentiable (by simp : (ω:WithTop ℕ∞)≠0) _) L.differentiableAt,ContinuousLinearMap.fderiv]; rw [map_zero]; change fderiv ℝ F 0 (compass a i)=_; unfold compass; split; rename_i h;
    · rw [h,Pi.single_eq_same]; unfold line1 F; rw [h]
    rw [Pi.single_eq_of_ne (by assumption),map_zero]
lemma priced (i:Bond c) : lend (teller S i p) (compass a) (compass b)= if i=a.1∧i=b.1 then lend (Lam.over S.kernel (p.2.2 i)) (colors G a.2) (colors G b.2) else 0 := by
    let L : Directions G c→L[ℝ] G.Color:= ContinuousLinearMap.proj i; let E:= Lam.over (G:=G) S.kernel (p.2.2 i); rw [show teller S i p=E ∘ L from rfl,along L E ((over_hot _ _).of_le le_top)]; change Hess E 0 ((Pi.single a.1 (colors G a.2):Bond c→ G.Color) i) ((Pi.single b.1 (colors G b.2):Bond c→ G.Color) i)=_; by_cases h:i=a.1; swap; rw [Pi.single_eq_of_ne h,if_neg (fun hh=>h hh.1),map_zero]; rfl; -- goal split semicolon?
    rw [show (Pi.single a.1 (colors G a.2):Bond c→ G.Color) i=colors G a.2 from by rw [h,Pi.single_eq_same]]; by_cases he:i=b.1; · rw [show (Pi.single b.1 (colors G b.2):Bond c→ G.Color) i=colors G b.2 from by rw [he, Pi.single_eq_same], if_pos ⟨h,he⟩]; rfl
    rw [Pi.single_eq_of_ne he,if_neg (fun hh=>he hh.2),map_zero]

-- roll upward world level.
lemma sensor : raise S (compass a) p=line1 (Lam.over S.kernel (p.2.2 a.1)) 0 (colors G a.2) ∧
    tip S (compass a) (compass b) p= if a.1=b.1 then lend (Lam.over S.kernel (p.2.2 a.1)) (colors G a.2) (colors G b.2) else 0:=by
    let μ:= univ (α:=Bond c); let f:= (teller S · p); let Z:=fun x=>∑ i : Bond c,f i x
    have hz : fderiv ℝ (tax S p)=∑ i:Bond c,fderiv ℝ (f i):=by
         funext v; have hd: HasFDerivAt Z _ _:= HasFDerivAt.fun_sum (u:=univ) (fun i _=>(Diff (lights S p i) v).hasFDerivAt)
         rw [Finset.sum_apply]; exact (hd.const_add p.2.1).fderiv -- tax definally?
    unfold raise tip lend line1 Hess; rw [hz,Finset.sum_apply,(HasFDerivAt.sum (u:=univ) (fun i _=>(wander (lights S p i) 0).hasFDerivAt)).fderiv]; simp_rw [_root_.sum_apply]
    change (∑ i,line1 (teller S i p) 0 (compass a))=_ ∧ (∑ i,lend (teller S i p) (compass a) (compass b))=_
    simp_rw [sparse, priced]; constructor
    · simp [Finset.sum_ite_eq']  -- no proof relation
    by_cases h:a.1=b.1; · simp [h, lend, Hess]
    rw [if_neg h]
    apply sum_eq_zero; intro i hi; rw [if_neg (fun he=> h (he.1.symm.trans he.2))]
end YM.RGComparison.Core16.Lam
