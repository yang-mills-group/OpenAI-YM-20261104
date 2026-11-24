import YM.MS.Cylinder.Strokes
import YM.MS.Wilson.BareTuned
/-!
# Color tests on Wilson regs

Even continuum uses same E frame G. Full on all stencil sources. Body for W
 at each link.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Native.Paint
open Function Set Finset Plane Koszul Cylinder Lab Taylor Bare Focus Landau Sew Chart Draft
open Lattice Color
open scoped Topology ContDiff
variable {G:Gauge} {P Q:Type} (u:G.El)
-- harmless equivalence.
def stripe (G:Gauge)(P:Type): LightMode G P≃ ((Atom Axis×P) × CI G) where
   toFun i:= ((i.1.1,i.2),i.1.2)
   invFun i:= ((i.1.1,i.2),i.1.2)
   left_inv _:= rfl
   right_inv _:= rfl
def dye (u:G.El): Dot G P →ₗ[ℂ] Dot G P:= paint (stripe G P) u
lemma dye_rep (F:Dot G P) : (dye u F).val=repeatC u F.val:=by
   funext l; induction l generalizing F with
   | nil=> simp [dye,paint]
   | cons i l ih=>
       rcases i with ⟨⟨i,q⟩,x⟩; rw [D_eval _ (dye u F).val,repeat_cons, ← enterp]
       have he := palette (stripe G P) u (i,x) q F
       rw [show enter ((i,q),x) (dye u F)= ∑ j:CI G,wc u q j • dye u (enter ((i,j),x) F) from he]; simp_rw [sum_stack, Finset.sum_apply,smul_stack,Pi.smul_apply,ih]; rfl
lemma pigment (F H:Dot G P) : dye u (couple DotFlip F H)=couple DotFlip (dye u F) (dye u H):= paint_couple _ u (fun i j h=> congr_arg Landau.p (show i.1.1 = j.1.1 from congr_arg Prod.fst (show (i.1.1,i.2)=(j.1.1,j.2) from h))) F H
lemma painting (F:Dot G P)(r:P→Q) : transport r (dye u F)=dye u (transport r F) := paint_pass (stripe G P) u (stripe G Q) (post r) (Prod.map id r) (fun _ _=>rfl) F

-- Action on ports
lemma art_dye (u:G.El) [Fintype Q][DecidableEq Q] (W:Q→Edge P)(F:Lot G Q→ℝ):
   dye u (Sew.art W F)= Ferry (knot W) (paint (Equiv.refl (Q × CI G)) u (region.symm (ink priv F))):= Eq.symm (paint_pass (Equiv.refl _) u (stripe G P) (knot W) (fun q:Q=> (Landau.gauge (W q).2,(W q).1)) (fun _ _=> rfl) _)
section
variable [Fintype Q] [DecidableEq Q]
-- Note weight `g` transpose of acting on components earlier; check. tintR N u (i,y) = weight g i y, symbol transformation corresponds to applying g to test with basis e(i) -> sum_y weight g i y. So art_dye(U○ g).
def roll (u:G.El) : Lot G Q→L[ℝ] Lot G Q:= ContinuousLinearMap.pi fun j=>(G.adjoint u).toContinuousLinearMap ∘L ContinuousLinearMap.proj j
lemma mine (i j : CI G): Landau.weight u i j= G.adjoint u (baseC i) j:= rfl
omit [Fintype Q] in
lemma roll_at (i:Q)(j:CI G): roll u (priv (i,j))=∑ k:CI G,Landau.weight u j k • priv (i,k) := by
    funext t; rw [Finset.sum_apply]
    by_cases h:t=i; swap; · simp [roll,priv,h]
    subst i; change G.adjoint u (priv (t,j) t)=_; simp only [priv,Pi.single_apply, if_true,Pi.smul_apply]; exact (color_sum (G.adjoint u _)).symm
lemma art_roll (W:Q→Edge P)(F:Lot G Q→ℝ)(h:germ F): dye u (Sew.art W F)=Sew.art W (F ∘ roll u):= by
    rw [art_dye]; unfold Sew.art; congr! 1; apply Subtype.ext; rw [tint_ink (W:=roll u ∘ priv) (V:=priv) (N:= Equiv.refl _) _ h (fun i=> roll_at u i)]; exact (ink_ctrl_one _ _ h).symm
end
lemma byedge (x:Edge P)(F:G.Color→ℝ)(h:germ F): dye u (onedge x F)= onedge x (F ∘ G.adjoint u) := by unfold onedge; rw [art_roll _ _ _ (show germ (fun b:Lot G Unit=>F (b ())) from h.comp (f:=fun b:Lot G Unit=> b ()) 0 (contDiff_apply ..|>.contDiffAt))]; rfl

lemma GH_dye (i:Conn G)(x:P): dye u (GH i x)=∑ k:G.ColorIndex,wc u k i • GH k x:= stroke (stripe G P) u (ghost,x) i
lemma AHP_dye (i:Conn G)(x:Edge P): dye u (AHplus i x)=∑ k:G.ColorIndex,wc u k i • AHplus k x:= stroke (stripe G P) u (anti x.2,x.1) i
lemma GHP_dye (i:Conn G)(x:P): dye u (GHplus i x)=∑ k:G.ColorIndex,wc u k i • GHplus k x:= stroke (stripe G P) u (gaugeC,x) i

-- ∆ comm later. Wick use `Color.repeatC`.
def Colorless (F:Dot G P): Prop:= ∀ u:G.El,dye u F=F
lemma originW [AddCommGroup P](d:Chart.Rail P)(x:P): Colorless (weightW G d x):= by
    intro u; simp_rw [weightW,map_sum,art_roll u _ _ bill_gone];
    have he : gone (G:=G) ∘ roll u=gone:= by funext v; let T:=G.adjoint u; unfold gone; dsimp only [Function.comp_apply,atCart];
                                               change -G.price (G.lieExp (T (v 0))*G.lieExp (T (v 1))*(G.lieExp (T (v 2)))⁻¹*(G.lieExp (T (v 3)))⁻¹) = _; unfold T; simp_rw [Maurer.runby]; rw [show (u*G.lieExp (v 0)*_) * (u*_ *_) * _*_ = u*(G.lieExp (v 0)*G.lieExp (v 1)*(G.lieExp (v 2))⁻¹*(G.lieExp (v 3))⁻¹)*u⁻¹ by group,G.price_conj]
    simp_rw [he]
lemma originH (x:P): Colorless (weightH G x):= by intro u; simp_rw [weightH,map_sum,byedge _ _ _ (Maurer.hlog G),funext (show ∀ x,(Maurer.lac ∘ G.adjoint u) x=Maurer.lac x from Maurer.lac_pass u)]
end YM.MS.Native.Paint
