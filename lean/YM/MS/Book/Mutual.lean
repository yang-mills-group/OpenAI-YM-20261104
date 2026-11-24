import YM.MS.Book.Ranks
import YM.MS.Wilson.Stance
/-!
# Bare terms rank-local frame

Exactly rank k+2 for log-class and k for log-spinand. No loops in the classical
  calculation. Inherits all sym. Parameters independent of support length chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Book
open Function Set Filter Finset Koszul Cylinder Lab Plane
open Native Native.Chart Landau Native.Sew Native.Orient Color Native.Paint Lattice
open Native.Draft
variable {G:Gauge}{A P:Type}{q:ℤ}{v:Dot G P}

lemma TuneModel (h: Tuned v q)(n:ℤ): Tuned (model n v) q:= by
    refine ⟨(fun l i j r=>?_),(fun l hl=>?_),(fun l=>?_)⟩ <;> simp_rw [mask_s,mask];
    · have hx : (v.val) (l ++ i::j::r)= _:= h.symm l i j r; simp only [LinearMap.coe_mk,AddHom.coe_mk,List.length_append,List.length]; split <;> simp only [hx,mul_zero]
    · change (if (_:Prop) then _ else _)=0; rw [h.ghost l hl]; split <;> rfl
    simp only [LinearMap.coe_mk,AddHom.coe_mk]; split <;> simp [h.still l]
lemma ColorMod (h:Colorless v)(n:ℤ): Colorless (model n v):=fun i=> by
    apply Subtype.ext; change shade (tintC _ _) (model n v)=_; rw [mod_ink,show shade (tintC (stripe G P) i) v=(dye i v).val from rfl,h]; rfl -- change ambiguity
lemma enterShim {h:Seed A Cover ℂ} (b:Bool)(n:Side)(r:ℤ): duty b n (model r h)=mask r (duty b n h):= by
    let F:= (Ferry (post (A:=A) (wrap n)) (R:=ℂ)); cases b
    · change (F _).val=mask r (F h).val; unfold F; rw [mod_ferry]; rfl
    change (sumHome (F _)).val=mask r (sumHome (F h)).val; unfold F; rw [total_uses,total_uses]; simp_rw [mod_ferry,Lab.Shift,transport,mod_ferry,sum_stack,mask_s,map_sum]
lemma poseModel (r:ℤ)(u:Signed)(v:Dot G Cover): pose u (model r v)=model r (pose u v):= by simp_rw [pose,LinearMap.comp_apply,mod_tag,mod_ferry]
lemma stance_model {v:Dot G Cover}(h:stance v)(r:ℤ) : stance (model r v):= fun k=> (h k).mono (fun n h=> by
    change duty true n _= duty true n _; rw [poseModel,enterShim,enterShim]; exact congr_arg _ h)
lemma scene_add {F H:Dot G Cover}(h:stance F)(he:stance H): stance (F+H):= fun k=> ((h k).and (he k)).mono (fun i hx=>by rw [map_add,map_add,map_add,hx.1,hx.2])
lemma scene_sum {F:A→ Dot G Cover}(s:Finset A)(h:∀ i∈s,stance (F i)): stance (∑ i∈s,F i):= by
   classical
   refine fun k=> ((Finset.eventually_all s).mpr (fun i hi=> h i hi k)).mono (fun n H=>?_); rw [map_sum,map_sum,map_sum]; exact Finset.sum_congr rfl (fun i hi=> H i hi)
lemma scene_scale {F:Dot G Cover}(h:stance F)(c:ℂ): stance (c • F):= fun k=> (h k).mono (fun i h=> by rw [map_smul,map_smul,map_smul,h])

-- Roof. on any port gauge.
lemma limit_enter (n:Side){F:Seed A Cover ℂ}(h:Limit F.val q): Limit (enters n F) q:= Limit.shades F h _
lemma limit_sum (n:Side){F:Seed A Cover ℂ}(h:Limit F.val q): Limit (docket n F) q:= by
   change Limit (sumHome _).val q; simp_rw [total_uses,sum_stack]; refine Limit.sum _ (fun i _=>?_); exact Limit.shades _ (limit_enter n h) (way (post fun x=> i+x))
lemma limitLens (b:Bool)(n:Side){F:Seed A Cover ℂ}(h:Limit F.val q): Limit (duty b n F) q:= by cases b; exacts [limit_enter n h,limit_sum n h]
lemma limits {F:Seed A Cover ℂ}(h:∀ᶠ n in atTop, Limit (enters n F) q): Limit F.val q:= by
   intro l he; suffices model (l.length:ℤ) F=0 from (_root_.Eq.trans (show F.val l=(model (l.length:ℤ) F).val l from (enough _ rfl).symm) (by simp [this]))
   refine (enterEq ..).mp (h.mono fun n h=>?_); rw [map_zero,show enters n (model _ F)= _ from enterShim (b:=false) n (l.length:ℤ)]; funext k; by_cases hl:k.length=l.length; simp_rw [enough k (show (k.length:ℤ)=(l.length:ℤ) from by rw [hl])]; exact h k (by omega); exact strange _ (show (k.length:ℤ) ≠ (l.length:ℤ) from by omega)

-- Simple G needed rank1. Colorless fact local
lemma evacuated (h:G.Simple) (he:Colorless v) (i:LightMode G P): v.val [i]=0:= by
   rcases i with ⟨⟨i,j⟩,x⟩; refine Landau.single h (fun j=> v.val [((i,j),x)]) (fun u k=> ?_) j; exact Eq.trans (Eq.symm (by rw [repeat_cons]; simp only [wc,rep_nil,setLeg,at_D])) (congr_fun ( (dye_rep u v).symm.trans (congr_arg Subtype.val (he u))) [((i,k),x)])
lemma fromC (h:G.Simple)(hh:Colorless v)(ht:v.val []=0): From v.val 2:= by
   intro l he; by_cases hx:l=[]; exact hx ▸ ht
   obtain ⟨i,rfl⟩:= List.length_eq_one_iff.mp (show l.length=1 from by have hl : 0<l.length:=List.length_pos_iff.mpr hx; omega)
   exact evacuated h hh i
lemma from_pass {f: Seed A Cover ℂ} (n:Side)(h:From f.val q): From (enters n f) q:= by
   intro l hl; rw [← enough l (F:=enters n f) rfl,show mask (l.length:ℤ) (enters n f)= enters n (model _ f) from (enterShim (b:=false) n _).symm, show model (l.length:ℤ) f =0 from ?_,map_zero]; rfl
   apply Subtype.ext; ext k; by_cases he:k.length=l.length; exact (enough k (show (k.length:ℤ)=(l.length:ℤ) from by rw [he])).trans (h k (by omega)); exact strange k (show (k.length:ℤ) ≠ (l.length:ℤ) from by omega)
lemma from_total {f: Seed A Cover ℂ}(n:Side)(h:From f.val q): From (docket n f) q:= by
   intro l hl; rw [← enough l (F:=docket n f) rfl,show mask (l.length:ℤ) (docket n f)= docket n (model _ f) from (enterShim (b:=true) n _).symm, show model (l.length:ℤ) f =0 from ?_,map_zero]; rfl
   apply Subtype.ext; ext k; by_cases he:k.length=l.length; exact (enough k (show (k.length:ℤ)=(l.length:ℤ) from by rw [he])).trans (h k (by omega)); exact strange k (show (k.length:ℤ) ≠ (l.length:ℤ) from by omega)
end YM.MS.Book
