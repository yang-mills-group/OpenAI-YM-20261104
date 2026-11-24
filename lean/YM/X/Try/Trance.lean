import YM.X.Try.Censor
import YM.X.Rank.Relate
/-!
# Texture readings with fixed lowest quadratics determine parity even across horizon SIX, even if H dropped. Use when kernels of unrestricted (non-H) frame drift may be unbounded along meshes. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tri
open Maxwell Maxwell.Free Wick MvPolynomial Function Set Filter
open PertExtension Heat.Top Next.Rank.Normal Rank
open Pert Pert.Position Pert.RawLabels
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{d n k:ℕ}(F:Labels.Frames G) (h:G.Simple)
local notation "T"=> Tile G.ColorIndex
variable (x:Fiber G→ℂ)(p:WickPol G)(v:E4)
def texture (i j:Stroke):ℂ:= (Fintype.card G.ColorIndex:ℂ)⁻¹ * (∑ c:G.ColorIndex,x (i,c)*x (j,c))
def fur : Symmetric (Fiber G) where
    cov i j:= if j.2=i.2 then texture x i.1 j.1 else 0
    symm i j:= by by_cases h:j.2=i.2; · simp only [h,↓reduceIte]; apply congr_arg ((Fintype.card G.ColorIndex:ℂ)⁻¹ * ·); exact Finset.sum_congr rfl fun i hi => mul_comm ..
                  simp only [if_neg h, if_neg (Ne.symm h)]
lemma foliage (c:G.ColorIndex) (hx:p∈Paths G): Next.Rank.Normal.blend (fur x) 0 (prim v p)= aeval x (prim v p):= by
   let A:= Next.Rank.Normal.blend (fur x) 0; let B:= prim (G:=G) v; let Q:= LinearMap.ker (A.comp B.toLinearMap- (aeval x).toLinearMap.comp B.toLinearMap);
   have ha(l r:Fiber G): A (X l * X r)=(fur x).cov l r:= by unfold A; rw [blend_components, feeds,show milk (fur x) (X r)=X r by nth_rw 1 [← mul_one (X _)]; rw [feeds];simp]; simp
   have hw: Paths G ≤ Q:= by
       apply sup_le
       · apply Submodule.span_le.mpr; rintro i hi; obtain rfl:i=(1:WickPol G):=hi; change A (B 1) - (aeval x) (B 1)=0; simp [A]
       apply Submodule.span_le.mpr; rintro _ ⟨i,j,rfl⟩; apply sub_eq_zero.mpr;
       let f(l:Style)(c:G.ColorIndex):= ((v,l),c); have hw(l:Style)(c:G.ColorIndex): prim v (bit (ax l.1 l.2) c)= X (f l c):= by unfold prim Rank.pluck; rw [AlgHom.comp_apply, paint_bit,penned]; exact rename_X ..
       change A (prim v _)= aeval x (prim v _); simp_rw [team,map_sum, map_mul (prim v),hw,ha, map_mul,aeval_X]; simp only [fur,↓reduceIte,f,texture, Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; rw [mul_inv_cancel_left₀]; haveI : Nonempty G.ColorIndex:=⟨c⟩; exact_mod_cast Fintype.card_pos (α:=G.ColorIndex) |>.ne' -- syntax
   exact sub_eq_zero.mp (hw hx)
lemma unpictures (c:G.ColorIndex)(hx:p∈Paths G)(hs:∃ s:Finset E4,Fits (s:Set E4) (prim v p)∧ Silent c (prim v p) s) : p=0:= by
   obtain ⟨s,he,hS⟩:=hs; have hh: prim v p=0:= MvPolynomial.funext (fun x:Fiber G→ℂ=> ((foliage x p v c hx).symm.trans (converted c (fur x) ⟨texture x,by intro i; funext j; unfold fur; split_ifs<;> first|rfl|simp_all⟩ he hS))|>.trans (map_zero (aeval x)).symm)
   apply full_poly; rw [map_zero]; apply rename_injective (R:=ℂ) (f:=Rank.pin v) (show Injective (Rank.pin (G:=G) v) from fun a b h=> Prod.ext (Prod.mk.inj (Prod.mk.inj h|>.1)|>.2) (Prod.mk.inj h|>.2)); rw [map_zero]; exact hh
set_option quotPrecheck false
local notation "K"=> Pert.Position.E F 6
local notation "L"=> lower F 4 6
-- tomography use station6 even p and sectors lower coexist
structure Splot (F:Labels.Frames G) where
   n:ℕ
   i:Fin n
   probes : Fin n→ Pert.Position.E F 6
   h : ∀ j, j≠i→ probes j∈ lower F 4 6
   test: Test n
namespace Splot
def sit (x:Pert.Position.E F 6)(p:Splot F):Section F 6:=⟨p.n,Function.update p.probes p.i x, p.test⟩
def result (p:Splot F)(Y:Bank F 6): Module.Dual ℂ (Pert.Position.E F 6) where
    toFun x:= lookie F (sit F x p) Y
    map_add' x y:= (Y p.n p.test).map_update_add ..
    map_smul' a x:= (Y p.n p.test).map_update_smul ..
lemma room (v: K)(hr:∀s:Splot F,result F s (pureBank F 6) v=0)(x:Points n)(hx:x∈conf n)(f:Fin n→ Pert.Position.E F 6)(i:Fin n)(he:f i=v)(hp:∀ j,j≠i→ f j∈L) : visible F 6 x f=0:= by
   apply ((Test.weak_null (visible_cont F 6 f)).1 ?_) hx; intro t; have hh:= hr ⟨n,i,f,hp,t⟩; change t.applyTo (fun x=> visible F 6 x (Function.update f i v))=0 at hh; simpa only [← he,Function.update_eq_self] using hh
end Splot
lemma gory (x: K)(c:G.ColorIndex)(hc:∀ p:Splot F,Splot.result F p (pureBank F 6) x=0): Silent c (prim (0:E4) (address F 6 x)) {0}:= by
    have he (n:ℕ)(v:Points n)(hv:v∈conf n)(f:Fin n→ Pert.Position.E F 6)(i:Fin n)(h:f i=x)(hf:∀j,j≠i→ f j∈L): Silent c (Rank.fuse v (address F 6 ∘ f)) (look v):= by
       intro W hw; induction W generalizing n with
       | nil=> rw [clothe,List.map_nil,List.prod_nil,one_mul]; exact (wick_prim c hv _).symm.trans ((visible_eq F f v).symm.trans (Splot.room F x hc v hv f i h hf))
       | cons a W IH=>
         obtain ⟨hu,hy,hw⟩:= (adm_cons ..).mp hw; let y:=Points.cons a.1 v; let b:= up F (show 4≤6 by omega) ((fields F 4).symm ⟨team G a.2 a.2,team_label _ _ (by omega)⟩); let g:= Fin.cons (α:=fun _:Fin (n+1)=>Pert.Position.E F 6) b f; have h₁:y∈conf (n+1):= by
            change Injective (Fin.cons (α:=fun _ : Fin (n+1)=> E4) a.1 v.ofLp); exact Fin.cons_injective_iff.mpr ⟨fun ⟨i,hi⟩=> hu (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩),hv⟩
         have ht(j:Fin (n+1)) : j≠ i.succ → g j∈L:= by refine Fin.cases ?_ (fun j he=> by unfold g; simp only [Fin.cons_succ]; exact hf _ (fun hy=>he (congr_arg Fin.succ hy))) j; intro; rw [up_pre F (by omega)];exact ⟨_,rfl⟩
         have hg: address F 6 b=team G a.2 a.2:= by unfold b; rw [show ∀ x,address F 6 (up F (show 4≤6 by omega) x)=_ from fun x=> address_rise F 6 (by omega) x]; exact congr_arg Subtype.val ((fields F 4).apply_symm_apply _)
         have he:= IH _ y h₁ g i.succ (by simp [g,h]) ht (by unfold y;rw [look_step]; exact ⟨hw.1,Finset.disjoint_insert_right.mpr ⟨hy,hw.2⟩⟩)
         rw [show (address F 6 ∘ g)=Fin.cons (address F 6 b) (address F 6∘ f) from funext (fun i=> Fin.cases rfl (fun a=> by unfold g; rw [comp_apply,Fin.cons_succ,Fin.cons_succ];rfl) i),fuse_cons,hg] at he
         rw [clothe_cons, patch_eq a a.2,mul_comm (prim a.1 _),mul_assoc]; exact he
    let y: Points 1:= points (fun _=> 0); have hx:y∈conf 1:= fun i j h=> Subsingleton.elim i j; have hw: Rank.look y={0}:=by unfold look; ext i; simp [y,points]
    have hf:= he 1 y hx (fun _=>x) 0 rfl (fun i hp=> (hp (Subsingleton.elim ..)).elim); rw [hw,Rank.fuse, Fin.prod_univ_one] at hf; exact hf
include h in
lemma even_unique (x: K)(hx:par F 6 x=x)(hc:∀ p:Splot F,Splot.result F p (pureBank F 6) x=0): x=0:= by
    let c:= coreColor h; let p:= address F 6 x; let y:Points 1:= points (fun _=>0); have hp: Fits (({(0:E4)}:Finset E4):Set E4) (prim (0:E4) p):= by
       have hh:= fuse_fits y (fun _=>p); rw [show look y={(0:E4)} from (by ext i; simp [look,y,points]),fuse, Fin.prod_univ_one] at hh; exact hh -- coercion singleton?
    apply address_inj F 6; rw [map_zero]; exact unpictures p 0 c (forests h p (address_in F 6 x) ((address_par F x).symm.trans (congr_arg _ hx))) ⟨{0},hp,gory F x c hc⟩
end YM.PositionX.Tri
