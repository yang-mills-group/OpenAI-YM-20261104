import YM.MS.Lifting.PureMark
/-!
# Any real local jet primitive has a Wilson graded symbol

Loose letters realized by noncovariant differences; inserted with the quantum BV
 operator by fit. Mark words actual Grassmann ordered. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Lifting
open Function Filter Set Finset Plane Koszul Color Real Momentum Wire Tensor Book
open Landau Detect Detect.Mark Cylinder Lab Taylor Native Draft Paint Sew Native.Chart Orient Wilsonian Studio
open Tone Tone.Frame Lattice Local Local.BV Submodule
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{F S:Dot G Cover}{v u:ℤ}{H K:Law G}{n q:ℕ}
-- cost charged, pure homogeneous

namespace Ghost

def ps (a:Branch G Axis) (x:List Axis): Dot G Cover := match x with
   | []=> Cylinder.single (a,0)
   | k::i=> (Lab.Shift (step k) (ps a i)) - ps a i
lemma ps_ghost (a:Branch G Axis)(x:List Axis): Tuned (ps a x) (ghostNo a):= by induction x with| nil=> exact Tune.lit (a,0)| cons k x ih=> exact (ih.move (fun i=> step k+i)).sub ih
lemma ps_rank (a:Branch G Axis)(x:List Axis): rank 1 (ps a x).val:= by induction x with| nil=> exact Rails.letter (a, (0:Cover))| cons k x ih=> exact (Rails.ferry (w:=fun _:LightMode G Cover=>1) (post (fun i:Cover=>step k+i)) (fun _=>rfl) (ps a x) ih).sub ih -- fix
lemma ps_c (a:Atom Axis)(x:List Axis)(c:Conn G)(T:G.El): dye T (ps (a,c) x)=∑ j:CI G, wc T j c • ps (a,j) x := by
    induction x with
    | nil=> exact stroke (stripe G Cover) T (a, (0:Cover)) c
    | cons k x ih=> simp only [ps,map_sub,Lab.Shift, ← painting,ih,map_sum,map_smul,smul_sub,Finset.sum_sub_distrib]
lemma ps_here (a b:Branch G Axis)(x:List Axis)(p:QP): Rest (fun t:ℝ=> run (ps b x) [(a,t • p)]) (wfield b+x.length-wfield a) (loose b (deriv x) (a,p)):= by
    induction x with
    | nil=> simp_rw [ps,pulse]; by_cases he:a=b; · subst b; simp only [loose,LinearMap.coe_mk,AddHom.coe_mk,if_true,pw,der_nil,List.length_nil,Nat.cast_zero, add_zero,sub_self]; exact Rest.level (bankForm ..) (by simp)
            simp only [loose, LinearMap.coe_mk,AddHom.coe_mk,he,↓reduceIte]; have hx p: paywave (a,p) (b,0)=0:= Classical.byContradiction (fun h=>he (in_light _ _ h)); simp_rw [hx]; exact Rest.zero _
    | cons i x ih=>
       have hz p : run (ps b (i::x)) [(a,p)]=(bill p (embed (step i))-1)*run (ps b x) [(a,p)]:= by rw [ps,map_sub,Pi.sub_apply,movement]; simp [net,sub_mul]
       simp_rw [hz]; convert! (stepForm p i).mul ih using 1; simp; omega; by_cases ha:a=b <;> simp [loose,ha,der_add]

def symbol (n:ℕ) (f:Fin n→ Letter)(c:Grid G n): Dot G Cover := prodS ℂ (couple DotFlip) (Cylinder.piece 1) n (fun i=>ps ((f i).face,c i) (f i).jets)
lemma value_verb (f:Fin (n+1)→ Letter)(c:Grid G (n+1)): symbol (n+1) f c= couple DotFlip (ps ((f 0).face,c 0) (f 0).jets) (symbol n (f ∘ Fin.succ) (c ∘ Fin.succ)):= rfl
lemma symbol_c (n:ℕ)(f:Fin n→ Letter)(c:Grid G n) (T:G.El): dye T (symbol n f c)=∑ j:Grid G n,(ink T j c:ℂ) • symbol n f j:= by
    let R i (c:Conn G):= ps ((f i).face,c) (f i).jets; have he i: dye T (R i (c i))=∑ j:CI G,wc T j (c i) • R i j:= ps_c ..; have hh : dye T (piece 1) = (piece (A:=LightMode G Cover) 1):= Subtype.ext (coin_turn ..);
    change dye T (prodS ℂ _ _ _ (fun i=>R i (c i)))=_; rw [prod_color (dye T) _ _ _ _ hh (fun i j=> pigment T i j)]; simp_rw [Function.comp_def,he]; exact color_expand (couple DotFlip) _ n R T c
lemma symbolT (n:ℕ)(f:Fin n→ Letter)(c:Grid G n): Tuned (symbol n f c) (∑ i,(f i).charge):= by induction n with| zero=> rw [Fin.sum_univ_zero]; exact mon_T (f:=fun i=>i.elim0) (d:=idRail) (0:Cover) 0 c| succ n ih=>rw [Fin.sum_univ_succ]; exact (ps_ghost ((f 0).face,c 0) (f 0).jets).pair (ih ..)
lemma symbol_n (n:ℕ)(f:Fin n→Letter)(u:Grid G n): Book.rank n (symbol n f u).val:= by induction n with| zero=> exact Rails.coin _| succ n ih=> push_cast; rw [add_comm (n:ℤ)]; exact (ps_rank ((f 0).face,u 0) (f 0).jets).product (ih (f ∘ Fin.succ) (u ∘ Fin.succ))
lemma in_rank {J:Type}{v:ℤ}{f:Raw J ℂ}(h:rank v f): From f v:= fun l he=> h l (by rw [mod_int]; omega)
lemma symbol_fit (n:ℕ)(f:Fin n→Letter)(u:Grid G n): Fits (symbol n f u) (family n (Letter.mark ∘ f) u) n (∑ i,((f i).edge+(f i).charge)) false:= by
    induction n with
    | zero=> rw [Fin.sum_univ_zero]; exact Fits.unit
    | succ n ih=>
       let T := f 0; let B:= (T.face, u 0)
       have hz : Fits (ps B T.jets) (Koszul.mono (T.mark (u 0))) 1 (T.edge+T.charge) false:=by rw [show T.edge+T.charge=wfield B+T.jets.length from by unfold Letter.edge; rw [sub_add_cancel]; rfl]; exact Fits.rank1 _ (fun a p=>ps_here a B T.jets p)
       rw [Fin.sum_univ_succ]; have ht:= hz.take (ih (f∘Fin.succ) (u ∘ Fin.succ)) (in_rank (ps_rank B T.jets)) (in_rank (symbol_n n _ _)); rw [add_comm 1 n] at ht; exact ht

def soul (n:ℕ)(f:Fin n→ Letter)(u:Grid G n): Dot G Cover:= ∑ i:Grid G n, (group G i u:ℂ) • symbol n f i
lemma soulC (n:ℕ)(f:Fin n→Letter)(u:Grid G n): Colorless (soul n f u):= fun i=> cash (P:=dye i) _ i (fun a=> symbol_c n f a i) _
lemma soulP (n:ℕ)(f:Fin n→ Letter)(u:Grid G n): Tuned (soul n f u) (∑ i,(f i).charge):= Tune.sum _ fun i _=> (symbolT n f i).cash _ (by simp)
lemma soul_rank (n:ℕ)(f:Fin n→Letter)(u:Grid G n): Book.rank n (soul n f u).val:= by rw [soul,sum_stack]; exact Rails.sum _ (fun i _=> (symbol_n n f i).smul _)
lemma soul_fit (n:ℕ)(f:Fin n→Letter)(u: Grid G n): Fits (soul n f u) (breeze (family n (Letter.mark ∘ f)) u) n (∑ i,((f i).edge+(f i).charge)) false:= Fits.sum _ (fun i _=> (symbol_fit n f i).smul _)
-- real vector space.
structure Vocal (F:Dot G Cover)(v:ℤ)(n:ℕ): Prop where
   charge : Tuned F v
   level : Book.rank n F.val
   lit : Colorless F
lemma voice (h:H∈ Physical.Lease G v n u) : ∃ F:Dot G Cover, Vocal F u n∧ Fits F H n v false:= by
    refine span_induction (p:=fun H _=>∃ F:Dot G Cover,Vocal F u n ∧ Fits F H n v false) ?_ ⟨0,⟨Tune.zero,Rails.zero,fun i=>map_zero _⟩,Fits.zero _⟩ ?_ ?_ (syntaxL h)
    · rintro j ⟨x,w,h,h1,rfl⟩; subst u; refine ⟨_,⟨soulP n x w,soul_rank n x w,soulC n x w⟩,?_⟩; let z:= soul_fit n x w; rw [Finset.sum_add_distrib,h,sub_add_cancel] at z; exact z
    · rintro v w hv hw ⟨F,hF,he⟩ ⟨H,hH,ht⟩; exact ⟨F+H,⟨hF.charge.add hH.charge,hF.level.add hH.level,hF.lit.add hH.lit⟩, he.add ht⟩
    rintro x y hy ⟨F,hv,hf⟩; refine ⟨(x:ℂ) • F,⟨hv.charge.cash _ (by simp),hv.level.smul _,hv.lit.smul _⟩,hf.smul (x:ℂ)⟩
end Ghost
end YM.MS.Lifting
