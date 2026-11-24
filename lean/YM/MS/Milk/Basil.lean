import YM.MS.Milk.Honey
/-! submodule of superflat exponent polynomials. Used only for comparison at *fixed positions*, 
pointwise norms no restrictions at sphere. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Milk
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Analysis Submodule InnerProductSpace City Next.Rank Next.Rank.Normal Theater Drops Maxwell
open Tensor (diagonal)
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {A X:Type}{G:Gauge}{n d r:ℕ}{s:ℝ}{f:ℝ→ℂ}
local notation "Φκ"=> field (P:=QP) ( Landau.parity ( C:=G.ColorIndex ) ( A:=Axis ) )
local infix:70 " ⋆ "=> product (field Landau.parity)
variable {W E I:Type}{L:Album X G}{U V P Q:ℝ→Law G}{D:Law G}{g:X→Normal.poly X}
variable {u v:ℝ→ Normal.Symmetric X}
def LeaseL (G:Gauge): Submodule ℂ ( ℝ→Law G ):={ carrier:=Giant, zero_mem':= Giant.zero,add_mem':=Giant.add, smul_mem' c _ h:= Giant.smul h c }
def road (G:Gauge): Submodule ℂ ( ℝ→Law G ):={ carrier:=Clean, zero_mem':= Clean.zero,add_mem':=Clean.add, smul_mem' c _ h:= Clean.smul h c }
lemma giant_c (A:Law G): Giant (fun _=> A):= fun _=> tallC _
abbrev flick (b:Bool): (ℝ→ℂ)→Prop:= if b then Sharp0 else Tall0
lemma routed (h:Clean U): Giant U:= fun w=> tall0 ( h w )
lemma τleft (u:X) : u=u:=rfl -- remove
lemma track_ξ (b c: Bool)(H:∀ f g:ℝ→ℂ,flick b f→flick c g→ flick (b||c) (f*g))(hp:∀ w,flick b (fun t:ℝ=> U t w))(hx:∀ w,flick c (fun t:ℝ=> V t w)) : ∀ w,flick (b||c) (fun t:ℝ=> trunk U V t w ) := by
    let d:=(b||c); have he(f g:ℝ→ℂ)(hp:flick d f)(ht:flick d g): flick d ( f+g ):= by
       by_cases hs:d=true; · simp only [flick,hs, ↓reduceIte ] at *; exact fun i=> ( hp i ).add ( ht i )
       simp only [flick,hs,↓reduceIte] at hp ht ⊢; exact sunny0 hp ht
    have hx' (f:ℝ→ℂ)(c:ℂ)(h:flick d f): flick d (c • f):= by by_cases hv:d=true; simp only [flick,hv, ↓reduceIte ] at h ⊢; exact fun i=> (h i).const_mul_left c; simp only [flick,hv, ↓reduceIte] at h ⊢; exact h.imp fun _ h=> h.const_mul_left c
    intro w; suffices hv : ∀ F:ℝ→ Shared (Lane4 G) ℂ,(∀ l r,flick d (fun t=> F t l r))→flick d (fun x=> scatter Φκ w (F x)) from ?_; · simp_rw [trunk,scattered]; exact hv _ fun a b=> H _ _ (hp a) (hx b)
    induction w with| nil=> exact fun _ h=> h _ _| cons i w ih=> exact fun F h=>ih _ (fun a b=> he _ _ (h (i::a) b) (hx' _ (cross (Φκ i) (degree Φκ a)) (h a (i::b))))
lemma trunk_G (hp:Giant U)(he:Giant V): Giant (trunk U V):= track_ξ false false (fun _ _=> shiver ) hp he
lemma trunk_C (hp:Giant U)(he:Clean V): Clean ( trunk U V ):= track_ξ false true (fun _ _=> solar0 ) hp he
lemma trunk_C' (hp:Clean U)(he:Giant V): Clean ( trunk U V ):= track_ξ true false (fun _ _ h hv=> solar1 hv h ) hp he
abbrev giantΦ (u:ℝ→ Normal.Symmetric X): Prop:=∀ i j,Tall0 (fun t=>(u t).cov i j)
abbrev cleanΦ (u v:ℝ→ Normal.Symmetric X): Prop:= ∀ i j,Sharp0 (fun t=> (u t).cov i j-( v t ).cov i j )
abbrev ArcL (L:Album X G)(v:ℝ→Normal.Symmetric X): Normal.poly X→ₗ[ℂ] OM (Lane4 G):= LinearMap.pi fun s=> Tint L ( v s )
lemma giant_H [DecidableEq A](hp:giantΦ u)(s:Finset A)(d:A→X): Giant ( arc (glyphs d s) L u ):= by
    induction s using Finset.strongInduction with| H s ih=>
       obtain h|⟨p,h⟩:=s.eq_empty_or_nonempty; · subst s; rw [ show arc _ _ _ =(fun _=> coin 1) from funext fun i=>by unfold arc Normal.glyphs; rw [Finset.prod_empty,step0] ]; exact giant_c _
       have hv : s.erase p ⊂ s:= Finset.erase_ssubset h; let T(v:Finset A) := arc (glyphs d v) L u; rw [ show arc _ L u=trunk (fun _=>L.H (d p)) ( T (s.erase p) ) + ∑ i∈s.erase p, Meat (fun t=>( u t ).cov ( d p ) ( d i ) ) (T (( s.erase p ).erase i)) from ?_]; exact Giant.add ( trunk_G (giant_c _) (ih _ hv) ) (gPack (fun i _=> giant_p (ih _ (Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset ..) hv)) (hp _ _)))
       funext i; rw [Pi.add_apply,Finset.sum_apply]; nth_rw 1 [ ← insert_erase h ]; exact step_k L d ( Finset.notMem_erase p s )
lemma aim_G (L:Album X G)(v: Normal.poly X)(hp:giantΦ u) : arc v L u∈ LeaseL G:= by
  classical
  refine (show v∈ (LeaseL G).comap (ArcL L u) from axis_v ( (LeaseL G).comap (ArcL L u) ) (fun s=> (?_ : Gaze s∈ (LeaseL G).comap (ArcL L u))) v); exact giant_H hp s Prod.snd
lemma subtract_c (h:Clean (U-P))(hp:Clean (V-Q))(he:Giant U)(hv:Giant Q): Clean (trunk U V-trunk P Q):= by rw [show trunk U V-trunk P Q=trunk U ( V-Q )+trunk ( U-P ) Q from ?_ ]; exact Clean.add ( trunk_C he hp ) ( trunk_C' h hv ); funext s; simp_rw [ Pi.sub_apply, Pi.add_apply,trunk,Pi.sub_apply,map_sub, LinearMap.sub_apply ]; abel -- order
lemma meat_2 (f g:ℝ→ℂ)(h:Tall0 f)(hp:Sharp0 (f-g))(hv:Clean (U-V))(ht:Giant V) : Clean ( Meat f U-Meat g V ):= by rw [ show Meat f U-Meat g V=Meat f ( U-V )+ Meat ( f-g ) V from ?_ ]; exact Clean.add ( clean_p hv h ) ( clean_p' ht hp ); funext x; change f x • U x- g x • V x=f x • ( U x-V x )+(f x-g x) • V x; module
lemma summitμ (hp:giantΦ u)(he:giantΦ v)(hx:cleanΦ u v) (T:Normal.poly X) : Clean ( arc T L u- arc T L v ):= by
    classical
    let U:= road G; have he1 (s:Finset (deck0 X)): Clean ( arc (Gaze s) L u- arc (Gaze s) L v ):= by
       induction s using Finset.strongInduction with| H s ih=>
          obtain h|⟨p,h⟩:= s.eq_empty_or_nonempty; · subst s; rw [ show arc (Gaze ∅) L u=arc ( Gaze ∅ ) L v from funext fun i=>by simp only [Gaze,arc,Normal.glyphs,Finset.prod_empty,step0], sub_self ]; exact Clean.zero
          let a:= s.erase p; have hv:a ⊂ s:=erase_ssubset h; let J(t:ℝ→Normal.Symmetric X)(s:Finset (deck0 X)):=arc ( Gaze s ) L t; let P:= fun (_:ℝ)=> L.H p.2; let A (t:ℝ→ Normal.Symmetric X)(k:deck0 X):= Meat (fun i=>( t i ).cov p.2 k.2) ( arc ( Gaze (a.erase k) ) L t ); have hh (t:ℝ→ Normal.Symmetric X): arc (Gaze s) L t=trunk P ( J t a )+ ∑ i∈ a,A t i := by funext i; rw [Pi.add_apply,Finset.sum_apply ]; nth_rw 1 [ ← insert_erase h ]; exact step_k L Prod.snd (Finset.notMem_erase p s ) -- sum_apply inside addition misorder
          rw [hh u,hh v,add_sub_add_comm, ← Finset.sum_sub_distrib ]; exact Clean.add (subtract_c ( by rw [sub_self]; exact Clean.zero ) ( ih a hv ) (giant_c _) (aim_G L _ he)) ( cPack (fun i _=>meat_2 _ _ (hp _ _) (hx _ _) (ih _ ( Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset ..) hv )) (aim_G L _ he) ) )
    refine ( show T∈ U.comap ( ArcL L u - ArcL L v ) from axis_v _ (fun a=> ?_) T ); exact he1 a
end YM.MS.Milk
