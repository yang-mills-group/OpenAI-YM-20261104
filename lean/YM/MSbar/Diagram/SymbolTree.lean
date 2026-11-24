import YM.MSbar.Diagram.Tag
/-! Spliced Ward operations read integer tensor positions on bottom field order.
Homogeneity needs support at cut (here) and retains all order/dimensions. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Diagram
open Super Domain Domain.DR Loops Dim Symbol Function Set Filter MeasureTheory
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {C:Type} {I:Finset C} {W:Edition C} {m k j n:ℕ} {U:Set ℂ}
  {f g : Functionals C} {L P A:Links C} {d e l : Bit}
namespace Tree
-- neutral-independent packed piece
def pick (W:Edition C)(d:Bit)(L:Links C)(f g:Functionals C)(m:ℕ)(a b:Token C m)(x y:Words C m) := letter W d L m m a b (-channel x)* (f m m ((a,-channel x)::x)*g m m ((b,channel x)::y))
def sow (W:Edition C)(d:Bit)(L:Links C)(f g:Functionals C)(m:ℕ) : Words C m → Words C m→ℂ := ∑ i∈W.members m,∑ b∈W.members m,pick W d L f g m i b
lemma split_open {w:Words C m}(q:Letter C m→Bit){T:Type}{I:Finset T}{F:T→Words C m→Words C m→ℂ}: split q (∑ i∈I,F i) w=∑ i∈I,split q (F i) w:=by rw [split_sum,Finset.sum_apply]
lemma same (W:Edition C)(d:Bit)(x:Words C m): split (lift (W.binary _)) (sow W d L f g m) x= splice W d L f g m m x:=by
   have hh(a b:C)(u v: Words C m): charge W d a b L f g m m (u,v)= ∑ r∈ index (W.vector a) m,∑ s∈ index (W.vector b) m, pick W d L f g m (a,r) (b,s) u v:=discrete ..
   have he:sow W d L f g m=∑ a∈W.active,∑ b∈ W.active,(fun u v=> charge W d a b L f g m m (u,v)):=by
      ext1 u; ext1 v; unfold sow; simp_rw [Finset.sum_apply, Edition.sum,hh]; refine Finset.sum_congr rfl fun x hx=> Finset.sum_comm
   rw [he]; simp_rw [split_open]; rfl
lemma within (W:Edition C)(d:Bit): splice W d L f g m m= tree (W.binary m) (W.members m) d (L m m) (f m m) (g m m):=by
   let I:= W.members m; let c(i):= W.binary m i; let u:= L (↑m) m; let X:= f (↑m) m; let Y:= g (↑m) m
   have he : sow W d L f g m= ∑ a∈I,∑ b∈I,Loops.price c d a b u X Y:=by
     ext1 w; funext y; let t:=channel w; let h (a b) := X ((a,-t)::w) * Y ((b,t)::y); let S(a b:Token C m):ℂ:= sign (c b) (c a+d)/2 * u a b (-t) * h a b;let U(a b):ℂ := sign (c b) d/2 * u b a t*h a b
     have hL(a b:Token C m): pick W d L f g m a b w y=S a b+ U a b:=by unfold pick letter S U; rw [neg_neg,add_mul]; rfl
     have hU(a b):Loops.price c d a b u X Y w y= S a b+U b a:=by unfold Loops.price S U h t; ring
     unfold sow; simp only [Finset.sum_apply,hL,hU,Finset.sum_add_distrib]; exact congr_arg₂ (·+·) rfl Finset.sum_comm
   funext w; rw [← same,he]; simp_rw [split_open]; rfl
end Tree
lemma splice_at (W:Edition C)(d:Bit){z:ℂ}{K:Links C}{h i:Functionals C}(he:L z=K z)(ht:f z=h z)(hk:g z=i z): splice W d L f g z=splice W d K h i z:=by
   have H (a b:C): Tree.charge W d a b L f g z=Tree.charge W d a b K h i z:=by
      unfold Tree.charge; congr! 1; unfold Tree.root Tree.letter; rw [he, ht, hk]
   funext m u; unfold splice walk; simp_rw [H]
variable (hf:Full U k W d f) (hg:Full U n W e g) (hL:Pilot U j W l L) {K:ℝ} (hB:Band U L K) (hz:(m:ℂ)∈U)
include hf hg hL hB hz
lemma grades : Homogeneous (lift (W.binary m)) (l+d+e) (splice W d L f g m m):=by
   rw [Tree.within]; obtain ⟨s⟩:= Edition.lattice m; exact Supported.wears s (Domain.supported hL hB hz) (hL.pace hz) (fares hf.licensed hz) (hf.quiet _ hz _) (fares hg.licensed hz) (hg.quiet _ hz _) (hf.span _ hz _) (hg.span _ hz _)
lemma polar_splice : Polar W (splice W d L f g m m):=by
   refine color (grades hf hg hL hB hz) (fun i p v=> ?_)
   let I:= W.members m; let q:= lift (M:=Mom m) (W.binary m); let Q:= Tree.sow W d L f g m; let c(t:Hat m): Letter C m:= ((i,t),p)
   let r(x y:Words C m):ℂ:=0 -- dummy
   simp_rw [← Tree.same,split_next]; apply Dim.One.add; unfold Tree.sow
   · refine one_split q (fun t x y=> Q (c t :: x) y) v ?_; intro x y H
     unfold Q Tree.sow; simp_rw [Finset.sum_apply]; refine one_sum (I:=I) (fun a ha=> one_sum I fun b hb=> ?_)
     let s :=p+channel x; let C:= g (↑m) m ((b,s)::y); let B:= Tree.letter W d L m m a b (-s); unfold Tree.pick; simp only [channel_cons];
     let V:=fun t=>f (↑m) m ((a,-s)::c t::x)
     have h : Dim.One (W.vector i) V:=hf.colors _ hz m i p [(a,-s)] x
     change Dim.One _ (fun t=> B*(V t*C)); rw [show (fun t=> _ )=(B*C) • V from ?_]; rotate_left; exact funext fun t=> Eq.trans (mul_assoc ..|>.symm) (mul_right_comm ..); exact h.scale _
   refine one_split q (fun t x y=> sign (W.parity i) (oddity q x)*Q x (c t::y)) v ?_
   intro x y hh; refine Dim.One.scale (sign (W.parity i) (oddity q x)) ?_; unfold Q Tree.sow; simp_rw [Finset.sum_apply]; refine one_sum I fun a ha=> one_sum I fun b hb=> ?_
   unfold Tree.pick; let B:= f (↑m) m ((a,-channel x)::x);
   exact ((hg.colors _ hz m i p [(b,channel x)] y).scale B).scale _
omit hz in
theorem spin_splice : Full U (j+(k+n)) W (l+d+e) (splice W d L f g):=by
    have h : ∀ (z:ℂ), z∈U→∀ m:ℕ, Polar W (splice W d L f g z m) ∧ Homogeneous (lift (W.binary m)) (l+d+e) (splice W d L f g z m):=by
       intro z hz m; have H:= splice_total (hf.freeze hz) (hg.freeze hz) (hL.freeze hz); have hp:Band univ (fun _=> L z) K:= fun _ _=> hB _ hz
       rw [splice_at (L:=L) (f:=f) (g:=g) W d (K:=fun _=> L z) (h:=fun _=> f z) (i:=fun _=> g z) rfl rfl rfl]; exact ⟨H.choose_color W (fun i=> polar_splice (hf.freeze hz) (hg.freeze hz) (hL.freeze hz) hp (m:=i) (mem_univ _)) z,H.choose_hom W (fun i=> grades (hf.freeze hz) (hg.freeze hz) (hL.freeze hz) hp (m:=i) (mem_univ _)) z⟩
    have he:= splice_total hf hg hL; exact ⟨he.safe,he.quiet,fun z hz n=> (h z hz n).1,fun z hz n=> (h z hz n).2⟩
end YM.MSbar.Diagram
