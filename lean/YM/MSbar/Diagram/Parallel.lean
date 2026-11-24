import YM.MSbar.Diagram.Readers
/-! No artificial factors of ζ in tree Wick operations including hat-vector vertices.
Needed to distinguish different internal-loop weights of counterterms. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Diagram.Parallel
open Super Domain Loops Dim Symbol Function Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {C:Type} {W:Edition C} {P:Sites C} {k l d:Bit} {m n:ℕ} {f g: Vertex C} (hf: Live W k f) (hg: Live W l g)
include hf
lemma blank (x:C)(hx: W.vector x)(p: Mom m)(t:Words C m): f (m+1) (((x,Trace.step m),taxi (up m) p)::above (line C) t)=0 :=by
    let s:Move m (m+1):= up m; let w := Trace.step m; obtain ⟨U,G,h⟩:= perp_turn s (show ‖w‖=‖-w‖ by simp) (fun x=> by unfold s w; rw [inner_neg_right,Trace.orth]; simp)
    let F(x':Hat (m+1)):= f (m+1) (((x,x'),taxi s p)::above (line C) t); obtain he:= hf.colors 0 (mem_univ _) (m+1) x (taxi s p) [] (above (line C) t); rw [Dim.One,if_pos hx] at he; obtain ⟨X,hX⟩:=he; change ∀ x,F x=X x at hX
    have L:U.toLinearIsometry.comp s=s:= DFunLike.ext _ _ h
    have H:F (-w)=F w:=by
        have hp:=(hf.licensed.natural 0 (mem_univ _)) U.toLinearIsometry (((x,w),taxi s p)::above (line C) t); unfold F
        change f (m+1) ((line C).move U.toLinearIsometry _) = f (m+1) _ at hp; rw [work,← (line C).together, show up m=s from rfl,L] at hp -- above abbrev
        simpa only [aleph,LinearIsometryEquiv.coe_toLinearIsometry,h _,G] using hp
    simp_rw [hX,map_neg] at H; have hh:= neg_eq_self.mp H; exact (hX w).trans hh -- char zero
omit hf in
lemma no_coeff {Y:ℕ→Type} (S: Motion Y){p:Prop}(F:∀ m,Y m × Hat m→ℂ)(z:ℂ)(x:Y m) (hv:p→F (m+1) (above S x,Trace.step m)=0): metric S p z F m x= ∑ i∈index p m,F _ (x,i):=by unfold metric; split_ifs with h; rw [show (grow m) (0,axis)=Trace.step m from rfl,show F _ _=0 from hv h]; ring; simp
include hg
lemma no_rank (x:Twins C m)(a b:C) (z:ℂ): Tree.charge W k a b (liftS P) (liftV f) (liftV g) z m x= Tree.charge W k a b (liftS P) (liftV f) (liftV g) m m x:=by
    let S:=(pack C).toMotion; let F:= Tree.root W k a b (liftS P) (liftV f) (liftV g) z; unfold Tree.charge; rw [Domain.discrete]; unfold duplex; change metric S (W.vector a) _ (metric (S.prod vectors) (W.vector b) _ F) m x=_
    have he (i:ℕ)(t:Twins C i × Hat i): metric (S.prod vectors) (W.vector b) z F i t= ∑ y∈ index (W.vector b) i,F i (t,y):= by
       apply no_coeff; intro h; unfold F Tree.root; simp only; apply mul_eq_zero_of_right; apply mul_eq_zero_of_right; unfold liftV; change g _ (((b,_),channel (above (line C) _)):: _) = 0; unfold above; rw [quiet_move]; exact blank hg b h ..
    rw [no_coeff]; simp_rw [he]; rfl
    intro h; rw [he]; apply Finset.sum_eq_zero; intro v hv; unfold F Tree.root; apply mul_eq_zero_of_right; apply mul_eq_zero_of_left; unfold liftV; change f _ (((a,_),-channel (above (line C) _))::_)=0; unfold above; rw [quiet_move,← map_neg]; exact blank hf a h ..
lemma tree (z:ℂ): traceT W k z P f g m= Loops.tree (W.binary m) (W.members m) k (P m) (f m) (g m):=by
   rw [show Loops.tree _ _ _ _ _ _=traceT W k (m:ℂ) P f g m from Tree.within W k|>.symm]; funext x; unfold traceT splice walk; apply Finset.sum_congr rfl; intro a _; refine Finset.sum_congr rfl fun b hb=> ?_; exact split_change _ fun _ _ _=> no_rank hf hg _ a b z
lemma sameT (x y:ℂ): traceT W k x P f g= traceT W k y P f g := funext fun m=> Eq.trans (tree hf hg x) (Eq.symm (tree hf hg y))
omit hg
open Arrow
lemma sameR (x y:ℂ): traceR W x P f= traceR W y P f:=by
    let V (z:ℂ) := Arrow.look W (liftS P) (liftV f) z
    let L(c:C)(z:ℂ):=metric (pack C).toMotion (W.vector c) z (read c (liftS P) (liftV f) z)
    have he (m:ℕ)(t:Twins C m)(z:ℂ)(c:C): L c z m t= ∑ y∈ index (W.vector c) m,read c (liftS P) (liftV f) x m (t,y):= by
       apply no_coeff; intro h; rcases t with ⟨_|⟨a,_|⟨b,s⟩⟩,v⟩ <;> try rfl
       apply mul_eq_zero_of_right; exact blank hf c h a.2 v
    have hv: V x= V y:= by funext m t; exact Finset.sum_congr rfl fun c _=> (he m t x c).trans (he m t y c).symm
    funext m s; apply split_change; intro u w _; exact congr_fun (congr_fun hv m) (u,w)
end YM.MSbar.Diagram.Parallel
