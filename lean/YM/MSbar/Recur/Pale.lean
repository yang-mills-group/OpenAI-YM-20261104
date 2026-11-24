import YM.MSbar.Diagram.Parallel
import YM.MSbar.Scale.Flat
import YM.MSbar.Recur.Load
/-! Flat-germ projections of trees. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Play.Pale
open Filter Dim Symbol Domain Diagram Scale Function Set Super Loops
open scoped Topology BigOperators Classical ContDiff
variable {C:Type}{W: Edition C}{P Q:Sites C} {n:ℕ}{l k e d:Bit}{x y:ℂ}{R:Finsupp C ℂ}{f g:Vertex C} (hf:Live W d f)(hg:Live W e g)

abbrev Near (f:ℝ→ℂ):Prop:= ∀ᶠ t:ℝ in 𝓝 0,f t=0
lemma range {ι:Type*}{s:Finset ι}{f:ι→ℝ→ℂ}(h:∀ i∈s,Near (f i)): Near (fun x=>∑ i∈s,f i x):= by
    obtain he:= (s.eventually_all (l:=𝓝 (0:ℝ)) (p:=fun i v=>f i v=0)).mpr h -- name check
    exact he.mono fun x hx=> Finset.sum_eq_zero hx
lemma kind {T:Type*}(p:T→ Bit)(F:ℝ→ List T→List T→ℂ)(v:List T)(h:∀ x y,(x++y).Perm v→Near (fun t=>F t x y)): Near (fun t=> split p (F t) v):=by
    induction v generalizing F with
    | nil=> simpa using h [] [] List.Perm.rfl
    | cons a v ih=>
        have hy:= ih (fun b s t=> sign (p a) (oddity p s)*F b s (a::t)) (fun x y H=> (h _ _ (List.perm_middle.trans (H.cons a))).mono (fun b hb=>by simp [hb]))
        refine ((ih (fun t x y=> F t (a::x) y) (fun x y H=> h _ _ (H.cons a))).and hy).mono fun t ht=> ?_; dsimp only at ht ⊢; rw [split_next,ht.1,ht.2,zero_add]
-- move momentum rays. Use even outside support constraints
lemma in_split (W:Edition C)(F:Words C n→Words C n→ℂ)(v:Words C n)(t:ℝ): split (lift (W.binary n)) F (drag t v)=split (lift (W.binary n)) (fun x y => F (drag t x) (drag t y)) v:=by
   induction v generalizing F with | nil=> simp [drag] | cons a v ih=> simp only [drag_cons,split_next,ih]; simp_rw [drag_pat]

abbrev Light (P:Sites C) : Prop := ∀ i a b (p: Mom i), Near fun t=> P i a b (t • p)
-- flat of tree terms if either input flat or kernel vanishes near p=0
include hf hg
lemma flat_tree (h:Light P ∨ Flat f ∨ Flat g): Flat (traceT W d x P f g):= by
    intro i v; rw [Parallel.tree hf hg]; refine range (fun a hA=> range fun b hB=> ?_)
    simp_rw [in_split]; apply kind; intro u v H
    let r:= -channel u; unfold Loops.price; simp only [drag_bal]
    simp_rw [← smul_neg]; rcases h with h|h|h
    · filter_upwards [h i a b r,h i a b (channel u)] with t ht hu; change P i _ _ (t•r) /2 * _+_= _ ; rw [ht,hu]; ring
    · filter_upwards [h i ((a,r)::u),h i ((b,r)::u)] with t ht hu;rw [drag_cons] at ht hu; change _*( _* f i ((a,t•r)::_)*_)+ _ * (_* f i ((b,t•r)::_)*_)=_; rw [ht,hu]; ring
    filter_upwards [h i ((a,channel u)::v),h i ((b,channel u)::v)] with t ht hu; rw [drag_cons] at ht hu; rw [show g i ((b,t• channel u)::_)= 0 from hu,show g i ((a,t• channel u)::_)=0 from ht]; ring
omit hg
include hf
lemma arrow_row (hq:Pilot univ 0 W k (liftS Q)) : traceR W x Q f n = split (lift (W.binary n)) (flow (Q n) (W.members n) (f n)):= by
    rw [Parallel.sameR hf x (n:ℂ)]; unfold traceR; rw [Arrow.lifts hf hq (mem_univ _),Loops.rooted _ (hf.span _ (mem_univ _) _)]
lemma flat_row (hq:Pilot univ 0 W k (liftS Q))(h: Flat f) : Flat (traceR W x Q f) :=by
    intro i v; rw [arrow_row hf hq]; simp_rw [in_split]; apply kind; rintro (_|⟨a,_|⟨b,u⟩⟩) y hy <;> try exact Eventually.of_forall fun _=> rfl
    -- used pattern `_ | u` issue
    apply range; intro b hb; filter_upwards [h i ((b,a.2)::y)] with t ht; rw [drag_cons] at ht; exact mul_eq_zero_of_right _ ht
end YM.MSbar.Play.Pale
