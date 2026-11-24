import YM.OPE.Sparse.Erase

/-! A path through a designated literal tree, all ancestor horizons retained.
Used when the other inputs have been proved to erase exactly, NOT pruning any
singular operator. Price comparison independent of ratios. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Sparse
open Orbits Orbits.Reader Nesting Nesting.Tree Function Filter Set Table
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
abbrev pathTree : (t:Tree)→t.Leaf→Tree:= Tree.rec (motive:=fun t=>t.Leaf→Tree)
     (fun _=>Tree.bud) (fun n f ih j=>Tree.fork 1 fun _=> ih j.fst j.snd)
namespace Tracing
def inlet : (t:Tree)→(j:t.Leaf)→ (pathTree t j).Inner→t.Inner :=
 Tree.rec (motive:=fun t=>(j:t.Leaf)→(pathTree t j).Inner→t.Inner) (fun _ x=> nomatch x) (fun n f ih j=>fun
   | Sum.inl ()=>Sum.inl ()
   | Sum.inr ⟨_,v⟩ => Sum.inr ⟨j.fst,ih j.fst j.snd v⟩)
def layout : (t:Tree)→(j:t.Leaf)→ (pathTree t j).Positions→t.Positions :=
 Tree.rec (motive:=fun t=>(j:t.Leaf)→(pathTree t j).Positions→t.Positions) (fun _ x=> ()) (fun n f ih j=>fun
   | Sum.inl ()=>Sum.inl ()
   | Sum.inr ⟨_,v⟩ => Sum.inr ⟨j.fst,ih j.fst j.snd v⟩)

lemma narrow(t:Tree)(j:t.Leaf): Measuring.Tree.Narrow (pathTree t j):=by
   induction t with
   | bud=>exact True.intro
   | fork n f ih=>exact ⟨le_rfl,fun p=>ih _ j.snd⟩
lemma name_unique(t:Tree)(j:t.Leaf): Nonempty ((pathTree t j).Leaf) ∧ Subsingleton ((pathTree t j).Leaf):= by induction t with
   | bud=>change Nonempty Unit ∧ Subsingleton Unit; exact ⟨⟨()⟩,inferInstance⟩
   | fork n f ih=>
       change Nonempty (Σ (_:Fin 1), (pathTree (f j.fst) j.snd).Leaf) ∧ Subsingleton (Σ (_:Fin 1), (pathTree (f j.fst) j.snd).Leaf)
       have ht := ih j.1 j.2; obtain ⟨s⟩:=ht.1
       refine ⟨⟨0,s⟩,{allEq:=?_}⟩; intro u v; obtain ⟨l,q⟩:=u; obtain ⟨l',q'⟩:=v; cases Subsingleton.elim l l'; exact congr_arg (Sigma.mk l) ((ht.2).allEq q q')
lemma seats(t:Tree)(j:t.Leaf)(p:(pathTree t j).Leaf): layout t j ((pathTree t j).leafSeat p)=t.leafSeat j:=by induction t with
   | bud=>cases j; rfl
   | fork n f ih=>
      rcases p with ⟨l,q⟩; rcases j with ⟨i,p'⟩
      change (Sum.inr ⟨i,layout (f i) p' (_: (pathTree (f i) p').Positions)⟩:Unit⊕ Σ v,(f v).Positions) = Sum.inr ⟨i,_⟩
      rw [ih i]
lemma top(t:Tree)(j:t.Leaf): layout t j ((pathTree t j).topSeat)=t.topSeat:=by cases t <;> rfl
lemma embeds(t:Tree)(j:t.Leaf) : Injective (inlet t j):=by induction t with
  | bud=>intro u; cases u
  | fork n f ih=>
     intro a b h; rcases a with ⟨_⟩|⟨i,p⟩ <;> rcases b with ⟨_⟩|⟨k,q⟩; rfl; exact Sum.inl_ne_inr h |>.elim; exact Sum.inr_ne_inl h |>.elim
     cases Subsingleton.elim i k; exact congr_arg (fun r=> Sum.inr (α:=Unit) (β:=Σ(_:Fin 1), _) ⟨i,r⟩) (ih j.fst _ (eq_of_heq (Sigma.mk.inj (Sum.inr.inj h)|>.2)))
lemma proportion (t:Tree)(j:t.Leaf)(s:t.Inner→ℝ)(p:(pathTree t j).Inner)(a:ℝ) : (pathTree t j).ratios a (s ∘ inlet t j) p= t.ratios a s (inlet t j p) :=by induction t generalizing a with
  | bud=>cases p
  | fork n f ih=> rcases p with ⟨_⟩ | ⟨l,q⟩; rfl; exact ih j.fst j.snd (childAge j.1 s) q (s (Sum.inl ()))
lemma priority (t:Tree)(j:t.Leaf) (s:t.Leaf→ℝ)(hs:∀ p,0 ≤ s p)(r:ℝ)(hr:r ≤ s j): (pathTree t j).headSum (fun _=>r) ≤ t.headSum s ∘ inlet t j:=by induction t generalizing r with
  | bud=>intro u; cases u
  | fork n f ih=>
      intro u; rcases u with ⟨_⟩|⟨l,q⟩
      · obtain ⟨h,h'⟩:=name_unique (fork n f) j; have : Unique ((pathTree (fork n f) j).Leaf):= {default:=Nonempty.some h,uniq:=fun a=>h'.allEq _ _}
        change ∑ z:(pathTree (fork n f) j).Leaf,r ≤ ∑ v:(fork n f).Leaf,s v; rw [Fintype.sum_unique]; exact hr.trans (Finset.single_le_sum (fun i _=>hs i) (Finset.mem_univ j))
      exact ih j.fst j.snd (childWages j.fst s) (fun p=>hs _) r hr q

lemma tapered (t:Tree) {a b:ℝ} (j:t.Leaf){s:t.Inner→ℝ} (h:Tapered t a b s):Tapered (pathTree t j) a b (s ∘ inlet t j):=by induction t generalizing a with
  | bud=>exact True.intro
  | fork n f ih=>exact ⟨h.1,h.2.1,fun k:Fin 1=>ih j.fst j.snd (h.2.2 j.fst)⟩
lemma relative (t:Tree) {M η:ℝ} (j:t.Leaf){s:t.Inner→ℝ}{z:t.Plot}(h:Relative M η t s z) :Relative M η (pathTree t j) (s ∘ inlet t j) (z ∘ layout t j) :=by induction t with
  | bud=>exact True.intro
  | fork n f ih =>exact ⟨fun v=> h.1 (layout _ j v),fun i j _ _ h=> (h (Subsingleton.elim i j)).elim,fun _=> ih j.fst j.snd (h.2.2 j.fst)⟩
lemma fits (t:Tree){a M η:ℝ} (j:t.Leaf){s:t.Inner→ℝ}{z:t.Plot} (h:Accept a M η s z): Accept a M η (s ∘ inlet t j) (z ∘ layout t j):=by
    refine ⟨tapered t j h.levels, relative t j h.relative, ?_⟩
    cases t; · exact h.scale
    exact h.scale
lemma root (t:Tree)(j:t.Leaf) (z:t.Plot): Tree.anchor (z ∘ layout t j)=Tree.anchor z:= congr_arg z (top t j)
lemma points(t:Tree)(j:t.Leaf)(z:t.Plot):Tree.profile (z ∘ layout t j)=z ∘ (fun _=> t.leafSeat j):= funext fun p=> congr_arg z (seats t j p)

namespace Price
private lemma nonnegative (t:Tree)(s:t.Leaf→ℝ)(hs:∀v:t.Leaf,0 ≤ s v)(i:t.Inner):0≤t.headSum s i:=by induction t with
 | bud=>cases i
 | fork n f ih=> rcases i with ⟨_⟩ | ⟨i,j⟩; exact Finset.sum_nonneg (fun l _=>hs l); exact ih i (childWages i s) (fun l=>hs _) j
variable {n:ℕ}{f:Fin n→Tree}
local notation "t"=>Tree.fork n f

def outer(j:(Tree.fork n f).Leaf): YM.OPE.Measuring.Tree.Nonroot (fun (_:Fin 1)=>pathTree (f j.fst) j.snd)→ YM.OPE.Measuring.Tree.Nonroot f := fun p=> ⟨j.fst, inlet (f j.fst) j.snd p.snd⟩
lemma outer_inj (j:(Tree.fork n f).Leaf):Injective (outer j) :=fun i k h=> Sum.inr_injective ((embeds (Tree.fork n f) j) (congr_arg (Sum.inr (α:=Unit)) h : inlet t j (.inr i) = inlet t j (.inr k) )) -- syntax?
lemma allows(j:(Tree.fork n f).Leaf)(s:(Tree.fork n f).Inner→ℝ)(h:Tapered t 1 1 s)(a:(Tree.fork n f).Leaf→ℝ)(ha:∀i:(Tree.fork n f).Leaf,0≤a i)(x:ℝ)(he:x≤a j)(m:ℝ): Nesting.Tree.toll (f:=fun (_:Fin 1)=>pathTree (f j.fst) j.snd) (fun _=>x) 0 m (s ∘ inlet _ j) ≤ toll a 0 m s:=by
     let fj:=fun (_:Fin 1)=>pathTree (f j.fst) j.snd
     let B(j:(Tree.fork n f).Inner):ℝ:=((Tree.fork n f).ratios 1 s j)^(-(Tree.fork n f).headSum a j - (0:ℝ))
     let q:=pathTree t j; let u (l:q.Inner):ℝ:= (q.ratios 1 (s ∘ inlet t j) l)^(-(q.headSum (fun _=>x) l)- (0:ℝ))
     have ht:=Measuring.Tree.tempered h one_pos
     have h'(l:q.Inner):u l≤ B (inlet t j l):=by
         dsimp only [u,q,B]; rw [proportion]
         exact Real.rpow_le_rpow_of_exponent_ge (ht _).1 (ht _).2 (sub_le_sub_right (neg_le_neg (priority t j a ha x he l)) _)
     have h₀(l:(Tree.fork n f).Inner):1 ≤ B l:= Real.one_le_rpow_of_pos_of_le_one_of_nonpos (ht l).1 (ht l).2 (by rw [sub_zero]; exact neg_nonpos.mpr (nonnegative t a ha l))
     have h'' :∏ l:q.Inner,u l ≤ ∏ k:(Tree.fork n f).Inner,B k := calc
          _ ≤ ∏ l:q.Inner,B (inlet t j l):= Finset.prod_le_prod (fun l _=> Real.rpow_nonneg ((ht (inlet t j l)).1.le.trans_eq (proportion t j s l 1).symm) _) (fun i _=>h' i)
          _ ≤ ∏ k∈ Finset.univ.image (inlet t j),B k:= (Finset.prod_image (embeds t j).injOn).symm.le
          _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _) (fun k _=>zero_le_one.trans (h₀ k)) fun k _ _=>h₀ k
     rw [← toll_eq (f:=f) (h.positive (Sum.inl ())), ← toll_eq (f:=fj)]; swap; exact h.positive _
     change (s (.inl ()))^m * ∏ l:q.Inner,u l ≤ (s (.inl ()))^m * ∏ k:(Tree.fork n f).Inner,B k
     exact mul_le_mul_of_nonneg_left h'' (Real.rpow_nonneg (h.positive (Sum.inl ())|>.le) _)
lemma saving (j:(Tree.fork n f).Leaf)(s:(Tree.fork n f).Inner→ℝ)(h:Tapered t 1 1 s)(D:(Tree.fork n f).Inner→ℕ):
    let fj:=fun (_:Fin 1)=>pathTree (f j.1) j.2
    Nesting.Tree.nestPrice (f:=fj) (s ∘ inlet (Tree.fork n f) j) (D ∘ inlet _ j) ≤ Nesting.Tree.nestPrice (f:=f) s D := by
    intro fj
    let q:=Tree.fork 1 fj
    let g(i:Measuring.Tree.Nonroot f):ℝ:= ((Tree.fork n f).ratios 1 s (.inr i))^(D (Sum.inr i)+1)
    let g'(i:Measuring.Tree.Nonroot fj):ℝ:= (q.ratios 1 (s ∘ inlet t j) (.inr i))^((D ∘ inlet _ j) (.inr i)+1)
    have he:=Measuring.Tree.tempered h one_pos
    have eq(i:Measuring.Tree.Nonroot fj):g' i=g (outer j i):= by change ((pathTree t j).ratios 1 (s ∘ inlet t j) (Sum.inr i))^(D (inlet t j (Sum.inr i))+1) = _; rw [proportion]; rfl
    have hP :(∑ i:Measuring.Tree.Nonroot fj,g' i)=(∑ i∈ Finset.univ.image (outer j),g i):=by rw [Finset.sum_image (outer_inj j).injOn]; simp only [eq]; congr
    apply hP.trans_le (?_)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _=> pow_nonneg (he (Sum.inr i)).1.le _
end Price
end Tracing
end YM.OPE.Sparse
