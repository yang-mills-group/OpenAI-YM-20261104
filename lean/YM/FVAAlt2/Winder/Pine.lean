import YM.FVAAlt2.Winder.Loops
/-! # First convergence theorem for qualifying exact coefficient arrays, already lifted -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Budget.FVAAlt2.Wind.Pine
open Function Set Filter Budget.Layer Budget.Packet Budget.Tuple Diagram
open scoped ENNReal NNReal BigOperators Classical Topology
variable {X Y Z W : Type} {l:Filter W} {K : Layer X X}{U : W→Layer X X} {i j r s:ℕ}

abbrev aster (l:Filter W)(K:Layer X X)(U: W→Layer X X) := ∃ C,SplitT l C K U
def below (l:Filter W)(v:Packet X r)(F:W→Packet X r) := ∃ C,Pivot l C v F
def above (l:Filter W)(v:Packet X r)(F:W→Packet X r) :=∃ C, Earn l C v F
variable {v u:Packet X r}{F G:W→Packet X r}
lemma below.free0 : below l (0:Packet X r) (fun _=>0):= ⟨_,Pivot.free⟩
lemma above.free0 : above l (0:Packet X r) (fun _=>0):= ⟨_,Earn.free⟩
lemma below.note (v:Packet X 0)(F₁:W→Packet X 0) : below l v F₁:= ⟨ 0,⟨ENNReal.zero_ne_top,fun _ i=> Fin.elim0 i⟩⟩ -- unused x l
lemma below.plus (m: below l v F)(n:below l u G) : below l (v+u) fun i=> F i + G i:= by obtain ⟨_,h⟩:=m; obtain ⟨_,h'⟩:= n; exact ⟨_,h.add h'⟩
lemma above.plus (m:above l v F)(n:above l u G) : above l (v+u) fun i=> F i+G i:= by obtain ⟨_,h⟩:=m; obtain ⟨_,h'⟩:=n; exact ⟨_,h.add h'⟩
lemma below.scale (m:below l v F) (t:ℝ): below l (t • v) (fun i=> t • F i):= by obtain ⟨_,h⟩:= m; exact ⟨_,h.scale _⟩
lemma above.scale (m:above l v F) (t:ℝ): above l (t • v) (fun i=> t • F i):= by obtain ⟨_,h⟩:=m; exact ⟨_,h.scale _⟩
lemma below.crop (m:below l v F)(t:Y↪ X): below l (Packet.crop t v) fun i=> Packet.crop t (F i):=by obtain ⟨_,h⟩:= m; exact ⟨_,h.crop _⟩
lemma above.crop (m:above l v F)(t:Y↪ X): above l (Packet.crop t v) fun i=> Packet.crop t (F i):=by obtain ⟨_,h⟩:=m; exact ⟨_,h.crop _⟩
lemma below.offer (m:below l v F)(t:X↪ Y): below l (Packet.offer t v) fun i=> Packet.offer t (F i):=by obtain ⟨_,h⟩:= m; exact ⟨_,h.offered _⟩
lemma above.offer (m:above l v F)(t:X↪Y): above l (Packet.offer t v) fun i=> Packet.offer t (F i):=by obtain ⟨_,h⟩:= m; exact ⟨_,h.offered _⟩
lemma below.sum (I:Finset Z){v:Z→Packet X r}{F:Z→W→Packet X r}(m:∀ i∈I,below l (v i) (F i)): below l (∑ i∈I,v i) (fun w=>∑ i∈I,F i w):=by
 induction I using Finset.induction_on with
 | empty=> simp only [Finset.sum_empty]; exact below.free0
 | insert i I h ih=> simp_rw [Finset.sum_insert h]; exact (m _ (by simp)).plus (ih (fun i hi=> m i (Finset.mem_insert_of_mem hi)))
lemma above.sum (I:Finset Z){v:Z→Packet X r}{F:Z→W→Packet X r}(m:∀ i∈I,above l (v i) (F i)): above l (∑ i∈I,v i) (fun w=>∑ i∈I,F i w):=by
 induction I using Finset.induction_on with | empty=> simp only [Finset.sum_empty]; exact above.free0 | insert i I h ih=> simp_rw [Finset.sum_insert h]; exact (m _ (by simp)).plus (ih (fun i hi=>m i (Finset.mem_insert_of_mem hi)))
lemma below.pull (m:below l v F)(n:aster l K U): below l (draft K v) fun i=>draft (U i) (F i) := by obtain ⟨_,h⟩:=m; obtain ⟨_,h'⟩:=n; exact ⟨_, (Pivot.drawing _ h h').ways ⟩
lemma above.pull (m:above l v F)(n:aster l K U): above l (draft K v) fun i=> draft (U i) (F i):= by obtain ⟨_,h⟩:=m; obtain ⟨_,h'⟩:=n; exact ⟨_,(Earn.drawing _ h h').ways⟩
section Heat
variable (k r:ℕ){B D: Ranked X}{G R:W→Ranked X}
lemma below.lap (m:below l (B (r+2)) (fun i=>G i (r+2)))(h:aster l K U): below l (heating K B r) (fun i=> heating (U i) (G i) r):= by obtain ⟨_,H⟩:=m; obtain ⟨_,h'⟩:=h; exact ⟨_,((H.loops h').ways).scale _⟩
lemma above.lap (m:above l (B (r+2)) (fun i=> G i (r+2)))(h:aster l K U): above l (heating K B r) fun i=>heating (U i) (G i) r:= by obtain ⟨_,H⟩:=m; obtain ⟨_,h'⟩:=h; exact ⟨_,((H.loops h').ways).scale _⟩
lemma below.fuse (m:∀ r, below l (B (r+1)) (fun i=> G i (r+1)))(n:∀ r,below l (D (r+1)) (fun i=> R i (r+1)))(h:aster l K U): below l (force K B D r) (fun i=> force (U i) (G i) (R i) r):=by
 apply below.sum; intro z hz; obtain he:= Finset.mem_antidiagonal.mp hz; rw [← he ]; obtain ⟨_,hk⟩:=m z.1; obtain ⟨_,h'⟩:=n z.2; obtain ⟨_,hU⟩:=h; unfold matchTwo; simp only; exact ⟨_,((hk.knots h' hU).ways).scale _ ⟩ -- by-canonical h=rfl reduces? ite reflex dec.Finset
lemma above.fuse (m:∀ r,above l (B (r+1)) (fun i=> G i (r+1)))(n:∀ r,below l (D (r+1)) (fun i=> R i (r+1)))(h:aster l K U): above l (force K B D r) (fun i=>force (U i) (G i) (R i) r):=by
 apply above.sum; intro z hz; obtain he:=Finset.mem_antidiagonal.mp hz; rw [← he]; obtain ⟨_,hk⟩:=m z.1; obtain ⟨_,h'⟩:=n z.2; obtain ⟨_,hU⟩:=h; unfold matchTwo; simp only; exact ⟨_,((hk.knots h' hU).ways).scale _⟩
end Heat
variable {V:Orders X}{Τ:W→ Orders X}
lemma unmarked (m:∀ i j,below l (V i j) (fun w=>Τ w i j))(h:aster l K U)(β γ:Bool)(k:ℕ) : ∀ i r, below l (logHeat K V β k i r) (fun w=> logHeat (U w) (Τ w) γ k i r):=by
 induction k using Nat.strong_induction_on with
 | _ k ih=>
    intro i r; by_cases he:r=0; subst r; exact below.note ..
    cases k
    · simp_rw [ logHeat_first,he,false_and, if_false]; exact m _ _
    next k=>
       simp_rw [logHeat_next,he,false_and,if_false]; apply below.scale; apply below.plus; exact below.lap _ (ih k (by omega) _ _) h
       apply below.scale; unfold drift carry; apply below.sum; intro z hz; apply below.sum; intro a ha; have hp:= Finset.mem_antidiagonal.mp hz; exact below.fuse r ( fun r=> ih _ (by omega) _ _ ) ( fun r=> ih _ (by omega) _ _) h
lemma closeV (m:∀ i j,below l (V i j) (fun w=> Τ w i j))(h:aster l K U)(β γ: Bool)(r i:ℕ): below l (ceaseHeat K V β i r) fun w=>ceaseHeat (U w) (Τ w) γ i r:=by unfold ceaseHeat heated; apply below.sum; exact fun z _=> unmarked m h _ _ _ _ _
variable {F₁:Orders X}{Q:W→Orders X}
lemma source {V:ℕ→Orders X}{Τ:W→ℕ→Orders X} (m:∀ k i j,below l (V k i j) (fun w=> Τ w k i j))(n:∀ i j,above l (F₁ i j) (fun w=> Q w i j))(h:aster l K U) (k:ℕ): ∀ i r,above l (markHeat K V F₁ k i r) (fun w=> markHeat (U w) (Τ w) (Q w) k i r):=by
 induction k using Nat.strong_induction_on with
 | _ k ih=>
    intro i r; cases k
    · simp_rw [markHeat_first]; exact n _ _
    next k=>
       simp_rw [markHeat_next]; apply above.scale; apply above.plus; exact above.lap _ (ih k (by omega) _ _) h
       unfold drift carry; apply above.sum; intro z hz; apply above.sum; intro a ha; have hp:= Finset.mem_antidiagonal.mp hz; exact above.fuse r (fun r=> ih _ (by omega) _ _) (fun j=> m _ _ _) h
lemma closeM (m:∀ i j,below l (V i j) (fun w=> Τ w i j))(n:∀ i j,above l (F₁ i j) (fun w=> Q w i j))(h:aster l K U)(β γ:Bool)(e r i:ℕ): above l (endHeat e K (logHeat K V β) F₁ i r) fun w=>endHeat e (U w) ( logHeat (U w) (Τ w) γ ) (Q w) i r:=by unfold endHeat heated; apply above.sum; exact fun z _=> source (fun _ _ _=> unmarked m h _ _ _ _ _ ) n h z i r
end YM.RegulatorIR.Budget.FVAAlt2.Wind.Pine
