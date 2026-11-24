import YM.RG03.Transports

/-!
# Walk reduction for repeated path alignment

Compare paths with the same **cover** displacement by a chain of adjacent exchanges and
cancellations, each at still controlled *full path* length. The finite-compression idea in
`YM.Further.CORRECTED_LIFT_COEFFICIENTS.Collapse.compress` concerns curvature coordinates
(germs and rebasing to positive `RG.Slot`s); here instead keep a chain and the possibly signed
oriented squares at each stage. Together with `defect_align` this will allow an exact polynomial
truncation with higher-*degree* tails in transported elementary holonomy defects, on
configurations U themselves, without Taylor-expanding over exponentially many subsets of a
long product of swaps. Implemented at arbitrary finite period normalized gauge field with
moves Lattice.Step (not continuum paths); no analyticity assumption here. The proof is
self-contained through the Lattice path and RG03 imports.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG03.Wiring
open Wilson Lattice
open scoped Classical

/-- Bounded-length paths used at anchors, with *actual elementary moves*, not equality only in
an Abelian quotient of the group. Index is number of cuts/swaps. -/
inductive Chain (M : ℕ) : Walk → Walk → ℕ → Prop
  | idle (w : Walk) (h : w.length ≤ M) : Chain M w w 0
  | swap (r s : Walk) (a b : Step) (h : ((r++[a,b])++s).length ≤ M) :
      Chain M ((r++[a,b])++s) ((r++[b,a])++s) 1
  | erase (r s : Walk) (a : Step) (h : ((r++[a,a.rev])++s).length ≤ M) :
      Chain M ((r++[a,a.rev])++s) (r++s) 1
  | trans {a b c : Walk} {d e : ℕ} (h : Chain M a b d) (h' : Chain M b c e) :
      Chain M a c (d+e)
namespace Chain
variable {M N j : ℕ}{a b : Walk}
lemma raise (h : Chain M a b j) (he : M ≤ N) : Chain N a b j := by
  induction h with
  | idle w h => exact idle w (h.trans he)
  | swap r s a b h => exact swap _ _ _ _ (h.trans he)
  | erase r s a h => exact erase _ _ _ (h.trans he)
  | trans h h' ih ih' => exact ih.trans ih'
lemma right (h : Chain M a b j) (t : Walk) : Chain (M+t.length) (a++t) (b++t) j := by
  induction h with
  | idle w h => exact idle _ (by simp [h])
  | swap r s a b h =>
    rw [List.append_assoc _ s t,List.append_assoc _ s t]; exact swap r (s++t) a b (by rw [← List.append_assoc,List.length_append];omega)
  | erase r s a h => rw [List.append_assoc _ s t,List.append_assoc _ s t]; exact erase r (s++t) a (by rw [←List.append_assoc,List.length_append];omega)
  | trans h h' ih ih' => exact ih.trans ih'
end Chain

private lemma rev_in_tail (L : Walk) (a : Step) (h : stop (0:Cover) (a::L)=0) : a.rev ∈ L := by
  by_contra hp
  rcases a with ⟨i,b | b⟩
  · have hs (z : Cover) (u : Walk) (hz : negDir i ∉ u) : z i ≤ stop z u i := by
      induction u generalizing z with
      | nil => rfl
      | cons c l ih =>
        have ht : negDir i ∉ l := fun h=> hz (List.mem_cons_of_mem _ h)
        refine le_trans ?_ (ih (z+c.vec) ht)
        rcases c with ⟨j,e | e⟩
        · change z i ≤ z i + step j i
          simp only [step_apply]; split <;> omega
        have he : j≠i := fun hj => hz ((show negDir i∈ ⟨j,true⟩::l by subst j; exact List.mem_cons_self))
        change z i ≤ z i + -(step j i); simp [he.symm]
    change stop (0+(posDir i).vec) L=0 at h
    have he := hs (0+(posDir i).vec) L hp; rw [h] at he; simp at he
  have hs (z : Cover) (u : Walk) (hz : posDir i ∉ u) : stop z u i ≤ z i := by
    induction u generalizing z with
    | nil => rfl
    | cons c l ih =>
      have ht : posDir i ∉ l := fun h=> hz (List.mem_cons_of_mem _ h)
      refine (ih (z+c.vec) ht).trans ?_
      rcases c with ⟨j,e | e⟩
      · have he : j≠i := fun hj => hz ((show posDir i∈ ⟨j,false⟩::l by subst j; exact List.mem_cons_self)); change z i + step j i ≤ z i; simp [he.symm]
      change z i + -(step j i) ≤ z i; simp only [step_apply]; split <;> omega
  change stop (0+(negDir i).vec) L=0 at h
  have he := hs (0+(negDir i).vec) L hp
  rw [h] at he; simp at he

private lemma shrink (r : Walk) (a : Step) (s : Walk) (ht : a.rev∈s) : ∃ u : Walk, ∃ e:ℕ,
    Chain (r++a::s).length (r++a::s) u e ∧ stop (0:Cover) u=stop (0:Cover) (r++a::s) ∧
      u.length+2=(r++a::s).length ∧ e ≤ s.length := by
  induction s generalizing r with
  | nil => cases ht
  | cons b w ih =>
    by_cases hh : a.rev=b
    · subst b
      refine ⟨r++w,1,?_,?_,?_,Nat.le_add_left ..⟩
      · simpa only [List.append_assoc,List.cons_append,List.nil_append] using
          (Chain.erase (M:=(r++a::a.rev::w).length) r w a (by simp only [List.length_append,List.length_cons,List.length_nil]; omega))
      · simp [stop_append,stop,Step.vec_rev]
      simp only [List.length_append,List.length_cons]; omega
    obtain ⟨u,e,h,hs,hL,he⟩ := ih (r++[b]) (List.mem_of_ne_of_mem hh ht)
    have sp (z : Step) (w : Walk) : r++ z:: w = r++[z]++w := (List.append_assoc r [z] w).symm
    rw [← sp] at h hs hL
    have hm : (r++a::b::w).length=(r++b::a::w).length := by simp
    rw [← hm] at h hL
    refine ⟨u,1+e,?_,?_,hL,Nat.add_comm _ _ ▸ Nat.succ_le_succ he⟩
    · exact Chain.trans (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using (Chain.swap r w a b (M:=(r++a::b::w).length) (by simp only [List.length_append,List.length_cons,List.length_nil];omega))) h
    rw [hs,stop_append,stop,stop,stop_append,stop,stop,add_right_comm]

theorem crush (w : Walk) (he : stop (0:Cover) w=0) : ∃ k, Chain w.length w [] k ∧ k ≤ w.length^2 := by
  generalize hn : w.length=n
  induction n using Nat.strong_induction_on generalizing w with | h n ih =>
    cases w with
    | nil => refine ⟨0,Chain.idle [] (Nat.zero_le _),Nat.zero_le _⟩
    | cons a w =>
      rw [List.length_cons] at hn
      obtain ⟨v,e,h,hS,hL,hV⟩ := shrink [] a w (rev_in_tail _ _ he)
      simp only [List.nil_append, List.length_cons] at h hS hL
      have hk : v.length<n := by omega
      obtain ⟨u,cl,hh⟩ := ih v.length hk v (hS.trans he) rfl
      rw [hn] at h; refine ⟨e+u,h.trans (cl.raise hk.le),(Nat.add_le_add hV hh).trans ?_⟩
      rw [← hn]; nlinarith

lemma lift_stop {n : Side} (w : Walk) (o : Site n) : stop o w = wrap n (stop (0:Cover) w) + o := by
  have ht (x y : Site n) (v : Walk) : stop (x+y) v = stop x v+y := by
    induction v generalizing x with
    | nil => rfl
    | cons c v ih => rw [stop,stop,show x +y+c.vec=x+c.vec+y from add_right_comm ..,ih]
  rw [wrap_stop_cover,map_zero,← ht,zero_add]

theorem same_lift (r s : Walk) (he : stop (0:Cover) r=stop (0:Cover) s) :
    ∃ k, k ≤ (r.length+s.length)^2 ∧ Chain (r.length+2*s.length) (r++Lattice.reverse s++s) s k := by
  obtain ⟨e,hh,h⟩ := crush (r++Lattice.reverse s) (by rw [stop_append,he,reverse_stop])
  have hl : (r++Lattice.reverse s).length = r.length+s.length := by simp [Lattice.reverse]
  refine ⟨e,hl ▸ h,?_⟩
  rw [show r.length+2*s.length=(r++Lattice.reverse s).length+s.length by omega]
  change Chain _ _ ([]++s) _; exact hh.right s

end YM.RG03.Wiring
