import YM.RG11Proof.Rigidity.Way

/-!
# Link derivative vanishes: all smaller panel assays already read
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open palette Strip Maxwell.Free Function
open scoped BigOperators Classical

variable {Q X C I : Type} [Fintype C] [DecidableEq C] [DecidableEq X]

-- Collect just the terms with a prefixed test x hitting someone in p. This
-- exact sum (colors and remainder multiplicities) appears before doing the
-- induction on the whole panel list.
omit [DecidableEq X] in -- X not in scope of type? lint
private lemma pushing (hit : Q→C→I) (E : I→I→ℝ) (B : Q→Q→ℝ)
    (hK : ∀ i j d c, E (hit i d) (hit j c)= if d=c then B i j else 0)
    (m : List I → ℝ) (h : Swap m) (a b : Q) (p : List (Pair Q)) :
    (∑ s : C, deck hit p (fun u=>pulls u (fun x r=> E (hit a s) x * m (hit b s :: r)))) = pulls p (fun i l=>
      B a i.1 * deck hit ((b,i.2)::l) m + B a i.2 * deck hit ((b,i.1)::l) m) := by
  have he (s : C) := fuses hit E B hK p a s (fun r=>m (hit b s::r)) (fun hp=>h (List.Perm.cons _ hp))
  simp_rw [he]; rw [pulls_sum_outer]; apply pulls_congr; intro v
  simp_rw [Finset.sum_add_distrib,← Finset.mul_sum,deck_bind]

lemma trims (hit : Q→C→I) (E : I → I → ℝ) (B : Q→Q→ℝ)
    (H : ∀ a b,E a b=E b a)
    (hK : ∀ i j d c,E (hit i d) (hit j c)= if d=c then B i j else 0)
    (w : Q→X) (L : List (Pair Q)) (m : List I→ℝ) (hm : Swap m) (S : Finset X)
    (hS : Journey w S L)
    (h0 : ∀ l : List (Pair Q), l.length < L.length → Journey w S l → deck hit l m=0) :
    deck hit L (nick E m)=0 := by
  induction L generalizing S m with
  | nil => rw [deck_nil,nick,pulls_nil]
  | cons a p ih =>
    have hs := legJourney w S a p |>.mp hS
    let X' := insert (w a.2) (insert (w a.1) S)
    let n := fun r=> ∑ s : C, m (hit a.1 s::hit a.2 s::r)
    have hz0 : deck hit p (nick E n)=0 := by
      refine ih _ (fun h=> Finset.sum_congr rfl fun i _=> swap_after m hm _ _ h) X' hs.2.2.2 (fun l hl hL=> ?_)
      have he : palette (l.map (byColor hit)) n = ∑ s,palette (l.map (byColor hit)) (fun r=>m (hit a.1 s :: hit a.2 s :: r)) := palette.sum ..
      refine he.trans (h0 (a::l) (by simp [hl]) ?_)
      exact legJourney w S a l|>.mpr ⟨hs.1,hs.2.1,hs.2.2.1,hL⟩
    have hn : (∑ s : C, deck hit p (nick E (fun l=>m (hit a.1 s:: hit a.2 s :: l))))=0 := by
      unfold deck
      rw [← palette.sum]
      refine Eq.trans ?_ hz0
      unfold deck n; congr 1; funext u
      unfold nick
      simp_rw [Finset.mul_sum]; unfold pulls
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> Finset.sum_comm
    have hi (U V : Q) (hu : U=a.1 ∨ U=a.2) (hv : V=a.1 ∨ V=a.2) :
        (∑ s : C, deck hit p (fun l=> pulls l (fun b r=> E (hit U s) b * m (hit V s :: r))))=0 := by
      rw [pushing hit E B hK m hm U V]
      unfold pulls; apply Finset.sum_eq_zero; intro i _
      let b := p.get i
      let l := p.eraseIdx i.val
      have he : Journey w S (a::b::l) := by
        exact (legJourney w S a _).mpr ⟨hs.1,hs.2.1,hs.2.2.1,pickJourney hs.2.2.2 i⟩
      have ht (t) (H : t=b.1 ∨ t=b.2) : deck hit ((V,t)::l) m=0 :=
        h0 _ (by simp only [List.length_cons, Nat.add_lt_add_iff_right]; exact pulls_short _) (mergeWay _ _ _ _ hv H _ he)
      change B U b.1 * deck hit ((V,b.2)::l) m + B U b.2 * deck hit ((V,b.1)::l) m=0
      rw [ht _ (Or.inr rfl),ht _ (Or.inl rfl),mul_zero,mul_zero,add_zero]
    have ho (s) (l : List I) : nick E m (hit a.1 s::hit a.2 s::l)=
        2*(E (hit a.1 s) (hit a.2 s)*m l)+2*pulls l (fun k r=> E (hit a.1 s) k*m (hit a.2 s::r))+
        2*pulls l (fun k r=>E (hit a.2 s) k*m (hit a.1 s::r))+
        nick E (fun l=>m (hit a.1 s::hit a.2 s::l)) l := by
      rw [nick_cons _ _ _ H,nick_cons _ _ _ H,pulls_cons]; ring
    rw [deck_bind]
    change (∑ s : C, palette (p.map (byColor hit)) (fun r=> nick E m (hit a.1 s::hit a.2 s::r)))=0
    simp_rw [ho,hK,if_true,← mul_assoc (2:ℝ) (B _ _) _,palette.add,palette.mul,Finset.sum_add_distrib,← Finset.mul_sum]
    unfold deck at hn hi h0
    rw [hn,hi _ _ (Or.inl rfl) (Or.inr rfl),hi _ _ (Or.inr rfl) (Or.inl rfl),h0 p (by simp) (hs.2.2.2.weaken (by intro i h; simp [h]))]
    simp

end YM.RG11.Rigidity
