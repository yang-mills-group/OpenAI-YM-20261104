import YM.MSbar.Pole.Sew.Columns

/-! Finish connection over all final-edge choices, always subtracting one unique
MS pole part (values outside strip irrelevant, represented by exact finite
polynomial in negative powers). -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Piece
open Function Set Filter MeasureTheory Ambient Momentum Age Mellin Sew Thread Symbol Curtain
open scoped Topology ContDiff BigOperators Classical
variable {I : Type} [Fintype I]

def includesTerm (M:Finset I)(a:ℤ)(p:Piece I): Piece I:= ⟨p.l,step M ⟨a,p.l⟩ p.g⟩
def cooked (s:List (Piece I))(M:Finset I)(a:ℤ):=s.map (includesTerm M a)

lemma unified (s:List (Piece I))(M:Finset I)(a:ℤ)(r:ℝ): sum s M a r=∑ i:Fin s.length, roll M ⟨a,(s.get i).l⟩ r (s.get i).g := by
  -- use List.sum_ofFn
  let B i:=roll M ⟨a,(s.get i).l⟩ r (s.get i).g; let p (x:Piece I):=roll M ⟨a,x.l⟩ r x.g; change (s.map p).sum=_
  rw [show s.map p=List.ofFn B from ?_, List.sum_ofFn]
  exact (List.ofFn_getElem_eq_map _ p).symm
lemma unifies (s:List (Piece I))(M:Finset I)(a:ℤ)(r:ℝ): sum (cooked s M a) M a r=∑ i:Fin s.length, roll M ⟨a,(s.get i).l⟩ r (step M ⟨a,(s.get i).l⟩ (s.get i).g) := by
  unfold cooked sum
  simp only [List.map_map]
  rw [← List.ofFn_getElem_eq_map,List.sum_ofFn]; rfl

variable {M:Finset I} {a:ℤ}
lemma pure (k : ℕ) (F : ℕ→Cloud I) (h : ∀ i<k,Local M a (F i)) {z:ℂ} : Local M a (purePolar k F z) := by induction k with
  | zero=> rw [purePolar_zero]; exact Local.zero
  | succ i ih=> rw [purePolar_up,Pi.add_apply]; exact (ih fun j hj=>h j (by omega)).add ((h i (by omega)).number _)
lemma priced (k :ℕ)(F : ℕ→Cloud I) (h : ∀ i<k,Canonical (F i)): Vortex k (purePolar k F):= by
  induction k with
  | zero=>rw [purePolar_zero]; exact Vortex.zero 0
  | succ i ih=>
    rw [purePolar_up]; refine Vortex.add ((ih fun j hj=>h j (by omega)).mono (by omega)) ⟨1,(fun _=>F i),zero_lt_one,(h i (by omega)).constant,fun z hz n x=> ?_⟩; have ht:z≠0:= hz.2
    change z^_* (z⁻¹^_*F i n x)=_; rw [inv_pow,mul_inv_cancel_left₀ (pow_ne_zero _ ht)]

variable {S T:Finset I} {s : List (Piece I)}
def remit (s:List (Piece I)) (M:Finset I)(a:ℤ)(H:ℂ→Cloud I) := Piece.mk 0 (-H)::cooked s M a

/-- Kept on all positive length values together; permits multisource contacts
through those units. -/
structure Accounts (s : List (Piece I)) (M : Finset I)(a:ℤ) (S T : Finset I) (H:ℂ→Cloud I) : Prop where
  charge : ∀ z, Local M a (H z)
  stocks : ∃ k : ℕ,∃ C:ℕ→Cloud I, H=purePolar k C ∧ ∀ i<k,Local M a (C i)∧Shape S T (C i)
  endures : ∀ r:ℝ,0<r → Vortex 0 (sum (cooked s M a) M a r-H)

lemma matures (h:Flag s M a S T)(hs:Disjoint M T) : ∃ H:ℂ→Cloud I, Accounts s M a S T H:=by
  choose k hk using fun i : Fin s.length=>(h.law (s.get i) (List.get_mem s i)).1
  let L:= Finset.univ.sup k
  have hb (i:Fin s.length) := h.law (s.get i) (List.get_mem s i)
  obtain ⟨C,hC,H⟩:= solved_mellin (s:=Finset.univ) (a:=a) (A:=M) (l:=fun i=> (s.get i).l) (k:=L) (J:=fun i=> (s.get i).g)
          (fun i _ => (hk i).mono (Finset.le_sup (Finset.mem_univ _))) (fun i _ => (hb i).2.2) (fun r hr=> unified s M a r ▸ h.clean r hr)
  have hp : ∀ r:ℝ,0<r→ Vortex 0 (sum (cooked s M a) M a r-purePolar (L+1) C):=fun r hr=>by rw [unifies]; exact H r hr
  have he : Acts S T (sum (cooked s M a) M a 1) := by
    refine senses ?_ hs a 1; intro i hi
    obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hi; obtain ⟨⟨k,hk⟩,hQ,_⟩:=h.law v hv
    exact whirl hk hQ ⟨a,v.l⟩ hs -- ambiguous
  refine ⟨purePolar (L+1) C, fun z=> pure (L+1) C fun i _=> hC i, ⟨L+1,C,rfl, fun i hi=> ⟨hC i, Shape.residue (hp 1 zero_lt_one) he i hi⟩⟩,hp⟩

lemma Accounts.serves {H:ℂ→Cloud I} (h:Flag s M a S T) (hq:Accounts s M a S T H) (hs:Disjoint M T): Stack (remit s M a H) M a S T:=by
  have he (r : ℝ) (hr:0<r): roll M ⟨a,0⟩ r (-H)= -H:=by
    funext z n x; exact (hq.charge z |>.neg).echo r hr z _ _
  constructor
  · intro x hx; rcases List.mem_cons.mp hx with hg|hg
    · subst x; constructor
      · obtain ⟨k,C,H,hc⟩:=hq.stocks; refine ⟨k,?_⟩; change Vortex _ (-_); rw [H, neg_eq_zero_sub]; exact (Vortex.zero _).sub (priced k C fun i hi=> (hc i hi).1.regular)
      · obtain ⟨k,C,rfl,hf⟩:=hq.stocks -- shadow
        refine Eventually.of_forall fun z=>?_; change Shape S T _
        have hu := Shape.scale (Shape.sum (Finset.range k) (fun i=> z⁻¹^(i+1) • C i) (fun i (hi:i∈Finset.range k)=>(hf i (Finset.mem_range.mp hi)).2.scale _)) (-1)
        change Shape S T ((-purePolar k C) z); simp only [purePolar,Pi.neg_apply,Finset.sum_apply]
        rw [neg_one_smul] at hu; exact hu
      refine fun _=> Eventually.of_forall fun z n x=> ⟨_,tendsto_const_nhds (x:=(-H) z n x) |>.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht; exact (congr_fun (congr_fun (congr_fun (he t ht) _) _) _).symm
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hg; obtain ⟨⟨k,hk⟩,he,hW⟩:=h.law i hi
    refine ⟨⟨_, beyond M _ hk⟩,whirl hk he _ hs,fun hi=>?_⟩
    have hp := (currents M _ hk hW).2 hi
    refine Eventually.mono hp fun z hz n x=> ⟨0,?_⟩
    change i.l=0 at hi
    specialize hz n x
    change Tendsto (fun t : ℝ=>roll M ⟨a,0⟩ t (step M ⟨a,i.l⟩ i.g) z n x) _ _
    rw [show Age.mk a 0=⟨a,i.l⟩ from congr_arg _ hi.symm]; exact hz -- rewriting accidental
  intro r hr; unfold remit; rw [sum_cons]; change Vortex _ (roll M ⟨a,0⟩ r (-H)+_); rw [he r hr,neg_add_eq_sub]; exact hq.endures r hr
end YM.MSbar.Pole.Piece
