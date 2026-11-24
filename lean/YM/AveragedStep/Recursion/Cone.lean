import YM.AveragedStep.Recursion.Flight
/- Low slot cones, always before sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep.SD
open Filter Function Lattice RG Loops Tree Wilson Precision Metric Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
open Finsupp
variable {c f:Side}{G:Gauge}{S:StepData c f}
def pop : Ink G c f→ℕ:= fun i=>i.1.elim (fun _=>1) (fun _=>0)
def clips (w:Lips G c f):ℕ:=(w.map pop).sum
lemma clips_cons (i:Ink G c f)(w):clips (i::w)=pop i + clips w:=rfl
lemma full (w:Lips G c f):clips w ≤ w.length:=by
 induction w with
 | nil=> simp [clips]
 | cons i w ih=> rw [clips_cons,List.length_cons,add_comm]; apply Nat.add_le_add ih; rcases i with ⟨_|_,_⟩; exact le_rfl; exact Nat.zero_le 1
lemma steps_cons (i:Ink G c f)(w)(x:Site f):steps (S:=S) x (i::w)=(separation x (atRim S i.1):ℝ)+steps (S:=S) x w:=rfl
lemma steps_attach (x:Site f)(u v:Lips G c f):steps (S:=S) x (u++v) = steps (S:=S) x u + steps (S:=S) x v:=by simp [steps]

structure Shy (S:StepData c f)(j:Ink G c f)(w v:Lips G c f):Prop where
  lo : v.length ≤ w.length+1
  fine : clips v ≤ clips w
  pays (x:Site f): steps (S:=S) x v ≤ steps (S:=S) x w+(separation x (atRim S j.1):ℝ)+2*aperture S.patch
lemma Shy.lifts (S:StepData c f)(i:Ink G c f){j}{w v:Lips G c f}(h:Shy S j w v):Shy S j (i::w) (i::v):=by
 obtain ⟨h1,h2,h3⟩:=h; constructor
 · simp only [List.length_cons]; omega
 · exact Nat.add_le_add_left h2 _
 intro x; simp only [steps_cons]; linarith only [h3 x]
lemma Shy.closes (S:StepData c f)(i j:Ink G c f)(w:Lips G c f):Shy S j (i::w) w:=by
 constructor
 · simp; omega
 · exact Nat.le_add_left ..
 intro x; rw [steps_cons];
 have h:0≤(separation x (atRim S i.1):ℝ):=by positivity
 have f:0≤(separation x (atRim S j.1):ℝ):=by positivity
 have m:0≤2*(aperture S.patch:ℝ):=by positivity
 linarith only [h,f,m]
lemma shy_del (S:StepData c f)(j:Ink G c f)(w:Lips G c f):Signed (Shy S j w) (del j w) (w.length:ℝ):=by
 induction w with
 | nil=> rw [del]; simpa using Signed.zero (Shy S j [])
 | cons i w ih=>
   have he:= ih.left (Shy S j w) (List.cons i) (Shy S j (i::w)) (fun _=>Shy.lifts S i) -- dotted?
   rw [del,List.length_cons,Nat.cast_add,Nat.cast_one,add_comm (↑w.length:ℝ)]
   refine Signed.plus ?_ he
   by_cases e:j=i; · simpa only [if_pos e,abs_one] using Signed.single _ (Shy.closes S i j w) 1
   rw [if_neg e]; exact (Signed.zero _).enrich (fun _=> id) zero_le_one
lemma local_travel (S:StepData c f)(j i:Rim c f)(h:i∈home S j)(x:Site f): (separation x (atRim S i):ℝ) ≤ (separation x (atRim S j):ℝ)+(2:ℝ)*(aperture S.patch):=by
 exact_mod_cast (separation_triangle x (atRim S j) (atRim S i)).trans (Nat.add_le_add_left (reach_home S j h) _)
lemma shy_equity {A:ChartRatio G}(S:StepData c f)(h:S.patch.Branches S.kernel G)(F:Forest S.ratio)(k:Key F G)(j:Cabin G c)(he:bracken S A F k j ≠ 0)(w:Lips G c f):Shy S (fkey F k) w (hatch j::w):=by
 constructor; · exact le_rfl
 · exact (Nat.zero_add _).le
 intro x; have ht:=local_travel S (Sum.inl k.1.val) (Sum.inr j.1) (bracken_keeps h A F k j he) x
 rw [steps_cons, show (hatch j : Ink G c f).1=Sum.inr j.1 from rfl,show (fkey F k).1=Sum.inl k.1.val from rfl]; linarith

-- idempotent cardinal charge used in the three l1 sums. NOT a gate in the
-- response. This is support of a coefficient for geometry owners.
def pinball {I : Type}(D:Finset I)(i:I):ℝ:=if i∈D then 1 else 0
lemma count_pin {I:Type}[Fintype I](D:Finset I):∑ i,pinball D i=D.card:=by
 simp only [pinball,← Finset.sum_filter]
 rw [show Finset.univ.filter (fun i=> i∈D)=D by ext;simp]; simp
lemma pin_payload {K:Type}(D:Finset K)(v:ℝ)(k:K)(h:v≠0→k∈D){B:ℝ}(ht:|v|≤B):|v| ≤ pinball D k*B:=by
 by_cases he:k∈D; · simpa [pinball,he]
 rw [of_not_not (show ¬ v ≠ 0 from fun hz=>he (h hz)),abs_zero,pinball,if_neg he,zero_mul]

def cards (P:Patch)(G:Gauge):ℝ:=cap (2*aperture P) rimCount*Fintype.card G.ColorIndex
lemma cards_nonneg(P:Patch)(G:Gauge):0≤cards P G:=by unfold cards; positivity
lemma sum_cards (S:StepData c f)(D:Finset (Rim c f))(hm:D.card ≤ cap (2*aperture S.patch) rimCount):∑ i:Ink G c f,pinball D i.1 ≤ cards S.patch G :=by
 rw [Fintype.sum_prod_type]; simp_rw [Finset.sum_const,nsmul_eq_mul]; rw [← Finset.mul_sum,count_pin,Finset.card_univ,mul_comm _ (D.card:ℝ)]; unfold cards; gcongr
lemma sum_cabin (S:StepData c f)(k:Rim c f): ∑ i:Cabin G c,pinball (home S k) (hatch i).1 ≤ cards S.patch G:=by
 have ht:=sum_cards (G:=G) S (home S k) (home_count S k)
 simp only [Fintype.sum_prod_type,hatch,Finset.sum_const,nsmul_eq_mul] at * -- expands edge sums c & f. sum over Rim then commute
 rw [Fintype.sum_sum_type] at ht; conv at ht=> lhs; rhs; rw [Fintype.sum_prod_type]
 refine le_trans ?_ ht
 apply le_add_of_nonneg_left
 exact Finset.sum_nonneg (fun i _=> mul_nonneg (by positivity) (by unfold pinball; split<;>simp))
lemma shy_friends (A:ChartRatio G)(P:Patch)(K:KernelChoices)(n:ℕ):∃ C:ℝ,0≤C ∧ ∀{c f:Side}(S:StepData c f)(F:Forest S.ratio),S.patch=P→S.kernel=K→S.patch.Branches S.kernel G→∀ (k:Key F G)(w:Lips G c f),w.length≤n→ Signed (Shy S (fkey F k) w) (friends F A k w) C:=by
 obtain ⟨B,hB,H⟩:=bracken_bound A P K
 refine ⟨n+(cards P G)*B,by have :=cards_nonneg P G; positivity,fun {c f} S F hP hK he k w hw=>?_⟩
 subst P K
 apply Signed.minus ((shy_del S _ _).enrich (fun _=>id) (by exact_mod_cast hw))
 let D:=home S (fkey F k).1
 let C (i:Cabin G c):=pinball D (hatch (f:=f) i).1*B
 let b:= bracken S A F k
 let l(i:Cabin G c):= hatch (f:=f) i::w
 let q:=Shy S (fkey F k) w
 have hs(i:Cabin G c):Signed q (single (l i) (b i)) (C i):=by
   by_cases ht:b i=0
   · rw [ht,Finsupp.single_zero]; apply Signed.enrich (Signed.zero q) (fun _=>id); unfold C pinball; split<;>positivity
   exact (Signed.single q (shy_equity S he F k i ht w) _).enrich (fun _=>id) (pin_payload D (b i) _ (bracken_keeps he A F k i) (H S F rfl rfl k i))
 refine (Signed.sum _ _ C (fun i _=>hs i)).enrich (fun _=>id) ?_
 unfold C; rw [←Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (sum_cabin S _) hB

structure Joy (S:StepData c f)(j:Ink G c f)(n:ℕ)(w v:Lips G c f):Prop where
 lo : v.length ≤ w.length+n
 pays (x:Site f): steps (S:=S) x v ≤ steps (S:=S) x w+n*((separation x (atRim S j.1):ℝ)+2*aperture S.patch)
lemma Joy.grows {S:StepData c f}{j:Ink G c f}{n m:ℕ}(he:n≤m){w v:Lips G c f}(h:Joy S j n w v): Joy S j m w v:=by
 obtain ⟨h1,h2⟩:=h
 refine ⟨by omega,fun x=> le_trans (h2 x) ?_⟩; gcongr
lemma steps_bound (S:StepData c f)(x:Site f)(u:Lips G c f)(B:ℝ)(h:∀ i∈u,(separation x (atRim S i.1):ℝ) ≤ B): steps (S:=S) x u ≤ u.length*B:=by
 induction u with
 | nil=> simp [steps]
 | cons i u ih=>
   rw [steps_cons,List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm _ B]; exact add_le_add (h i (by simp)) (ih fun i hi=>h i (by simp [hi]))
lemma joy_attach (S:StepData c f)(j:Ink G c f)(n:ℕ){u:Lips G c f}(hu:u.length=n)(h:∀ i∈u,i.1∈home S j.1)(w:Lips G c f):Joy S j n w (u++w):=by
 refine ⟨by simp [hu,add_comm],fun x=>?_⟩; rw [steps_attach,← hu]; rw [add_comm]; exact add_le_add_right (steps_bound S x u _ (fun i hi=> local_travel S _ _ (h _ hi) x)) _
lemma pack (S:StepData c f)(D:Finset (Rim c f))(n:ℕ){B:ℝ}(he:0≤B)(b:(Fin n→Ink G c f)→ℝ)(h:∀ i,|b i|≤ B)(hq:∀ i,b i ≠0→ ∀ j,(i j).1∈D)(hs:D.card ≤ cap (2*aperture S.patch) rimCount):∑ i, |b i| ≤ (cards S.patch G)^n * B :=by
 let U(i:Ink G c f):=pinball D i.1
 have hU(i:Ink G c f):0≤U i:=by unfold U pinball; split<;>simp
 calc
   _ ≤ ∑ i,(∏ j,U (i j))*B:= Finset.sum_le_sum (fun i _=> by
      by_cases ht:b i=0
      · rw [ht,abs_zero]; exact mul_nonneg (Finset.prod_nonneg (fun j _=>hU (i j))) he
      simpa only [U,pinball, if_pos (hq i ht _),Finset.prod_const_one,one_mul] using (h i))
   _ = (∏ _j:Fin n,∑ i:Ink G c f, U i)*B:=by rw [← Finset.sum_mul,Fintype.prod_sum]
   _ ≤ _:=by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Finset.sum_nonneg (fun i _=>hU i)) (sum_cards S D hs) _) he
lemma signed_tether (S:StepData c f)(j:Ink G c f)(w:Lips G c f)(n:ℕ){B:ℝ}(he:0≤B)(b:(Fin n→Ink G c f)→ℝ)(h:∀ i, |b i|≤B)(hq:∀ i,b i ≠0→ ∀ l,(i l).1∈home S j.1):Signed (Joy S j n w) (tether b w) ((cards S.patch G)^n *B):=by
 let D:=home S j.1; let q:=Joy S j n w
 have ht(i:Fin n→Ink G c f):Signed q (single (List.ofFn i ++ w) (b i)) |b i|:=by
   by_cases hv:b i=0; · simpa only [hv,single_zero,abs_zero] using Signed.zero q
   refine Signed.single q (joy_attach S j n (List.length_ofFn) (fun x hx=> ?_) w) _
   obtain ⟨l,hl⟩:=List.mem_ofFn.mp hx; rw [← hl]; exact hq i hv _
 exact (Signed.sum Finset.univ _ (fun i=>|b i|) fun i _=> ht i).enrich (fun _=>id) (pack S D n he b h hq (home_count S j.1))
lemma joy_leap (A:ChartRatio G)(P:Patch)(K:KernelChoices)(n:ℕ):∃ C:ℝ,0≤C ∧ ∀{c f:Side}(S:StepData c f),S.patch=P→S.kernel=K→∀(j:Ink G c f)(w:Lips G c f),Signed (Joy S j (n+1) w) (leap (A:=A) S j n w) C:=by
 obtain ⟨B,hB,H⟩:=canopy_bound P K (n+1) G
 obtain ⟨D,hD,h⟩:=elm_bound A (n-1)
 refine ⟨(cards P G)^(n+1)*B+(cards P G)^(n-1)*D,by have :=cards_nonneg P G; positivity,fun {c f} S hP hK j w=>?_⟩
 subst P K
 apply Signed.minus (signed_tether S j w (n+1) hB (canopy S j) (H S rfl rfl j) (canopy_keeps S j))
 refine Signed.enrich (p:=Joy S j (n-1) w) (K:=(cards S.patch G)^(n-1)*D) ?_ (fun _=> Joy.grows (by omega)) le_rfl
 exact signed_tether S j w (n-1) hD (elm A j) (h j) (fun i he a=> by rw [elm_keeps A j i he]; exact home_self S j.1)
end YM.AveragedStep.SD
