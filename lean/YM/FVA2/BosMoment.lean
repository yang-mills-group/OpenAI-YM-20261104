import YM.FVA2.Evaluate
import YM.PertExtension.GaussianIBP

/-!
# Wick from `Shot` equals Gaussian integral on all polynomials
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Bosonic
open Function Set Filter Finset Matrix MeasureTheory MS MS.Swirl MS.Book MS.Koszul MS.Puff
open MS.Cylinder MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal PertExtension GaussianScore
open scoped Topology ContDiff Classical
variable {A : Type} [Fintype A]

/-- Lists of positions in an ordinary point monomial. Use once per factor. -/
def row (x:List A) : Raw A ℂ := x.foldr (fun x p=> product (plain A) (atLetter x) p) (coin 1)
local notation "ε"=> plain A
local infixl:70 " ⋄ "=> product (plain A)

omit [Fintype A] in
lemma append_row (a:A)(l:List A) : row (a::l)=atLetter a ⋄ row l := rfl
omit [Fintype A] in
lemma acceptable (x:List A) : Symm ε (row x) ∧ row x∈Mini _ := by
  induction x with
  | nil=> exact ⟨coin_symm _,minH (coinN _)⟩
  | cons a l IH=> exact ⟨(speaks_s _).times IH.1,miPair (minH (letterN a)) IH.2⟩

def rows : Submodule ℂ (Raw A ℂ) := Submodule.span ℂ (Set.range row)
lemma generate (F:Raw A ℂ) (hs:Symm ε F) (hv:F∈ Mini _): F∈ rows := by
  have he (l:List A) : row l∈ rows:=Submodule.subset_span (Set.mem_range_self _)
  apply spanning rows F hs hv
  · intro c; rw [show coin (A:=A) c=c • row ([]:List A) from funext fun l=> by cases l <;> simp [row,coin]]; exact rows.smul_mem _ (he _)
  intro V _ _ ht i
  exact (show Submodule.span ℂ (Set.range row)≤Submodule.comap (product ε (atLetter i)) rows from
    Submodule.span_le.mpr fun q ⟨x,h⟩=>h ▸ he (i::x)) ht

-- recursion tagged
omit [Fintype A] in
lemma permutes {l k:List A} (h:l.Perm k) : row l=row k := by
  induction h with
  | nil=>rfl
  | cons i h H=> simp only [append_row,H]
  | swap i j l => simp_rw [append_row]; rw [← times_assoc, ← times_assoc, show product ε (atLetter j) (atLetter i) = _ from Pure.central (p:=ε) (speaks_p j) (atLetter i)]
  | trans h ht ih ih' => exact ih.trans ih'

section Tagged
variable {I:Type} [DecidableEq I] (p:I→A) (T:Finset I)
def tag := row (T.toList.map p)
omit [Fintype A] in
lemma tag_more (i:I)(h:i∉ T) : tag p (insert i T)=atLetter (p i) ⋄ tag p T := by
  unfold tag; rw [← append_row]; exact permutes ((toList_insert h).map p) -- needs h
lemma valuate (x:A→ℂ): eval x (tag p T) = ∏ i∈T,x (p i) := by
  induction T using Finset.induction_on with
  | empty => simp [tag,row, value_constant]
  | insert b T hb IH=> rw [tag_more p T b hb,eval_letter_prod x _ (tag p T) (acceptable _).2, prod_insert hb, IH]

omit [Fintype A] in
lemma tag_D (i:A) : D i (tag p T)=∑ j∈T, if p j=i then tag p (T.erase j) else 0 := by
  induction T using Finset.induction_on with
  | empty=> simp [tag,row, D, coin]; rfl
  | insert a T ha IH=>
    rw [tag_more p T a ha,D_product,IH, sum_insert ha,show ε i=false from rfl, sign_id,erase_insert ha];
    congr 1
    · split_ifs with h; · rw [h,hear,coin_product,one_smul]
      rw [unheard _ (Ne.symm h),map_zero]; rfl
    rw [map_sum]; apply Finset.sum_congr rfl; intro j hj
    rw [show (insert a T).erase j = insert a (T.erase j) from erase_insert_of_ne (Ne.symm (ne_of_mem_of_not_mem hj ha))]
    split_ifs; rw [tag_more p (T.erase j) a (fun h=> ha (mem_of_mem_erase h))]; exact map_zero _
end Tagged

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (P:Law E) (u:A→ Module.Dual ℝ E)
  (K:Grain A)(hk:∀ i j:A, Chill K i j=(P.wick (u i) (u j):ℂ))
  (μ:Measure E)[μ.HasTemperateGrowth][μ.IsAddRightInvariant][NeZero μ]

noncomputable def value (F:Raw A ℂ)(x:E) := eval (fun i:A=>(u i x:ℂ)) F
structure Meaning (F:Raw A ℂ) : Prop where
  reads : Integrable (fun x=> (P.kern x : ℂ) * value u F x) μ
  equal : (∫ x, (P.kern x:ℂ) * value u F x ∂μ) = Complex.ofReal (∫ x,P.kern x ∂μ) * View K F

include hk
lemma monomial {I:Type} [DecidableEq I] (p:I→A) (T:Finset I) : Meaning P u K μ (tag p T) := by
  have hw i j : P.wick (u i) (u j) = P.wick (u j) (u i) := by
    simpa only [P.applies,Law.wick] using P.turns (P.inverse (u j)) (P.inverse (u i))
  have hs : Cog.Sym ε K := by
    intro i j; have ht := (hk i j).trans ((congr_arg Complex.ofReal (hw i j)).trans (hk j i).symm)
    exact (mul_left_cancel₀ (two_ne_zero : (2:ℂ)≠0) ht).trans (by change _ = cross false false *_; rw [cross_false,one_mul])
  let L:=P.kern
  let f(x:E)(T:Finset I):=Law.product (u∘p) T x
  have he : View K (tag p T) = (P.average μ (Law.product (u∘p) T):ℂ) := by
    induction T using Finset.strongInduction with
    | H T IH=>
      by_cases he:T.Nonempty
      · obtain ⟨i,hi⟩ := he
        let S := T.erase i
        have hS : i∉S := Finset.notMem_erase i T
        have hr : tag p T = atLetter (p i) ⋄ tag p S:= by
          nth_rw 1 [← Finset.insert_erase hi]; exact tag_more p S i hS
        have hy : Law.product (u∘p) T=fun x=> f x S * u (p i) x:= by
          nth_rw 1 [← Finset.insert_erase hi]; funext x; exact (Finset.prod_insert hS).trans (mul_comm ..)
        rw [hr,hy,ibpV (F:=tag p S) _ (fun _ _ _=>rfl : Clear ε K) hs (acceptable _).1 (acceptable _).2, show P.average μ _= _ from P.recursion μ (u (p i)) (u∘p) S,Complex.ofReal_sum]
        simp_rw [ tag_D,map_sum,Finset.mul_sum ]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j hj=>?_
        rw [Finset.sum_eq_single_of_mem (p j) (mem_univ _), if_pos rfl,IH (S.erase j) (Finset.ssubset_of_subset_of_ssubset (erase_subset ..) ( Finset.erase_ssubset hi )), hk, Complex.ofReal_mul, mul_comm]; rfl
        intro b _ h; rw [if_neg (Ne.symm h), map_zero, mul_zero]
      rw [Finset.not_nonempty_iff_eq_empty.mp he]; unfold tag; rw [Finset.toList_empty,List.map_nil]; rw [show row ([]:List A)=coin (1:ℂ) from rfl,minView, show Law.product (u∘p) ∅=1 from funext fun _=> by simp [Law.product],P.empty]; simp
  have ht : (fun x=> (P.kern x:ℂ) * value u (tag p T) x) = fun x=>(↑(f x T*L x):ℂ) := by
    funext x; rw [value, valuate]; unfold f L Law.product; push_cast; rw [mul_comm]; rfl
  have hu:=P.integrable_entry μ (Law.product_bound (u∘p) T) (Law.product_cont (u∘p) T)
  refine ⟨ht ▸ hu.ofReal,?_⟩
  rw [ht,he,integral_complex_ofReal,Law.average]
  have hpos : (∫ x,P.kern x ∂μ)≠0 := by
    have H:=P.integrable_entry (A:=1) μ (Series.Zone.Invoice.const (1:ℝ)) continuous_const
    rw [one_mul] at H; exact (integral_exp_pos H).ne'
  rw [←Complex.ofReal_mul, mul_comm (∫ x,P.kern x ∂μ),div_mul_cancel₀ _ hpos]; rfl

omit hk [MeasurableSpace E] [BorelSpace E] [Fintype A] in
lemma list_tag (l:List A): row l=tag l.get (Finset.univ:Finset (Fin l.length)) := by
  unfold tag
  have he : ((Finset.univ:Finset (Fin l.length)).toList).Perm (List.finRange l.length) := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    exact nodup_toList _
    exact List.nodup_finRange _
    simp
  rw [permutes (he.map _)]
  simp

theorem wick_eval (F:Raw A ℂ) (hs:Symm ε F) (hr:F∈ Mini _): Meaning P u K μ F := by
  let D(p:Raw A ℂ)(x:E):= (P.kern x:ℂ) * value u p x
  refine Submodule.span_induction (p:=fun F _ => Meaning P u K μ F) ?_ ?_ ?_ ?_ (generate F hs hr)
  · rintro x ⟨l,rfl⟩; rw [list_tag l]; exact monomial P u K hk μ _ _
  · constructor
    · simp [value]
    simp [value]
  · intro x y _ _ hf hp
    have hx : D (x+y)=D x+D y:= funext fun k=> by simp only [D,value,map_add,mul_add];rfl
    refine ⟨show Integrable (D (x+y)) μ from hx ▸ hf.reads.add hp.reads,?_⟩
    change (∫ k,D (x+y) k ∂μ)=_
    rw [hx,show ∫ k,(D x + D y) k ∂μ = _ from integral_add hf.reads hp.reads, hf.equal,hp.equal,map_add,mul_add]
  intro c x _ hx
  have hv : D (c • x)=c • D x:= funext fun k=> by simp only [D,value,map_smul, Pi.smul_apply,smul_eq_mul];rw [mul_left_comm]
  refine ⟨show Integrable (D (c • x)) μ from hv ▸ hx.reads.smul _,?_⟩
  change (∫ k,D (c • x) k ∂μ)=_
  rw [hv,show ∫ k,(c • D x) k ∂μ = c • (∫ k,D x k ∂μ) from integral_smul c (D x),
    show ∫ k,D x k ∂μ=_ from hx.equal, map_smul]; exact (mul_left_comm ..)
end YM.FVA2.Bosonic
