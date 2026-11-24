import YM.RG3.Forms.Partners
import YM.Extra.ITERATION_NO_LOSS.Sums

/-!
# Marked log-book changes with common reserved profiles

Separate from carrying the K polynomials. Reindex is literal, without
changing the column dictionary of the supplying witness. Includes cheap
invoice (unit) and caption channels; retain global constants also when they
originated on a good mask, as in Common Compensate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script
open Function Wilson RG Source Extra.Trajectories Marker Overlay Finset Lattice RG3.Forms RG3.Press Extra.Multi Push.AbsoluteSums Extra.Iteration
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {α : Type*} {V : Type*} [DecidableEq V] {R : Census V} {n : Side} {G : Gauge} (ζ : V→Site n)

def expense (B : ℕ) (a : ℝ)(X : Support n)(c : ℝ):= Real.exp (a*(coverNumber B X))*c

def per (B : ℕ) (a : ℝ) (w : V→ℝ)(pp : α→R.Mode) (X : α→Support n) (f : α→ℝ)(s : V) (x : α):=
    if s∈(pp x).val then Poly.toll w (pp x)*expense B a (X x) (f x) else 0
variable {B : ℕ} {a C : ℝ} {w : V→ℝ} {X : α→Support n} {f : α→ℝ} {j : α→R.Mode}
lemma per_nn (h : ∀ i,0 ≤ w i)(hf : ∀ i,0 ≤ f i)(i : α) (x : V): 0 ≤ per B a w j X f x i:= by
  unfold per; split
  · apply mul_nonneg (prod_nonneg (fun s (he:s∈(j i).val)=> h s)); unfold expense; exact mul_nonneg (Real.exp_pos _).le (hf _)
  exact le_rfl
lemma per_le (h : ∀ i,0 < w i)(hf : ∀ i,0 ≤ f i){a'}(ha : a ≤ a') (i : α) (x : V):
    per B a w j X f x i ≤ per B a' w j X f x i:= by
  unfold per expense; split
  · gcongr; exact (Poly.worth h _).le; exact hf i
  rfl

lemma label_budget (h : ∀ i,0<w i) (hf : ∀ i,0≤f i) {a':ℝ} (ha:a≤a')
    (H : ∀ x, SumBudget (per B a' w j X f x) C) x: SumBudget (per B a w j X f x) C :=
  budget_mono (H x) (fun i=> per_nn (fun i=> (h i).le) hf i x) (fun i=> per_le h hf ha i x)

/-- Full marked log layout, irrespective of whose forces it will be multiplied
with when dressing. All additional scalars emitted with caption receipts. -/
structure Edition (R : Census V) (G : Gauge) where
  pure : V → ℂ
  home : ℕ → Support n
  pins : ℕ → R.Mode
  song : ℕ → Config G n → ℂ
  footer : Captions R n
  -- reference ζ
  mentored : ∀ i, ζ i=ζ i := fun _=>rfl

namespace Edition
variable {ζ} (q q' : Edition ζ R G)

/-- Layout of a caller's literal log coordinates, fixing its origin data to
our ζ via caller lemma. -/
def read (P : Rep G n) (d : Deck R P) (v : V→Site n) : Edition v R G where
  pure := d.contents.units
  home:=d.contents.support
  pins:=d.contents.rays
  song:=d.contents.H
  footer:=d.captions

/-- Keep old flags & force alternatives. -/
def scribe {P:Rep G n}(d : Deck R P) : Deck R P := {
    contents := { d.contents with
      origins := ζ
      units := q.pure
      support := q.home
      rays := q.pins
      H := q.song }
    captions := q.footer }

lemma scribe_id {P:Rep G n}(d:Deck R P)(hz:d.contents.origins=ζ): (read P d ζ).scribe d=d:= by
  unfold scribe read; rw [← hz]

structure Principle (p : BudgetPoint) : Prop where
  hot i : (q.pins i).val.Nonempty
  rem i s : s∈ (q.pins i).val → ζ s∈q.home i
  reg i : p.Regular (q.home i) (q.song i)
  vertical : q.footer.Sound ζ

/-- Keep numeric per-item vouchers exposing with a possibly stronger exponent
but ALWAYS using same p derivative/threshold conventions. Later may want
these SAME vouchers valid at every held testing position. -/
structure Grant (p : BudgetPoint) (w : V→ℝ)(a u c g:ℝ) (f : ℕ→ℝ) : Prop where
  one i : w i * ‖q.pure i‖ ≤ u
  nn i : 0 ≤ f i
  pay i s : s∈(q.pins i).val → p.supBounds (ζ s) (q.home i) (q.song i) (f i)
  more i : SumBudget (per p.B a w q.pins q.home f i) c
  captions i : SumBudget (per p.B a w q.footer.tag q.footer.cover (fun j=>‖q.footer.value j‖) i) g

variable {P : Rep G n} {q}
abbrev read_principle {d:Deck R P}(h:d.Active)(hz:d.contents.origins=ζ) : (read P d ζ).Principle P.p:= by
  subst ζ
  exact ⟨h.articles.proper, h.articles.pins,h.articles.regular,h.captions⟩

abbrev principle {d:Deck R P} (h : q.Principle P.p) : Article.Contents (q.scribe d).contents:=⟨h.hot,h.rem,h.reg⟩
lemma grant {d:Deck R P} {u c Y : ℝ}{f:ℕ→ℝ}(h : q.Grant P.p w a u c Y f) (hw : ∀ i,0<w i)(ha : P.p.supportExponent ≤ a):
    Article.LogBounds (q.scribe d).contents w u c ∧ q.footer.Paid w P.p Y:= by
  refine ⟨⟨h.one, f,fun i=>⟨h.nn _,h.pay _⟩,fun i=>?_⟩,⟨fun i=>?_⟩⟩
  · exact label_budget hw h.nn ha h.more i
  exact label_budget hw (fun _=>norm_nonneg _) ha h.captions i

lemma authorized {d:Deck R P}(hz:d.contents.origins=ζ)(h : q.Principle P.p)(he:d.Active):(q.scribe d).Active:=by
  subst ζ
  exact ⟨⟨h.hot,h.rem,h.reg,he.articles.occurs,he.articles.retained,he.articles.inspects,he.articles.keeps,he.articles.meas,he.articles.invi⟩,h.vertical⟩
lemma funds {d:Deck R P} {u c Y t' b a0 u0 c0 : ℝ}{f:ℕ→ℝ}(h : q.Grant P.p w a u c Y f) (ha : P.p.supportExponent ≤ a)(hf:d.Budget w u0 c0 t' b a0):(q.scribe d).Budget w u c t' b Y:=by
  obtain ⟨⟨i,g⟩,t⟩:=grant (d:=d) h hf.radial.pure ha
  exact ⟨⟨hf.radial.pure,i,hf.radial.factor,g,hf.radial.hits⟩,t⟩
lemma affords {d:Deck R P} {u c d' b Y : ℝ}(h:d.Budget w u c d' b Y)(hz:d.contents.origins=ζ) : ∃f:ℕ→ℝ,(read P d ζ).Grant P.p w P.p.supportExponent u c Y f:=by
  subst ζ; obtain ⟨f,H,hf⟩:=h.radial.bulk
  exact ⟨f,h.radial.localU,fun i=> (H i).1,fun i=>(H i).2,hf,h.captions.budget⟩

variable (q)

def birth (p : BudgetPoint)(i : ℕ) (U : Config G n) := Poly.send (q.pins i) (masked p.threshold (q.home i) (q.song i) U)

def log [Fintype V] (p:BudgetPoint) (U : Config G n):= ((∑ i,Poly.send (R.fire i) (q.pure i)) + ∑' i,q.birth p i U)+q.footer.chord
lemma deck_log [Fintype V](d : Deck R P): (q.scribe d).log=q.log P.p:=rfl
lemma read_log [Fintype V](d : Deck R P)(v : V→Site n):(read P d v).log P.p=d.log:=rfl

def blend {α:Type*} (f g:ℕ→α):ℕ→α:= Sum.elim f g ∘ numbering (ℕ⊕ℕ)

def add : Edition ζ R G := {
  pure := fun i=> q.pure i+q'.pure i
  home:=blend q.home q'.home
  pins:=blend q.pins q'.pins
  song:=blend q.song q'.song
  footer:= ⟨blend q.footer.tag q'.footer.tag,blend q.footer.cover q'.footer.cover,blend q.footer.value q'.footer.value⟩ }
lemma from_left {α:Type*} (f g:ℕ→α) {i n':ℕ}(hh:numbering (ℕ⊕ℕ) i=Sum.inl n'): blend f g i=f n':=by simp [blend,hh]
lemma from_right {α:Type*} (f g:ℕ→α) {i n':ℕ}(hh:numbering (ℕ⊕ℕ) i=Sum.inr n'): blend f g i=g n':=by simp [blend,hh]

variable {q q'}
lemma principle_plus {p : BudgetPoint}(h:q.Principle p)(h':q'.Principle p) :(q.add q').Principle p:=by
  constructor
  · intro i; cases hi:numbering (ℕ⊕ℕ) i with
    | inl i=> simpa only [add,from_left _ _ hi] using h.hot i
    | inr i=> simpa only [add,from_right _ _ hi] using h'.hot i
  · intro i; cases hi:numbering (ℕ⊕ℕ) i with
    | inl i=> simpa only [add,from_left _ _ hi] using h.rem i
    | inr i=> simpa only [add,from_right _ _ hi] using h'.rem i
  · intro i; cases hi:numbering (ℕ⊕ℕ) i with
    | inl i=> simpa only [add,from_left _ _ hi] using h.reg i
    | inr i=> simpa only [add,from_right _ _ hi] using h'.reg i
  refine ⟨fun i=>?_,fun i=>?_⟩
  · cases hi:numbering (ℕ⊕ℕ) i with
    | inl i=> simpa only [add,from_left _ _ hi] using h.vertical.card i
    | inr i=> simpa only [add,from_right _ _ hi] using h'.vertical.card i
  cases hi:numbering (ℕ⊕ℕ) i with
  | inl i=> simpa only [add,from_left _ _ hi] using h.vertical.pins i
  | inr i=> simpa only [add,from_right _ _ hi] using h'.vertical.pins i

lemma budget_blend {A B : ℝ} {f g : ℕ→ℝ} (ha : SumBudget f A) (hb : SumBudget g B): SumBudget (blend f g) (A+B) := Cost.equiv _ (Cost.sum (f:=Sum.elim f g) ha hb)
lemma blended {α : Type*} [AddCommGroup α] [TopologicalSpace α] [IsTopologicalAddGroup α] [T2Space α] {f g:ℕ→α} (hf : Summable f) (hg : Summable g): Summable (blend f g) ∧ (tsum (blend f g))=tsum f+tsum g := by
  let u:=Sum.elim f g; let e:=numbering (ℕ⊕ℕ); change Summable (u∘e) ∧ _
  exact ⟨e.summable_iff.mpr (Summable.sum u hf hg), (e.tsum_eq u).trans (Summable.tsum_sum (f:=u) hf hg)⟩
lemma grant_plus {p:BudgetPoint}{a u c g u' c' g' : ℝ}{f f':ℕ→ℝ}(hw:∀ i,0<w i)(h : q.Grant p w a u c g f)(h':q'.Grant p w a u' c' g' f'):
    (q.add q').Grant p w a (u+u') (c+c') (g+g') (blend f f'):=by
  constructor
  · intro i; unfold add; simp only; exact ((mul_le_mul_of_nonneg_left (norm_add_le ..) (hw i).le)).trans (by rw [mul_add]; exact add_le_add (h.one i) (h'.one i))
  · intro i; cases hi:numbering (ℕ⊕ℕ) i <;> simpa only [blend,comp_apply,hi,Sum.elim_inl,Sum.elim_inr] using (by first|exact h.nn (by assumption)|exact h'.nn (by assumption))
  · intro i; cases hi:numbering (ℕ⊕ℕ) i with
    | inl i=> simpa only [add,from_left _ _ hi] using h.pay i
    | inr i=> simpa only [add,from_right _ _ hi] using h'.pay i
  · intro i; convert budget_blend (h.more i) (h'.more i) using 1
    ext j; cases he:numbering (ℕ⊕ℕ) j <;> simp only [add,per,blend,comp_apply,he,Sum.elim_inl,Sum.elim_inr]
  intro i; convert budget_blend (h.captions i) (h'.captions i) using 1
  ext j; cases he:numbering (ℕ⊕ℕ) j <;> simp only [add,per,blend,comp_apply,he,Sum.elim_inl,Sum.elim_inr]

lemma birth_blend (p:BudgetPoint)(U:Config G n): (fun j=>(q.add q').birth p j U)=blend (fun i=>q.birth p i U) (fun i=>q'.birth p i U):=by
  ext1 j; cases he:numbering (ℕ⊕ℕ) j <;> simp [birth,add,blend,he]

lemma log_plus [Fintype V](p:BudgetPoint) (U : Config G n) (h : Summable fun j=>q.birth p j U)(h' : Summable fun j=>q'.birth p j U)
    (hc:Summable fun j=>Poly.send (q.footer.tag j) (q.footer.value j)) (hc':Summable fun j=>Poly.send (q'.footer.tag j) (q'.footer.value j)):
    (q.add q').log p U=q.log p U+q'.log p U:=by
  unfold log Captions.chord
  rw [birth_blend p U,(blended h h').2,show (fun i=>Poly.send ((q.add q').footer.tag i) ((q.add q').footer.value i))=blend _ _ from ?_, (blended hc hc').2]; swap
  · funext j; cases he:numbering (ℕ⊕ℕ) j <;> simp [add,blend,he]
  have He (i : R.Mode)(a b:ℂ):Poly.send i (a+b) = Poly.send i a + Poly.send i b:= by ext; simp only [Poly.part_plus,Poly.part_send]; split <;> simp
  simp_rw [show ∀ i,(q.add q').pure i=q.pure i+q'.pure i from fun i=>rfl,He,sum_add_distrib]; abel
end Edition
end YM.RG3.Script
