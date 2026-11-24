import YM.Comparison.Density.Fusing.Composing

/-!
Coexistence of address alphabets. Incoming residuals at a different
read support MUST remain on that address until an actual re-expression
occurs; take sums by a bijection with ℕ. Never sum Boolean tests into
new alternatives on different supports without a merger.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Fusing
open Testing Markers Registers Marker RG Lattice Function Finset MeasureTheory Filter Wilson
open Pert.Attach Push.AbsoluteSums Assembly
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {V : Type} [DecidableEq V] {R : Census V} {n : Side} {G : Gauge}
variable {X : V → Type} [∀ v, NormedAddCommGroup (X v)] [∀ v, NormedSpace ℂ (X v)]

section Vacuum
variable {P Q : Activities G n} {B : BudgetPoint}

-- abstract regular chains can be grafted before reset. Leaves forced
-- slots of P only; Q can be the discrepancy's regular log family.
abbrev rubric : ℕ≃(ℕ⊕ℕ) := Equiv.natSumNatEquivNat.symm

def weave (P Q : Activities G n) : Activities G n := ⟨Sum.elim P.reg Q.reg ∘ rubric, P.forced, Sum.elim P.E Q.E ∘ rubric, P.K⟩

def Art (P : Activities G n) (B : BudgetPoint) := ∀ i, B.Regular (P.reg i).support (P.E i)

lemma weave_art (h : Art P B) (hp : Art Q B) : Art (weave P Q) B := by
  intro i; dsimp [weave]; cases rubric i; exact h _; exact hp _
lemma weave_bound {r s : ℝ} (h : P.EBound B r) (he : Q.EBound B s) : (weave P Q).EBound B (r+s):= by
  obtain ⟨a,ha,h⟩:=h; obtain ⟨b,hb,he⟩:=he; let R := weave P Q
  refine ⟨Sum.elim a b ∘ rubric,fun i=>?_,fun x=>?_⟩
  · dsimp [weave]; cases rubric i; exact ha _; exact hb _
  have hx := h x; have hy:= he x
  let c:= fun i=> if (Sum.elim P.reg Q.reg i).site=x then B.mass ((Sum.elim P.reg Q.reg i).support) (Sum.elim a b i) else 0
  exact budget_pull rubric rubric.injective (split_budget (f:=c) hx hy)
lemma weave_summed {r s : ℝ} (h : P.EBound B r) (he : Q.EBound B s) (U) :
    (weave P Q).additive B U=P.additive B U+Q.additive B U := by
  -- no affine/value nullity needed for summability
  have hx (P : Activities G n) (r : ℝ) (hr : P.EBound B r) : Summable fun i=> P.regularOccurrence B i U:= by
    obtain ⟨b,hb,H⟩:=Activities.E_total hr
    refine Summable.of_norm (hb.of_nonneg_of_le (fun i=>norm_nonneg _) fun i=> ?_)
    unfold Activities.regularOccurrence; by_cases hi:Healthy B.threshold (P.reg i).support U
    · rw [masked_eq _ _ _ _ hi]; exact (H i).2 _ hi [] (Nat.zero_le _) (by simp)
    rw [masked_ne _ _ _ _ hi,norm_zero]; exact (H i).1
  let f:= fun i=> masked B.threshold ((Sum.elim P.reg Q.reg i).support) (Sum.elim P.E Q.E i) U
  exact (rubric.hasSum_iff.mpr (HasSum.sum (f:=f) ((hx _ _ h).hasSum) ((hx _ _ he).hasSum))).tsum_eq

def weave_moves {x s} (h : P.Moves x s) (e : Q.Moves x s) : (weave P Q).Moves x s := by
  let p:= Equiv.sumCongr h.ep e.ep
  refine ⟨(rubric.trans p).trans rubric.symm,h.kp,?_,?_,h.forced_support,h.forced_inventory,h.forced_tests,?_,h.valuesK⟩
  · intro i; simp only [weave, Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply]; cases rubric i; exact h.reg_site _; exact e.reg_site _
  · intro i; simp only [weave, Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply]; cases rubric i; exact h.reg_support _; exact e.reg_support _
  intro i U; simp only [weave, Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply]; cases rubric i; exact h.valuesE _ U; exact e.valuesE _ U
end Vacuum

section Marks
variable (A D : Registers R X G n)
def alongside : Registers R X G n where
  static i := Sum.elim (A.static ⟨i.1,·⟩) (D.static ⟨i.1,·⟩) (rubric i.2)
  constant i := Sum.elim (A.constant ⟨i.1,·⟩) (D.constant ⟨i.1,·⟩) (rubric i.2)
  sites i := Sum.elim (A.sites ⟨i.1,·⟩) (D.sites ⟨i.1,·⟩) (rubric i.2)
  body i := Sum.elim (A.body ⟨i.1,·⟩) (D.body ⟨i.1,·⟩) (rubric i.2)

variable {A D} {B : BudgetPoint} {O : Readers V X n} {w : V→ ℝ}
lemma alongside_layout (h : Layout B O A) (he : Layout B O D) : Layout B O (alongside A D) := by
  constructor <;> intro i <;> dsimp only [alongside]
  · cases hz:rubric i.2 with
    | inl j=> exact fun v hv=> h.assigns (i.1,j) v hv
    | inr j=> exact fun v hv=> he.assigns (i.1,j) v hv
  · cases hz:rubric i.2 with
    | inl j=> exact fun v hv=> h.contiguous (i.1,j) v hv
    | inr j=> exact fun v hv=> he.contiguous (i.1,j) v hv
  · cases rubric i.2; next j=> exact h.fixed (i.1,j)
    next j=> exact he.fixed (i.1,j)
  · cases rubric i.2; exact h.static _; exact he.static _
  · intro U; cases rubric i.2; next j=> exact h.extendsAt (i.1,j) U
    next j=> exact he.extendsAt (i.1,j) U
  · intro U; cases rubric i.2; exact h.track _ U; exact he.track _ U
  intro x; cases rubric i.2; exact h.smooth _ x; exact he.smooth _ x

private lemma dispatch {f : (Address R) ⊕ (Address R) → ℝ} {u v : ℝ} (hu:SumBudget (fun i:Address R=>f (.inl i)) u)
    (hv:SumBudget (fun i:Address R=>f (.inr i)) v): SumBudget f (u+v):= by
  apply budget_of_sum (Sum.rec hu.1 hv.1); intro s; rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight]
  exact add_le_add (budget_sum hu _) (budget_sum hv _)

private lemma delivery {J K : Address R → Support n} {a b : Address R→ℝ} {u v : ℝ} (h : Freight B w J a u) (hp : Freight B w K b v) :
    Freight B w (fun i=>Sum.elim (J ⟨i.1,·⟩) (K ⟨i.1,·⟩) (rubric i.2))
      (fun i=>Sum.elim (a ⟨i.1,·⟩) (b ⟨i.1,·⟩) (rubric i.2)) (u+v) := by
  let q : Address R ≃ ((Address R) ⊕ (Address R)):=
    (Equiv.prodCongr (Equiv.refl _) rubric).trans (Equiv.prodSumDistrib ..)
  refine ⟨add_nonneg h.1 hp.1,fun i=> ?_,fun i=>?_⟩
  · dsimp only; cases hz:rubric i.2; exact h.2.1 _; exact hp.2.1 _
  have ht := budget_pull q q.injective (dispatch (f:=Sum.elim _ _) (h.2.2 i) (hp.2.2 i)) -- elaborator sees only inl
  convert ht using 2 with x
  obtain ⟨j,i⟩:=x; simp only [q,Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply]; cases rubric i <;> rfl

omit [∀ v, NormedSpace ℂ (X v)] in
lemma alongside_budget {a b c d : ℝ} (h : Budget B O A w a b) (hp : Budget B O D w c d) :
    Budget B O (alongside A D) w (a+c) (b+d) := by
  constructor
  · obtain ⟨e,he,H⟩:=h.globalCosts; obtain ⟨f,hf,Hf⟩:=hp.globalCosts
    refine ⟨_,delivery he hf,fun x hx i=>?_⟩; dsimp only [alongside]; cases rubric i.2; exact H x hx _; exact Hf x hx _
  obtain ⟨e,he,H⟩:=h.bodyCosts; obtain ⟨f,hf,Hf⟩:=hp.bodyCosts
  refine ⟨_,delivery he hf,fun x hx i v hv=>?_⟩; dsimp only [alongside]; cases rubric i.2; exact H x hx _ _ hv; exact Hf x hx _ _ hv

lemma alongside_log [Fintype V] {a b c d : ℝ} (h : Budget B O A w a b) (hp : Budget B O D w c d) (he : A.Layout B O) (hh : D.Layout B O) (hw : ∀ i,0<w i) (x : Cross X) (U) :
    (alongside A D).log B x U=A.log B x U+D.log B x U := by
  ext i; by_cases hi:i.val.Nonempty
  · let k : Multi.Hot R:= ⟨_,hi⟩; rw [Poly.part_plus]; simp_rw [← show k.val=i from rfl, alive,ledger]
    rw [orderZero, orderZero, orderZero]
    have ht : (∑' i:ℕ, (alongside A D).constant (k,i) x)=(∑' i:ℕ,A.constant (k,i) x)+∑' i:ℕ,D.constant (k,i) x:= by
      let f:=fun j=> (Sum.elim (A.constant ⟨k,·⟩) (D.constant ⟨k,·⟩) j) x
      exact (rubric.hasSum_iff.mpr (HasSum.sum (f:=f) ((glob_series hw he h x k).hasSum) ((glob_series hw hh hp x k).hasSum))).tsum_eq
    rw [ht,add_add_add_comm]; refine congrArg₂ _ rfl ?_ -- adjust
    let f:= fun j=> masked B.threshold (Sum.elim (A.sites ⟨k,·⟩) (D.sites ⟨k,·⟩) j) (Sum.elim (A.body ⟨k,·⟩) (D.body ⟨k,·⟩) j x) U
    exact (rubric.hasSum_iff.mpr (HasSum.sum (f:=f) (((dom hw he h x k).summable U).hasSum) (((dom hw hh hp x k).summable U).hasSum))).tsum_eq
  · rw [show i=R.quiet from Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp hi)]; simp only [Poly.part_plus, baseline,zero_add]
end Marks
end YM.Comparison.Density.Fusing
