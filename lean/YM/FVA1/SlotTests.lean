--
import YM.FVA1.Slot
import YM.Next.FOUNDATIONS.Regular

/-!
Linear uses of addresses on each prescribed slot. We work with operator
bounds on unit tests specified by a downstream test convention (uniform before summing
supports) and retain address stubs at the scale's roots. This is not an assertion
that passage between two different physical address conventions preserves norms
or only costs a constant.
-/

noncomputable section
set_option autoImplicit false
namespace YM.FVA1
open Finset Function Filter Lattice Wilson RG RG05.Strand Extra.Trajectories
open Marker Push.GridApprox.Nil
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {T I V:Type*}[DecidableEq V]{R:Census V}
variable [AddCommGroup T][Module ℂ T]

/-- Multilinearity and dependence on only the marked tests.
    `T` includes arbitrary function spaces of smooth tests. -/
structure SlotLinear (s:Finset V) {Y:Type*} [AddCommGroup Y][Module ℂ Y] (f:(V→T)→Y) : Prop where
  reads : ∀ (x y:V→T), Set.EqOn x y s → f x=f y
  add : ∀ i ∈ s, ∀ (x:V→T)(a b:T), f (update x i (a+b))=f (update x i a)+f (update x i b)
  hom : ∀ i∈ s, ∀ (x:V→T)(a:ℂ)(b:T), f (update x i (a • b))= a • f (update x i b)

namespace SlotLinear
variable {X Y:Type*} [AddCommGroup X][AddCommGroup Y][Module ℂ X][Module ℂ Y]
variable {s:Finset V}{f g : (V→T)→X}
lemma zero (s:Finset V): SlotLinear s (0:(V→T)→X):=by constructor <;> intros <;> simp
lemma const (v:X) : SlotLinear (∅:Finset V) (fun _:(V→T)=>v):=
  ⟨fun _ _ _=>rfl,fun i h=>False.elim (Finset.notMem_empty i h),fun i h=>False.elim (Finset.notMem_empty i h)⟩
lemma plus (a:SlotLinear s f)(b:SlotLinear s g):SlotLinear s (f+g):=by
  constructor
  · intro x y h; simp [a.reads x y h,b.reads _ _ h]
  · intro i h x v w; simp [a.add i h,b.add i h]; abel
  · intro i h x v w; simp [a.hom i h,b.hom i h,smul_add]
lemma smul (h:SlotLinear s f)(c:ℂ):SlotLinear s (c • f):=by
  constructor
  · intro x y he; simp [h.reads x y he]
  · intro i hi x v w; simp [h.add i hi,smul_add]
  · intro i hi x v w; simp only [Pi.smul_apply,h.hom i hi]; exact smul_comm _ _ _
lemma sum {f : I→(V→T)→X}(u:Finset I)(h:∀ i∈u, SlotLinear s (f i)):SlotLinear s (∑ i∈u,f i):=by
  induction u using Finset.induction_on with
  | empty => simpa only [sum_empty] using zero (X:=X) (T:=T) s
  | insert i u hi ih => rw [sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).plus (ih fun j hj=>h j (mem_insert_of_mem hj))

variable {s u:Finset V}
lemma mul {f g:(V→T)→ℂ}(hd:Disjoint s u)(hf:SlotLinear s f)(hg:SlotLinear u g): SlotLinear (s∪u) (f*g):=by
  have ha {z:(V→T)→ℂ}{v:Finset V}(he:SlotLinear v z)(i:V)(hi:i∉v)(x:V→T)(y:T):z (update x i y)=z x:=
    he.reads _ _ fun j hj=> update_of_ne (by intro h; subst j; exact hi hj) ..
  constructor
  · intro x y h; simp only [Pi.mul_apply,hf.reads x y (fun _ he=>h (mem_union_left _ he)),hg.reads x y (fun _ he=>h (mem_union_right _ he))]
  · intro i hi x a b; rcases mem_union.mp hi with h|h
    · have hh:i∉u:=fun he=> Finset.disjoint_left.mp hd h he
      simp only [Pi.mul_apply,hf.add i h, ha hg i hh, add_mul]
    have hh:i∉s:= fun he=> Finset.disjoint_left.mp hd he h
    simp only [Pi.mul_apply,hg.add i h, ha hf i hh, mul_add]
  intro i hi x a b; rcases mem_union.mp hi with h|h
  · have hh:i∉u:=fun he=> Finset.disjoint_left.mp hd h he
    simp only [Pi.mul_apply,hf.hom i h, ha hg i hh, smul_eq_mul,mul_assoc]
  have hh:i∉s:= fun he=> Finset.disjoint_left.mp hd he h
  simp only [Pi.mul_apply,hg.hom i h, ha hf i hh, smul_eq_mul]; ring

variable {sI:I→Finset V}
lemma prod {f:I→(V→T)→ℂ}(u:Finset I)(hh:(u:Set I).PairwiseDisjoint sI)(hv:∀ i∈u, SlotLinear (sI i) (f i)) :
    SlotLinear (u.biUnion sI) (∏ i∈u,f i):=by
  induction u using Finset.induction_on with
  | empty => rw [prod_empty,biUnion_empty]; exact const (V:=V) (T:=T) 1
  | insert i u hi ih =>
    rw [Finset.prod_insert hi,biUnion_insert]; refine mul ?_ (hv _ (mem_insert_self ..)) (ih (hh.subset ?_) ?_)
    · exact (disjoint_biUnion_right ..).mpr fun j hj=>
        hh (mem_insert_self ..) (mem_insert_of_mem hj) (by rintro rfl; exact hi hj)
    · exact Finset.coe_subset.mpr (subset_insert ..)
    intro j hj; exact hv j (mem_insert_of_mem hj)
end SlotLinear

variable (θ:I→R.Mode) (f:I→(V→T)→ℂ)
lemma slotDecMode (hf : ∀ i, SlotLinear (θ i).val (f i)) (s:Finset I) (a:R.Mode):
    SlotLinear a.val (fun p=>decMode θ (fun i=>f i p) s a):=by
  by_cases h:Fits θ s
  · by_cases he:unionTag θ s h=a; swap; · simp only [decMode,dif_pos h,if_neg he]; exact (SlotLinear.zero (X:=ℂ) (T:=T) a.val)
    simp only [decMode,dif_pos h,if_pos he]; rw [← he]; change SlotLinear (s.biUnion _) _
    convert SlotLinear.prod s h.1 (fun i _=>hf i)
    simp only [Finset.prod_apply]
  simp only [decMode,dif_neg h]; exact SlotLinear.zero (X:=ℂ) (T:=T) a.val

variable {Z:Type*}
def decSum [DecidableEq I][Fintype I] (g : (FreeCensus I).Mode → Z → ℂ)(φ:V→T) (a:R.Mode):Z→ℂ:=
  ∑ i, (decMode θ (fun j=> f j φ) i.val a) • (g i)

variable [DecidableEq I] [Fintype I]
omit [AddCommGroup T] [Module ℂ T] in
lemma decSum_eq (g:(FreeCensus I).Mode → Z→ℂ)(φ:V→T)(a:R.Mode)(x:Z):
    decSum θ f g φ a x=(decoder θ (fun j=> f j φ) (Poly.inject fun i=> g i x)).part a:=by
  rw [dec_part]; simp only [decSum,Finset.sum_apply, Pi.smul_apply,smul_eq_mul,mul_comm, Poly.inject, Poly.part]

lemma slot_dec (hf : ∀ i, SlotLinear (θ i).val (f i)) (g : (FreeCensus I).Mode→Z→ℂ)(a:R.Mode)(x:Z):
    SlotLinear a.val (fun p=>decSum θ f g p a x):=by
  convert SlotLinear.sum (s:=a.val) (Finset.univ:(Finset (FreeCensus I).Mode)) (fun i _=>
    SlotLinear.smul (slotDecMode θ f hf i.val a) (g i x))
  simp only [decSum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm]

open Next.Foundations
variable {G:Gauge}{n:Side}
variable {q:BudgetPoint}
omit [AddCommGroup T] [Module ℂ T] in
lemma dec_reg_bounds {g:(FreeCensus I).Mode → Config G n→ℂ} {s:Support n} (φ:V→T) (v:R.Mode)(o:Site n)
    (hb:∀ i,q.Regular s (g i))(c:I→ℝ)(Hf:∀ i,‖f i φ‖≤ c i)(u:Sheet (FreeCensus I))
    (hY:∀ i,q.supBounds o s (g i) (u i)): q.Regular s (decSum θ f g φ v) ∧ q.supBounds o s (decSum θ f g φ v) (decSheet θ c u v):=by
  unfold decSum decSheet
  apply regular_bound_sum _ _ _
  intro i _; refine ⟨regular_smul _ (hb _), ?_⟩
  have h:=bound_smul (decMode θ (fun j=> f j φ) i.val v) (hY i)
  have he : ‖decMode θ (fun i=> f i φ) i.val v‖*u i ≤ u i* decFee θ c i.val v:= (mul_le_mul_of_nonneg_right (fee_cap θ _ c Hf _ _) ((hY i).1)).trans (mul_comm ..).le
  exact ⟨h.1.trans he,fun x hx L hL d=>(h.2 x hx L hL d).trans he⟩

/-- The positions which a choice of input occurrence forces into its support.
These may include field paths, test stencils, and connecting stubs. -/
def atlas (k:(FreeCensus I).Mode) (A:I→Support n) :=
  let S := k.val
  S.biUnion A

omit [AddCommGroup T] [Module ℂ T] in
lemma dec_scoped {g:(FreeCensus I).Mode→Z→ℂ}(a:R.Mode)(x:Z)
    (A:I→Support n)(s:Support n)(φ:V→T)
    (hv:decSum θ f g φ a x ≠ 0)
    (he:∀ i:(FreeCensus I).Mode,g i x ≠0→ atlas i A ⊆ s):
    ∀ i∈ a.val, ∃ b:I,i∈(θ b).val ∧ A b⊆s:=by
  simp only [decSum,Finset.sum_apply] at hv
  obtain ⟨p,hm⟩ : ∃ p:(FreeCensus I).Mode, (decMode θ (fun i=>f i φ) p.val a) • g p x ≠0:= by
    by_contra! H; exact hv (Finset.sum_eq_zero fun i _=> H i)
  have hx : g p x≠0:= fun h'=>hm (by rw [h',smul_zero]); have hb:=he p hx
  unfold decMode at hm; split at hm; next hf =>
    split at hm; next hf'=>
      intro i hi; rw [← hf'] at hi; obtain ⟨j,hj,hk⟩:= Finset.mem_biUnion.mp hi
      exact ⟨j,hk,(Finset.subset_biUnion_of_mem _ hj).trans hb⟩
    next _ => exact (hm (zero_smul ..)).elim
  next _=> exact (hm (zero_smul ..)).elim

omit [AddCommGroup T] [Module ℂ T] in
/-- Passively retain every old required placement on actual decoded terms. -/
lemma dec_stamped {g:(FreeCensus I).Mode→Z→ℂ}(a:R.Mode)(x:Z)
    (A:I→Support n)(s:Support n)(φ:V→T)
    (hv:decSum θ f g φ a x ≠ 0)
    (he:∀ i:(FreeCensus I).Mode,g i x≠0→atlas i A ⊆s)
    (o:V→Support n)(h:∀ i:I,∀ j∈(θ i).val,o j ⊆ A i):
    ∀ i∈ a.val, o i⊆s:= by
  intro i hi; obtain ⟨b,hb,hb'⟩:=dec_scoped θ f a x A s φ hv he i hi
  exact (h b i hb).trans hb'

/-- Scalar hypotheses for retaining one anchor at a time suffice to retain
whole projected address/support tables. In this statement use anchors picked
*before* entering a term's support, not just anchors already in the support.
Empty-support alternatives must be filled in any such table; here use a variant
which only demands choices on nonempty supports. -/
lemma atlas_of_each (A:I→Support n)(i:(FreeCensus I).Mode)(s:Support n)
    (h:∀ o:I→Site n,(∀ k:I,(A k).Nonempty → o k∈A k)→∀ j∈i.val,(A j).Nonempty → o j ∈s): atlas i A ⊆s:=by
  intro x hx; obtain ⟨j,hj,hx⟩:= Finset.mem_biUnion.mp hx
  let o(k:I):Site n:=if k=j then x else if hy:(A k).Nonempty then hy.choose else 0
  have he:= h o (fun k hN=>by
    unfold o
    split
    · rename_i h; subst k; exact hx
    · exact hN.choose_spec) j hj ⟨x,hx⟩
  simpa only [o,if_true] using he

end YM.FVA1
