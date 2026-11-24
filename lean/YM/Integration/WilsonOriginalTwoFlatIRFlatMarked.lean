import YM.Integration.WilsonOriginalTwoFlatIRFlatSeries
import YM.Integration.WilsonOriginalCensusUnitEquation
import YM.QCDContinuum.Sources.Dial

/-! The ordinary product of all genuine connected faces on a full squarefree
census satisfies the native log/ordinary equation, for any coefficient ring. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRFlatMarked
open Finset Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent
open WilsonCoeffUV.Wheel.Mark
open WilsonOriginalCensusUnitEquation (blank convolution at_blank)
open scoped Classical BigOperators
variable {V A:Type}[Fintype V][DecidableEq V][CommRing A]
local notation "J" => Stock.census V
local notation "I" => {z:(J).Mode // z.val.Nonempty}
def seat (s:Finset V):(J).Mode:=⟨s,mem_univ _⟩
def field (B:Cargo (J) A)(s:Finset V):A:=B.part (seat s)
def shot (T:Finset V)(v:A)(s:Finset V):A:=if s=T then v else 0

omit [Fintype V] in
private theorem insert_shot (T:Finset V)(v:A)(M:Sac V A)(s:Finset V):
    shells (shot T v) M s=if T⊆s then v*M (s\T) else 0:=by
  by_cases sub:T⊆s
  · rw [if_pos sub,shells,sum_eq_single T]
    · simp [shot]
    · intro b _ no; simp [shot,no]
    · simp [sub]
  · rw [if_neg sub,shells]
    apply sum_eq_zero
    intro b hb
    have no:b≠T:=by rintro rfl; exact sub (mem_powerset.mp hb)
    simp [shot,no]

omit [Fintype V] in
private theorem paid (T:Finset V)(live:T.Nonempty)(v:A):
    Equation (blank+shot T v) (shot T v):=by
  have nz:T≠∅:=live.ne_empty
  have dated:dial (shot T v)=shot T (T.card • v):=by
    funext b; by_cases h:b=T <;> simp [dial,shot,h]
  refine ⟨by simp [blank,shot,nz.symm],by simp [shot,nz.symm],?_⟩
  funext s
  rw [dated,insert_shot]
  by_cases h:s=T
  · subst s; simp [dial,blank,shot,nz,nz.symm]
  · by_cases sub:T⊆s
    · have left:s\T≠∅:=by intro he; exact h (Subset.antisymm (sdiff_eq_empty_iff_subset.mp he) sub)
      have right:s\T≠T:=by
        intro eq
        obtain ⟨w,hw⟩:=live
        have yes:w∈s\T:=by rw [eq]; exact hw
        exact (mem_sdiff.mp yes).2 hw
      have some:s≠∅:=by intro z; subst s; exact nz (subset_empty.mp sub)
      simp [dial,blank,shot,h,sub,left,right,some]
    · by_cases empty:s=∅ <;> simp [dial,blank,shot,h,sub,empty,nz,nz.symm]

private theorem force (T s:Finset V)(v:A)(B:Cargo (J) A):
    field (Cargo.send (seat T) v * B) s=if T⊆s then v*field B (s\T) else 0:=by
  unfold field
  rw [Cargo.part_mul,sum_eq_single (seat T)]
  · by_cases sub:T⊆s
    · rw [if_pos sub,sum_eq_single (seat (s\T))]
      · have hit:Poly.merges (seat T) (seat (s\T)) (seat s):=by
          exact ⟨Finset.disjoint_left.mpr (fun w hw ht=>(mem_sdiff.mp ht).2 hw),union_sdiff_of_subset sub⟩
        simp [hit]
      · intro t _ miss
        have no:¬Poly.merges (seat T) t (seat s):=by
          intro hit
          apply miss; apply Subtype.ext; change t.val=s\T
          have dis:=Finset.disjoint_left.mp hit.1
          have all:T∪t.val=s:=hit.2
          ext w; simp only [mem_sdiff]; constructor
          · intro hw; exact ⟨all ▸ mem_union_right T hw,fun h=>dis h hw⟩
          · rintro ⟨hw,h⟩; rw [←all] at hw; exact (mem_union.mp hw).resolve_left h
        simp [no]
      · simp
    · rw [if_neg sub]
      apply sum_eq_zero
      intro t _
      have no:¬Poly.merges (seat T) t (seat s):=by
        intro hit; apply sub; rw [←show T∪t.val=s from hit.2]; exact subset_union_left
      simp [no]
  · intro v' _ no; simp [Cargo.part_send,no]
  · simp

def roster (F:Finset (I))(L:Finset V→A):Cargo (J) A:=
  ∏z∈F,(1+Cargo.send z.val (L z.val.val))

theorem earns (F:Finset (I))(L:Finset V→A):
    Equation (field (roster F L)) (∑z∈F,shot z.val.val (L z.val.val)):=by
  induction F using Finset.induction_on with
  | empty=>
    have unit:field (1:Cargo (J) A)=blank:=by
      funext s
      change (1:Cargo (J) A).part (seat s)=if s=∅ then 1 else 0
      rw [Cargo.one_part]; congr 1; exact propext (by simp [seat,Census.quiet,Subtype.ext_iff])
    rw [roster,prod_empty,sum_empty,unit]
    refine ⟨by simp [blank],rfl,?_⟩
    funext s; by_cases e:s=∅ <;> simp [dial,shells,blank,e]
  | @insert z F fresh ih=>
    let a:=L z.val.val
    have equiv:field (roster (insert z F) L)=shells (blank+shot z.val.val a) (field (roster F L)):=by
      funext s
      rw [roster,prod_insert fresh,add_mul,one_mul,shells_l,at_blank,Pi.add_apply,insert_shot]
      change (roster F L).part (seat s)+(Cargo.send (seat z.val.val) a*roster F L).part (seat s)=_
      exact congrArg (_+·) (force z.val.val s a (roster F L))
    rw [equiv,sum_insert fresh]
    exact convolution _ _ _ _ (paid z.val.val z.property a) ih

theorem original [IsAddTorsionFree A] (M L:Finset V→A)(law:Equation M L):
    M=field (roster univ L):=by
  have pay:=earns (univ:Finset (I)) L
  have whole:(∑z:I,shot z.val.val (L z.val.val))=L:=by
    funext s
    rw [Finset.sum_apply]
    by_cases live:s.Nonempty
    · let c:I:=⟨seat s,live⟩
      rw [sum_eq_single c]
      · simp [shot,c,seat]
      · intro t _ h; apply if_neg; intro e; apply h; exact Subtype.ext (Subtype.ext e.symm)
      · simp
    · have e:s=∅:=not_nonempty_iff_eq_empty.mp live
      subst s
      rw [law.2.1]
      apply sum_eq_zero; intro t _; exact if_neg t.property.ne_empty.symm
  rw [whole] at pay
  exact Equation.prod_u _ _ _ law pay

end YM.Integration.WilsonOriginalTwoFlatIRFlatMarked
end
