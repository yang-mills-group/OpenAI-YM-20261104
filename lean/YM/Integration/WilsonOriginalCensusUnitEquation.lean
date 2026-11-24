import YM.Integration.WilsonReceivedCanonicalSocketLevels

/-! A measured marked scalar in the native square-free ordinary and connected tables. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusUnitEquation
open Finset WilsonCoeffUV.Wheel.Mark
open scoped BigOperators Classical
variable {I R:Type}[DecidableEq I][CommRing R]

def omitAt (v:I)(F:Sac I R)(s:Finset I):R:=if v∈s then 0 else F s
def spike (v:I)(c:R)(s:Finset I):R:=if s={v} then c else 0
def blank (s:Finset I):R:=if s=∅ then 1 else 0

theorem erased {M L:Sac I R}(law:Equation M L)(v:I):
    Equation (omitAt v M) (omitAt v L):=by
  classical
  refine ⟨by simp [omitAt,law.1],by simp [omitAt,law.2.1],?_⟩
  funext s
  by_cases present:v∈s
  · simp only [dial,omitAt,present,if_true,nsmul_zero,shells]
    symm
    apply sum_eq_zero
    intro t ht
    by_cases h:v∈t
    · simp [h]
    · simp [h,present]
  · have inc:=congrFun law.2.2 s
    change s.card • (if v∈s then 0 else M s)=∑t∈s.powerset,
      (t.card • omitAt v L t)*omitAt v M (s\t)
    rw [if_neg present]
    refine inc.trans (sum_congr rfl (fun t ht=>?_))
    rw [omitAt,if_neg (fun w=>present ((mem_powerset.mp ht) w)),omitAt,
      if_neg (fun w=>present (sdiff_subset w))]
    rfl

theorem convolution (B D F H:Sac I R)(left:Equation B F)(right:Equation D H):
    Equation (shells B D) (F+H):=by
  refine ⟨by simp [shells_emp,left.1,right.1],by simp [left.2.1,right.2.1],?_⟩
  rw [dial_shell,left.2.2,right.2.2,dial_p,shells_l,littoral,
    ←littoral B (dial H) D,shores B (dial H),littoral]

theorem at_spike (v:I)(c:R)(M:Sac I R)(s:Finset I):
    shells (spike v c) M s=if v∈s then c*M (s.erase v) else 0:=by
  classical
  simp [shells,spike,ite_mul,Finset.sdiff_singleton_eq_erase]

theorem at_blank (M:Sac I R):shells blank M=M:=by
  funext s
  simp [shells,blank,ite_mul]

theorem small (v:I)(c:R):Equation (blank+spike v c) (spike v c):=by
  classical
  have once:dial (spike v c)=spike v c:=by
    funext s
    by_cases e:s={v}
    · subst s;simp [dial,spike]
    · simp [dial,spike,e]
  have no:dial (blank (I:=I) (R:=R))=0:=by
    funext s
    by_cases e:s=∅
    · subst s;simp [dial,blank]
    · simp [dial,blank,e]
  refine ⟨by simp [blank,spike],by simp [spike],?_⟩
  rw [dial_p,once,no,zero_add]
  funext s
  rw [at_spike]
  by_cases hv:v∈s
  · rw [if_pos hv]
    have noSelf:s.erase v≠{v}:=by
      intro same
      have h:v∈s.erase v:=same ▸ mem_singleton_self v
      exact notMem_erase v s h
    by_cases e:s={v}
    · subst s;simp [spike,blank]
    · have left:s.erase v≠∅:=by
        intro eq
        apply e
        simpa [eq] using (insert_erase hv).symm
      simp [spike,blank,noSelf,e,left]
  · have e:s≠{v}:=fun eq=>hv (eq ▸ mem_singleton_self v)
    simp [hv,spike,e]

/-- The measured ordinary division by the original quiet leaves the scalar
on its own connected singleton, and annihilates each mixed connected term containing it. -/
theorem filed [IsAddTorsionFree R] (M L:Sac I R)(law:Equation M L)(v:I)(c:R)
    (measured:∀s:Finset I,v∈s → M s=c*M (s.erase v)):
    L=spike v c+omitAt v L:=by
  classical
  have together:=convolution _ _ _ _ (small v c) (erased law v)
  have same:shells (blank+spike v c) (omitAt v M)=M:=by
    rw [shells_l,at_blank]
    funext s
    simp only [Pi.add_apply,at_spike]
    by_cases h:v∈s
    · simp [h,omitAt,measured s h]
    · simp [h,omitAt]
  rw [same] at together
  exact Equation.unique _ _ _ law together

end YM.Integration.WilsonOriginalCensusUnitEquation
