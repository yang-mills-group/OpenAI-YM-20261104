import YM.Integration.WilsonMaxwellThermometerPublicUnit
import YM.Integration.WilsonMaxwellThermometerRegisteredOdd

/-! Factor-count and engineering grade on the actual registered local
basis descend to the Maxwell null quotient, including its original unit. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerChargedHeads
open Function Finset Labels MvPolynomial Maxwell Maxwell.Free Maxwell.Wick
open XSpace XSpace.Rose XSpace.Normalize XSpace.Cirrus XSpace.Structure1 XSpace.AxesTangent
open Spec OPE RG17 PhysMS PhysMS.Frame
open scoped BigOperators Classical
variable {G:Gauge}{d:ℕ}(F:Labels.Frame G d)

def sector:F.Coeff→ₗ[ℂ]Sec G d:=(observable G d).rangeRestrict.comp F.coords.symm.toLinearMap

def arm (i:F.Index):Sec G d:=(observable G d).rangeRestrict (F.basis i)

theorem summed (v:F.Coeff):sector F v=∑i,v i • arm F i:=by
  change (observable G d).rangeRestrict (F.coords.symm v)=_
  rw [←F.basis.sum_repr (F.coords.symm v),map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  have eq:F.basis.repr (F.coords.symm v) i=v i:=congrFun (F.coords.apply_symm_apply v) i
  rw [eq]
  rfl

theorem graded (i:F.Index):2*(F.grades i).2≤(F.grades i).1:=by
  let v:=F.basis i
  have nz:v.val≠0:=fun h=>(Module.Basis.ne_zero F.basis i) (Subtype.ext h)
  obtain ⟨l,hi⟩:=Finset.nonempty_iff_ne_empty.mpr
    (show v.val.support≠∅ from fun h=>nz (MvPolynomial.support_eq_empty.mp h))
  have h: Finsupp.weight bidegree l=F.grades i :=(pure_grade _ v).mp (F.pure i) (MvPolynomial.mem_support_iff.mp hi)
  rw [←h,weight_slot]
  unfold height
  rw [Finsupp.weight_apply]
  unfold Finsupp.sum
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  change 2*l j ≤ l j*generation j
  rw [mul_comm 2]
  exact Nat.mul_le_mul_left _ (show 2≤generation j from Nat.le_add_left _ _)

theorem reflection (i:F.Index):hinge d (arm F i)=((-1:ℂ)^(F.grades i).2) • arm F i:=by
  apply Subtype.ext
  rw [val_hinge]
  change _=((-1:ℂ)^(F.grades i).2) • reduceEq (F.basis i).val
  apply XSpace.Taylor.parity_sign
  let v:=(F.basis i).val
  change IsWeightedHomogeneous (fun _:Slot G=>(1:ℕ)) (reduceEq v) (F.grades i).2
  nth_rw 1 [v.as_sum]
  rw [map_sum]
  apply IsWeightedHomogeneous.sum
  intro l hl
  have h: Finsupp.weight bidegree l=F.grades i:=(pure_grade _ _).mp (F.pure i) (MvPolynomial.mem_support_iff.mp hl)
  rw [weight_slot] at h
  have degree:Finsupp.weight (fun _:Key G=>(1:ℕ)) l=(F.grades i).2:=by
    simpa [Finsupp.weight_apply,Finsupp.sum] using congrArg Prod.snd h
  rw [←degree]
  exact bounded_grade (fun _:Key G=>(1:ℕ)) (fun _:Slot G=>(1:ℕ)) reduceEq
    (reduce_grade fun _=>1) l _

def head (v:F.Coeff):F.Coeff:=fun i=>if F.grades i=(d,d/2) then v i else 0

theorem low (F:Labels.Frame G 4)(simple:G.Simple)(v:F.Coeff):
    sector F v=sector F (head F v)+(v 0) • leaf G 4:=by
  have axis0:arm F 0=leaf G 4:=by
    apply Subtype.ext
    change reduceEq (F.basis 0).val=1
    rw [F.starts_unit]
    exact map_one reduceEq
  have cut (i:F.Index):¬F.grades i=(4,2)→i=0:=by
    intro no
    by_contra nz
    have positive:=F.factors_pos i nz
    have h:=WilsonMaxwellThermometerWardColors.arity simple F i
    have debt:=graded F i
    have dh:=F.bound i
    exact no (Prod.ext (by omega) (by omega))
  rw [summed,summed]
  have separation (i:F.Index):v i • arm F i=(head F v i) • arm F i+
      (if i=0 then v 0 • leaf G 4 else 0):=by
    by_cases h:i=0
    · subst i;rw [if_pos rfl,axis0];simp [head,F.zero_degree]
    · have full:F.grades i=(4,2):=by by_contra no;exact h (cut i no)
      simp [head,full,h]
  calc
    _ = ∑i,((head F v i) • arm F i+(if i=0 then v 0 • leaf G 4 else 0)):=Finset.sum_congr rfl fun i _=>separation i
    _ = _:=by simp [Finset.sum_add_distrib]

theorem even (F:Labels.Frame G 6)(simple:G.Simple)(v:F.Coeff):
    hinge 6 (sector F v - sector F (head F v))=sector F v - sector F (head F v):=by
  rw [summed,summed,←Finset.sum_sub_distrib,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h:F.grades i=(6,3)
  · simp [head,h]
  have debt:=graded F i
  have bound:=F.bound i
  have no:=WilsonMaxwellThermometerWardColors.arity simple F i
  have pass:(F.grades i).2=0 ∨ (F.grades i).2=2:=by
    by_contra c
    exact h (Prod.ext (by omega) (by omega))
  have reflection':hinge 6 (arm F i)=arm F i:=by
    rw [reflection]
    rcases pass with s|s <;> simp [s]
  simp [head,h,map_smul,reflection']

end YM.Integration.WilsonMaxwellThermometerChargedHeads
end
