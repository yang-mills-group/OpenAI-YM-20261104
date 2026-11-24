import YM.Integration.WilsonPhysicalHistoryRetainedSpringField
import YM.WilsonCoeffUV.Kinetic.Alpha

/-! Evaluate the original rank-two kinetic reader before resetting the
finite incoming plan. Only its positive even coupling grades remain after
the authenticated constant alpha has been removed. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Lattice Wilson RG Precision IterationFour IterationFour.Vacuum PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic PowerSeries
open scoped BigOperators Classical
variable {G : Gauge} {N per r m : ℕ}

def pitchTail (R : Run G) (N m r : ℕ) (g : ℝ) : ℝ :=
  ∑ e∈Finset.range (r-2+1), if 2≤e ∧ e%2=0 then
    readSun (freshet R.family.path.levels R.metals.O N m (e+2) 2)*g^(e-2) else 0

def pitchPolynomial (R : Run G) (N m r : ℕ) (g : ℝ) : ℝ :=
  ∑ e∈Finset.range (r-2+1), coeff (e+2) (pitch R.family.path.levels R.metals.O N m)*g^e

theorem pitch_polynomial (R : Run G) (simple : G.Simple) (hm : m<N) (r : ℕ) (g : ℝ) :
    pitchPolynomial R N m r g-R.alloy.B.kin.alpha N m=g^2*pitchTail R N m r g := by
  let F:=freshet R.family.path.levels R.metals.O N m
  let p:=pitch R.family.path.levels R.metals.O N m
  have actual:=perch R.family.path.levels R.metals.O simple R.alloy.B.ratio hm
  have head:coeff 2 p=R.alloy.B.kin.alpha N m:=
    (alpha_stable simple R.alloy.B.ratio R.alloy.B.support hm.le).2 hm
  rw [pitchPolynomial,pitchTail,Finset.mul_sum]
  let E:=Finset.range (r-2+1)
  have zero:0∈E:=Finset.mem_range.mpr (by omega)
  rw [←Finset.sum_erase_add E (fun e=>coeff (e+2) p*g^e) zero]
  simp only [Nat.zero_add,pow_zero,mul_one,head,add_sub_cancel_right]
  rw [←Finset.sum_erase_add E (fun e=> g^2* (if 2≤e ∧ e%2=0 then readSun (F (e+2) 2)*g^(e-2) else 0)) zero]
  simp only [show ¬2≤(0:ℕ) by decide,false_and,if_false,mul_zero,add_zero]
  apply Finset.sum_congr rfl
  intro e he
  have ne : e≠0:=Finset.ne_of_mem_erase he
  by_cases live : 2≤e ∧ e%2=0
  · rw [if_pos live]
    have count:e=2+(e-2):=by omega
    have power : g^e=g^2*g^(e-2):=by conv_lhs => rw [count,pow_add]
    rw [power]
    change coeff (e+2) (Kstar F)*_=_
    rw [stellar_read]
    ring
  · rw [if_neg live,mul_zero]
    have odd:(e+2)%2≠0:=by omega
    have killed : coeff (e+2) p=0:=actual.parityC (e+2) odd
    rw [killed,zero_mul]

def pitchDifference (R : Run G) (P : Plan R.family N per r) (m : ℕ) (g : ℝ) : ℝ :=
  (R.alloy.B.kin.alpha N m-P.alpha m)+
  ∑ e∈Finset.range (r-2+1),
    (P.coefficient m e-coeff (e+2) (pitch R.family.path.levels R.metals.O N m))*g^e

theorem actual_pitch (R : Run G) (simple : G.Simple) (P : Plan R.family N per r) (hm : m<N) (g : ℝ) :
    P.poly m g-P.alpha m=pitchDifference R P m g+g^2*pitchTail R N m r g := by
  rw [←pitch_polynomial R simple hm r,pitchDifference,pitchPolynomial,Plan.poly]
  simp only [sub_mul,Finset.sum_sub_distrib]
  ring

theorem higher_pitch (R : Run G) (simple : G.Simple) (P : Plan R.family N per r) (hm : m<N)
    (cash : ∀e≤r-2, P.coefficient m e=coeff (e+2) (pitch R.family.path.levels R.metals.O N m))
    (alpha : P.alpha m=R.alloy.B.kin.alpha N m) (g : ℝ) :
    P.poly m g-P.alpha m=g^2*pitchTail R N m r g := by
  rw [actual_pitch R simple P hm,pitchDifference,alpha,sub_self,zero_add]
  have same (e : ℕ) (h:e∈Finset.range (r-2+1)) :
      (P.coefficient m e-coeff (e+2) (pitch R.family.path.levels R.metals.O N m))*g^e=0 := by
    rw [cash e (by have:=Finset.mem_range.mp h; omega),sub_self,zero_mul]
  rw [Finset.sum_eq_zero same,zero_add]

end YM.Integration.OriginalMarkedRunAction
