import YM.Integration.WilsonMaxwellThermometerWardColors
import YM.Integration.WilsonMaxwellThermometerChargedHeads

/-! A simple-gauge invariant label of horizon at most four sees only the
undifferentiated curvature. This statement is on the actual off-shell label
space, before applying the Maxwell quotient. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourVariables
open Finset Labels MvPolynomial
open scoped Classical BigOperators
variable {G:Gauge}{h:ℕ}(F:Frame G h)(simple:G.Simple)(cap:h≤4)
include F simple cap
theorem support (i:F.Index)(l:Key G→₀ℕ)(member:l∈(F.basis i).val.support)
    (v:Key G)(present:v∈l.support):v.1=0:=by
  have weight: Finsupp.weight bidegree l=F.grades i:=
    (pure_grade _ _).mp (F.pure i) (MvPolynomial.mem_support_iff.mp member)
  rw [weight_slot] at weight
  have order:l.sum (fun _ n=>n)=(F.grades i).2:=congrArg Prod.snd weight
  have paid:height l≤4:=(congrArg Prod.fst weight).le.trans ((F.bound i).trans cap)
  have pos:0<l v:=Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp present)
  have inc:l v≤l.sum fun _ n=>n:=Finset.single_le_sum (s:=l.support) (f:=l) (fun _ _=>Nat.zero_le _) present
  have noOne:=WilsonMaxwellThermometerWardColors.arity simple F i
  have many:2*(l.sum fun _ n=>n)≥4:=by omega
  have count:height l=2*(l.sum fun _ n=>n)+∑j∈l.support,j.1*l j:=by
    unfold height
    rw [Finsupp.weight_apply]
    unfold Finsupp.sum
    simp only [Finset.mul_sum,←Finset.sum_add_distrib]
    apply sum_congr rfl
    intro j _
    change l j*(j.1+2)=2*l j+j.1*l j
    ring
  have small:(∑j∈l.support,j.1*l j)=0:=by omega
  have one:v.1*l v≤(∑j∈l.support,j.1*l j):=single_le_sum (f:=fun j:Key G=>j.1*l j) (fun _ _=>Nat.zero_le _) present
  exact (Nat.mul_eq_zero.mp (Nat.eq_zero_of_le_zero (small ▸ one))).resolve_right (Nat.ne_of_gt pos)

private theorem letter (i:F.Index)(A B:Jet G)(same:A 0=B 0):
    read A (F.basis i).val=read B (F.basis i).val:=by
  unfold Labels.read
  simp only [MvPolynomial.aeval_eq_eval₂Hom,MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_eq]
  apply sum_congr rfl
  intro l mem
  congr 1
  apply prod_congr rfl
  intro v here
  have first:=support F simple cap i l mem v here
  rcases v with ⟨t,j⟩
  change t=0 at first
  subst t
  simp only [coord,same]

theorem original (p:Label G h)(A B:Jet G)(same:A 0=B 0):read A p.val=read B p.val:=by
  let at_ (Y:Jet G):Label G h→ₗ[ℂ]ℂ:=(read Y).toLinearMap.comp (localFields G h).subtype
  change at_ A p=at_ B p
  rw [←F.basis.sum_repr p,map_sum,map_sum]
  apply sum_congr rfl
  intro i _
  simp only [map_smul]
  rw [show at_ A (F.basis i)=at_ B (F.basis i) from letter F simple cap i A B same]

end YM.Integration.WilsonPositionProgramTrialPublicJointFourVariables
