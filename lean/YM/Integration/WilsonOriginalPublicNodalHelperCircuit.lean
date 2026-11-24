import YM.Integration.WilsonOriginalPublicNodalHelperShape
import YM.Integration.WilsonIndependentLicensedCircuit

/-! The grouped prefix on the physical helper side uses the already enrolled finite menu of real patches. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalHelperCircuit
open Lattice RG RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger
open WilsonOriginalPublicNodalHelperShape
open WilsonIndependentLicensedCircuit (stamp stages patches)
open WilsonIndependentEvenPassport (power)
open scoped Classical
variable {X:Type}(V:XSpace.Run)(E r:X → ℕ)(a k:ℕ)(positive:0<a)(late:4≤k)

def stage (p:Page (length E r a)):ℕ:=if p.downW=0 then k+1 else k

def circuit:Circuit (length E r a) (n V E r a) where
  l p:=((n V E r a (Page.opening _ p.bindW)).val:ℝ)/(n V E r a p).val
  P x:=((n V E r a (Page.opening _ x)).val:ℝ)
  sizeL:=edge V E r a
  J:=stage E r a k
  seats:=seats V E r a
  odd f:=V.odd.pow
  holds f:=by
    apply V.large.trans (Nat.le_self_pow _ _)
    split_ifs <;> omega
  stands p:=V.finalSide.large.trans (Nat.le_mul_of_pos_right _ (V.den_pos _))
  dual p:=even_iff_two_dvd.mpr (dvd_mul_of_dvd_left V.finalSide.even _)
  week p:=by dsimp [stage];split_ifs <;> omega
  shakes f:=by simp only [stage,Flap.next,Flap.prev,Nat.add_one_ne_zero,if_false];split_ifs <;> omega
  slow f:=by simp only [stage,Flap.next,Flap.prev,Nat.add_one_ne_zero,if_false];split_ifs <;> omega
  l_p p:=div_pos (by exact_mod_cast (n V E r a (Page.opening _ p.bindW)).pos) (by exact_mod_cast (n V E r a p).pos)
  comet p:=div_mul_cancel₀ _ (by exact_mod_cast (n V E r a p).pos.ne')

local notation "C" => circuit V E r a k positive late
theorem opening (x:X):(C).l (Page.opening _ x)=1:=div_self (by exact_mod_cast (n V E r a (Page.opening _ x)).pos.ne')
theorem length_le (f:Flap (length E r a)):(power V a).val≤((C).sizeL f).val:=by
  change V.ratio^a ≤ V.ratio^(if f.offset=0 then a+r f.volW else a)
  split_ifs <;> first | exact le_rfl | exact Nat.pow_le_pow_right (by have:=V.large;omega) (Nat.le_add_right _ _)
theorem page (s:Page (length E r a)):(C).J s∈stages k:=by
  change (if s.downW=0 then k+1 else k)∈stages k
  split_ifs <;> simp [stages]
private theorem patch_eq {p q:Patch}(l:p.L=q.L)(k:p.J=q.J):p=q:=by cases p;cases q;congr
theorem patch (res:∀x,r x<a)(f:Flap (length E r a)):
    (C).pactP f∈patches V a k positive late:=by
  rw [patches,Finset.mem_insert]
  by_cases z:f.offset=0
  · right;apply Finset.mem_image.mpr
    refine ⟨⟨r f.volW,res _⟩,Finset.mem_univ _,?_⟩
    apply patch_eq
    · simp [stamp,Circuit.pactP,circuit,edge,z]
    · simp [stamp,Circuit.pactP,circuit,stage,Flap.prev,z]
  · left
    apply patch_eq
    · simp [stamp,Circuit.pactP,circuit,edge,z]
    · simp [stamp,Circuit.pactP,circuit,stage,Flap.prev,z]

include positive in
theorem outer (enough:∀x,0<length E r a x)(x:X):
    (n V E r a (Page.finallyW _ x)).val≤V.finalSide.side.val*V.ratio^a:=by
  rw [terminal V E r a enough]
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_right (by have:=V.large;omega) (Nat.mod_lt _ positive).le

end YM.Integration.WilsonOriginalPublicNodalHelperCircuit
end
