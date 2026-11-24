import YM.Integration.WilsonOriginalTwoFlatIRFlatWage

/-! One total coupling truncation after all disjoint ordinary products have
been formed. Each connected block spends its own actual scalar invoice. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRFlatPartitions
open Finset Marker
open scoped BigOperators Classical
variable {V I:Type} [DecidableEq V] [Fintype I] {J:Census V} {q:ℕ}
  (m:I→J.Mode)(cash:I→Fin (q+1)→ℂ)
private def grade : Option (Fin (q+1))→ℕ
  | none=>0
  | some e=>e.val
def row (j:I) : Option (Fin (q+1))→Poly J
  | none=>1
  | some e=>Poly.send (m j) (cash j e)
def exponent (w:I→Option (Fin (q+1))):ℕ:=∑j,grade (w j)
def term (w:I→Option (Fin (q+1))):Poly J:=∏j,row m cash j (w j)
def settled (g:ℂ):Poly J:=∏j,(1+Poly.send (m j) (∑e:Fin (q+1),g^e.val*cash j e))
def crop (g:ℂ)(p:ℕ):Poly J:=
  ∑w:I→Option (Fin (q+1)),if exponent w≤p then (g^(exponent w)) • term m cash w else 0

omit [Fintype I] in
private theorem factor (g:ℂ)(j:I):
    (1+Poly.send (m j) (∑e:Fin (q+1),g^e.val*cash j e))=
      ∑u:Option (Fin (q+1)),g^(grade u) • row m cash j u:=by
  rw [Fintype.sum_option]
  simp only [grade,row,pow_zero,one_smul]
  apply congrArg (1+·)
  ext s
  rw [Poly.part_sum]
  by_cases h:s=m j <;> simp [Poly.part_smul,Poly.part_send,h]

theorem expanded (g:ℂ):
    settled m cash g=
      ∑w:I→Option (Fin (q+1)),g^(exponent w) • term m cash w:=by
  unfold settled
  simp_rw [factor m cash g]
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro w _
  simp [term,exponent,Finset.prod_smul,Finset.prod_pow_eq_pow_sum]

private theorem price (s:J.Mode)(w:I→Option (Fin (q+1))):
    ‖(term m cash w).part s‖≤∏j,Poly.price (fun _:V=>1) (row m cash j (w j)):=by
  have available:=Poly.member (w:=fun _:V=>1) (fun _=>zero_lt_one) s (term m cash w)
  rw [show Poly.toll (fun _:V=>1) s=1 by simp [Poly.toll],one_mul] at available
  exact available.trans (Poly.multiple (fun _:V=>zero_lt_one) univ _)

theorem original (g:ℝ)(hg:0≤g)(small:g≤1)(p:ℕ)(s:J.Mode):
    ‖(settled m cash g).part s-(crop m cash g p).part s‖≤
      g^(p+1)*∏j,(1+∑e:Fin (q+1),‖cash j e‖):=by
  rw [expanded,crop,Poly.part_sum,Poly.part_sum,←sum_sub_distrib]
  let wgt (j:I)(k:Option (Fin (q+1))):=Poly.price (fun _:V=>1) (row m cash j k)
  have cost (j:I):∑k:Option (Fin (q+1)),wgt j k=1+∑e:Fin (q+1),‖cash j e‖:=by
    simp [wgt,Fintype.sum_option,row,Poly.toll]
  simp_rw [←cost]
  rw [Fintype.prod_sum,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro w _
  by_cases keep:exponent w≤p
  · simp only [if_pos keep,sub_self,norm_zero]
    exact mul_nonneg (pow_nonneg hg _) (prod_nonneg fun j _=>Poly.nonnegative (fun _:V=>zero_lt_one) _)
  · rw [if_neg keep,Poly.part_nil,sub_zero,Poly.part_smul,norm_mul,norm_pow,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hg]
    exact mul_le_mul (pow_le_pow_of_le_one hg small (by omega)) (price m cash s w) (norm_nonneg _) (pow_nonneg hg _)

end YM.Integration.WilsonOriginalTwoFlatIRFlatPartitions
end
