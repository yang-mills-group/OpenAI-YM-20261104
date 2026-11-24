import YM.Integration.WilsonIndependentFittedNumericalProduct
import YM.Integration.WilsonIndependentFittedMixedCash

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentFittedRosterCash
open WilsonCoeffUV Blue Finset PowerSeries
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open scoped BigOperators Classical
variable {I:Type}[Fintype I]{J:I→Type}[∀i,Fintype (J i)]

def roster (A:(i:I)→J i→ Cost)(B:((i:I)→J i)→ Cost):Cost:=∑w,(∏i,A i (w i))*B w
def numerical (Q:ℕ)(g:ℝ)(A:(i:I)→J i→ Cost):ℝ:=∏i,∑j,‖cash Q g (embed (A i j))‖
def reserve (Q:ℕ)(A:(i:I)→J i→ Cost):ℝ:=∏i,∑j,belt Q (embed (A i j))

theorem measured (Q:ℕ)(g:ℝ)(small:|g|≤1)(A:(i:I)→J i→ Cost)(B:((i:I)→J i)→ Cost)
    (M:ℝ)(salary:∀w,belt Q (embed (B w))≤M):
    ‖cash Q g (embed (roster A B))-∑w,(∏i,cash Q g (embed (A i (w i))))*cash Q g (embed (B w))‖≤
      ((Fintype.card I:ℝ)+1)*|g|^(Q+1)*reserve Q A*M:=by
  unfold roster reserve
  simp only [map_sum,map_mul,map_prod,WilsonIndependentFittedNumericalProduct.added]
  rw [←sum_sub_distrib,Fintype.prod_sum,mul_sum,sum_mul]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro w _
  let f:Option I→PowerSeries ℂ:=fun i=>i.elim (embed (B w)) (fun j=>embed (A j (w j)))
  have one:=WilsonIndependentFittedNumericalProduct.signed Q small univ f
  simp only [Fintype.prod_option,f,Option.elim_none,Option.elim_some,card_univ,
    Fintype.card_option,Nat.cast_add,Nat.cast_one] at one
  calc
    _ = ‖cash Q g (embed (B w)*∏i,embed (A i (w i)))-cash Q g (embed (B w))*(∏i,cash Q g (embed (A i (w i))))‖:=by
      rw [mul_comm (embed (B w)),mul_comm (cash Q g (embed (B w)))]
    _ ≤ ((Fintype.card I:ℝ)+1)*|g|^(Q+1)*(belt Q (embed (B w))*(∏i,belt Q (embed (A i (w i))))):=by
      rwa [norm_sub_rev]
    _ ≤ _:=by
      have pos (i:I):0≤belt Q (embed (A i (w i))):=sum_nonneg fun _ _=>norm_nonneg _
      have price:=mul_le_mul_of_nonneg_right (salary w) (prod_nonneg (s:=univ) fun i _=>pos i)
      simpa only [mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_left price
        (by positivity:0≤((Fintype.card I:ℝ)+1)*|g|^(Q+1))

theorem original (Q:ℕ)(g:ℝ)(small:|g|≤1)(A:(i:I)→J i→ Cost)(B:((i:I)→J i)→ Cost)
    (M:ℝ)(salary:∀w,belt Q (embed (B w))≤M):
    ‖cash Q g (embed (roster A B))‖≤
      (numerical Q g A+((Fintype.card I:ℝ)+1)*|g|^(Q+1)*reserve Q A)*M:=by
  let v:=∑w,(∏i,cash Q g (embed (A i (w i))))*cash Q g (embed (B w))
  have kept:‖v‖≤numerical Q g A*M:=by
    unfold numerical
    rw [Fintype.prod_sum,sum_mul]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro w _
    rw [norm_mul,norm_prod]
    exact mul_le_mul_of_nonneg_left ((WilsonIndependentFittedMixedCash.cash_le Q g small _).trans (salary w))
      (prod_nonneg fun _ _=>norm_nonneg _)
  have tail:=measured Q g small A B M salary
  calc
    _ ≤ ‖cash Q g (embed (roster A B))-v‖+‖v‖:=(norm_le_insert' ..).trans_eq (add_comm _ _)
    _ ≤ ((Fintype.card I:ℝ)+1)*|g|^(Q+1)*reserve Q A*M+numerical Q g A*M:=add_le_add tail kept
    _=_:=by ring

end YM.Integration.WilsonIndependentFittedRosterCash
