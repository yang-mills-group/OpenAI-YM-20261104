import YM.Integration.WilsonIndependentFittedNumericalProduct

/-! Exact residual price when the normalized basis belongs to the original raw frame. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentFittedNumericalTail
open Finset Lattice XSpace XSpace.Rose XSpace.Cirrus FVA2
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonIndependentFittedNumericalProduct (fitted numerical gross pivot regroup)
open scoped BigOperators Classical
variable {G:Gauge}(W:Initialize G){n:ℕ}(x:Sample n){I:Type}[Fintype I]
    {α:I→Type}[∀i,Fintype (α i)]
    (P:(i:I)→α i→Bare.Series (W.tree x.F.p) G)(D:(i:I)→α i→PowerSeries ℂ)

def tariff (Q J:ℕ)(u:ℝ):ℝ:=∑a:(i:I)→α i,(∏i,‖cash Q u (D i (a i))‖)*
    ‖cash Q u (pivot W x P a)-cash J u (pivot W x P a)‖

theorem original (Q J:ℕ){u:ℝ}(small:|u|≤1):
    ‖cash Q u (fitted W x P D)-numerical W x P D Q J u‖≤
      ((Fintype.card I:ℝ)+1)*|u|^(Q+1)*gross W x P D Q+tariff W x P D Q J u:=by
  have loss:‖numerical W x P D Q Q u-numerical W x P D Q J u‖≤tariff W x P D Q J u:=by
    unfold numerical tariff
    rw [←sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro a _
    rw [←mul_sub,norm_mul,norm_prod]
  have tri:=norm_add_le (cash Q u (fitted W x P D)-numerical W x P D Q Q u)
    (numerical W x P D Q Q u-numerical W x P D Q J u)
  rw [sub_add_sub_cancel] at tri
  exact tri.trans (add_le_add (regroup W x P D Q small) loss)

end YM.Integration.WilsonIndependentFittedNumericalTail
