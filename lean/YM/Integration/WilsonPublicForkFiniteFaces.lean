import YM.Integration.WilsonPublicOutputRegulators

/-! The original ordinary numerator and each of the original genuine
output-column two-point readings can be compared before finite-basis subtraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkFiniteFaces
open Next.Rank RG12 SharpGram Extraction
open Function Finset Filter Set Table Spec RG17 Maxwell Climb FVA2 FVA2.Register
open PhysicalNext.Repeat.Legato XSpace XSpace.Normalize FVA2.O
open MS MS.Menus MS.Land MS.Theater WilsonMSDictionaryVector WilsonPublicOutputRegulators
open scoped Classical BigOperators Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
variable {I:Type}[Fintype I](F:Final R.family f S)(L:Layout F)(X:I → External R.family S)
  {n h:ℕ}(d:Fin n → ℕ)(ins:∀i,R.family.label (d i))(out:Dframe.Toon G h → R.family.label h)
  (r:ℝ)(ψ:Test n)

theorem measured (i:UVIndex)(e:Free R.family h)(ordinary:I → ℂ)(gram:Dframe.Toon G h → I → ℂ)
    {fee a b c:ℝ}(fp:0≤fee)(ap:0≤a)(bp:0≤b)(cp:0≤c)
    (wallet:(∑k,‖(WilsonMSDictionaryVector.basis R.family h).repr e k‖)≤fee)
    (product:∀j,‖packMark L (X j) d ins r ψ i - ordinary j‖≤a)
    (columns:∀k j,‖headMark L (X j) h r i (out k)-gram k j‖≤b)
    (independent:∀j,‖ordinary j-∑k,(WilsonMSDictionaryVector.basis R.family h).repr e k*gram k j‖≤c):
    ‖contrast F L X d ins out r ψ e i‖≤a+c+fee*b:=by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr;intro j
  let α:=fun k=>(WilsonMSDictionaryVector.basis R.family h).repr e k
  let peer:=fun k=>headMark L (X j) h r i (out k)
  let trueRow:=packMark L (X j) d ins r ψ i
  have joined:contrast F L X d ins out r ψ e i j =
      (trueRow-ordinary j)+(ordinary j-∑k,α k*gram k j)-∑k,α k*(peer k-gram k j):=by
    dsimp [contrast,α,peer,trueRow];simp only [mul_sub,Finset.sum_sub_distrib];ring
  have due:‖∑k,α k*(peer k-gram k j)‖≤fee*b:=by
    calc
      _≤∑k,‖α k*(peer k-gram k j)‖:=norm_sum_le _ _
      _≤∑k,‖α k‖*b:=by
        apply Finset.sum_le_sum;intro k _;rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (columns k j) (norm_nonneg _)
      _=(∑k,‖α k‖)*b:=by rw [Finset.sum_mul]
      _≤fee*b:=mul_le_mul_of_nonneg_right wallet bp
  rw [joined]
  exact (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (product j) (independent j))) due)

end YM.Integration.WilsonPublicForkFiniteFaces
