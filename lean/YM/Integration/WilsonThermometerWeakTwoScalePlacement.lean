import YM.Integration.WilsonThermometerWeakJointMesh
import YM.Integration.WilsonThermometerWeakJointCells

/-! Physical separation at the large detector buys the distinct-cell hearing on
both elected smaller chambers, before the UV and period regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakTwoScalePlacement
open Function Filter Set Lattice RG Push Next.Extract Dash Cells Next.Rank Next.Rank.Station
open scoped Classical Topology BigOperators
variable {G:Gauge} (A:Levels G)

theorem fee (simple:G.Simple) (u h:ℝ) (floor:0≤u) (room:u<h) (x:Fin 2 → E4)
    (away:∃j:Axis,x 0 j≠x 1 j):
    ∀ᶠ k:ℕ in atTop,∀ (m p:ℕ),A.S.a m≤gap A u k → ∀b:Fin 2 → Cover,
    (∀i j,|A.S.gridPoint k (b i) j-gap A h k*x i j|≤16*A.S.a k) →
    (∃j:Axis,A.S.a m+A.S.a k≤|A.S.gridPoint k (b 0) j-A.S.gridPoint k (b 1) j|) ∧
    (∀j:Axis,2*(|A.S.gridPoint k (b 0) j-A.S.gridPoint k (b 1) j|+A.S.a k+A.S.a m)<
      (A.S.side m p).val*A.S.a m):=by
  obtain ⟨a,ne⟩:=away
  let d:ℝ:=|x 0 a-x 1 a|
  have dp:0<d:=abs_pos.mpr (sub_ne_zero.mpr ne)
  let M:=∑j:Axis,|x 0 j-x 1 j|
  have Mp:0≤M:=Finset.sum_nonneg (fun j _=>abs_nonneg _)
  have grow:∀ᶠ k in atTop,34/d ≤ mag A (h-u) k:=
    (mag_rate A simple (sub_pos.mpr room)).eventually_ge_atTop _
  have shrink:∀ᶠ k in atTop,2*(M+34)*gap A h k<1:=by
    have van: Tendsto (fun k=>2*(M+34)*gap A h k) atTop (𝓝 0):=by
      simpa only [mul_zero] using (gap_rate A simple h).const_mul (2*(M+34))
    exact van.eventually_lt_const zero_lt_one
  filter_upwards [grow,shrink] with k gain small m p fee b close
  let ρ:=gap A h k
  have mn:1≤A.clock.monitor k:=Real.one_le_exp (sq_nonneg _)
  have mag₀:1 ≤ mag A u k:=Real.one_le_rpow mn floor
  have hf:0<gap A u k:=by exact mul_pos (A.S.a_pos k) (lt_of_lt_of_le zero_lt_one mag₀)
  have mr:1 ≤ mag A (h-u) k:=Real.one_le_rpow mn (sub_pos.mpr room).le
  have ratio:gap A u k*mag A (h-u) k=ρ:=by
    dsimp [gap,mag,ρ];rw [mul_assoc,←Real.rpow_add (lt_of_lt_of_le zero_lt_one mn)]
    congr 2;ring
  have mesh:A.S.a k≤gap A u k:=(le_mul_of_one_le_right (A.S.a_pos k).le mag₀)
  have fine:gap A u k≤ρ:=by rw [← ratio];exact le_mul_of_one_le_right hf.le mr
  have pos:0≤ρ:=hf.le.trans fine
  have rescale:34*gap A u k≤ρ*d:=by
    rw [←ratio,mul_assoc,mul_comm 34]
    exact mul_le_mul_of_nonneg_left ((div_le_iff₀ dp).mp gain) hf.le
  have compare (j:Axis):
      ρ*|x 0 j-x 1 j|≤|A.S.gridPoint k (b 0) j-A.S.gridPoint k (b 1) j|+32*A.S.a k ∧
      |A.S.gridPoint k (b 0) j-A.S.gridPoint k (b 1) j|≤ρ*|x 0 j-x 1 j|+32*A.S.a k:=by
    have l:=close 0 j;have r:=close 1 j
    have left:=abs_sub_le (ρ*x 0 j) (A.S.gridPoint k (b 0) j) (ρ*x 1 j)
    have right:=abs_sub_le (A.S.gridPoint k (b 0) j) (A.S.gridPoint k (b 1) j) (ρ*x 1 j)
    have mid:=abs_sub_le (A.S.gridPoint k (b 0) j) (ρ*x 0 j) (A.S.gridPoint k (b 1) j)
    have target:=abs_sub_le (ρ*x 0 j) (ρ*x 1 j) (A.S.gridPoint k (b 1) j)
    have eq:|ρ*x 0 j-ρ*x 1 j|=ρ*|x 0 j-x 1 j|:=by rw [←mul_sub,abs_mul,abs_of_nonneg pos]
    rw [eq,abs_sub_comm (ρ*x 0 j) (A.S.gridPoint k (b 0) j)] at left
    rw [eq,abs_sub_comm (ρ*x 1 j) (A.S.gridPoint k (b 1) j)] at target
    change |A.S.gridPoint k (b 0) j-ρ*x 0 j|≤_ at l
    change |A.S.gridPoint k (b 1) j-ρ*x 1 j|≤_ at r
    constructor <;> linarith
  refine ⟨⟨a,by change 34*gap A u k≤ρ*|x 0 a-x 1 a| at rescale;linarith [(compare a).1]⟩,?_⟩
  intro j
  have axis:|x 0 j-x 1 j|≤M:=Finset.single_le_sum (fun j _=>abs_nonneg (x 0 j-x 1 j)) (Finset.mem_univ j)
  have length:1≤(A.S.side m p).val*A.S.a m:=by
    rw [mul_comm,A.S.span_side]
    exact_mod_cast (A.S.period p).property
  apply lt_of_lt_of_le _ length
  have comparison:ρ*|x 0 j-x 1 j|≤M*ρ:=(mul_le_mul_of_nonneg_left axis pos).trans_eq (mul_comm ..)
  change 2*(M+34)*ρ<1 at small
  linarith [(compare j).2]

end YM.Integration.WilsonThermometerWeakTwoScalePlacement
end
