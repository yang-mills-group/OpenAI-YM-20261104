import YM.Integration.WilsonPhysicalStationDatedSalary
import YM.Integration.WilsonPhysicalStationRawReading

/-! The genuine booked graph margin on an elected positive reporting date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationFiledGate
open Function RG Wilson MergeProof Labels Source Lattice Work.G08
open Next.Rank Next.Rank.East Next.Rank.Price
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonPhysicalStationRawReading (err)
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {H:(Bel R.family.book).Hierarchy}
    {D:ℕ} (A:Vane R.family D)
local notation "L₀" => R.family.path.levels
local notation "C₀" => ((L₀).params A.k).columns
local notation "β₀" => (L₀).clock.hatBeta A.k
local notation "M₀" => Station.mag (L₀) A.b A.k

theorem refund : 0 ≤ 1-err R A.k := by
  apply sub_nonneg.mpr
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (Perch.boil_pos _) (by norm_num))

theorem original (check:A.checked f H D) (old:0<A.k)
    (book:∀ i,i ≤ A.k → ((R.family.S.block i).val:ℝ) ≤ (L₀).clock.monitor A.k) :
    1 ≤ M₀ ∧ (C₀)*err R A.k ≤ 1/2 := by
  have op:0 ≤ A.b:=(by norm_num : (0:ℝ) ≤ 5).trans check.high.1.le
  have w : 5<Perch.y (β₀):=check.high.1.trans_le check.high.2
  let t:=Perch.boil (β₀)
  have rich:25 ≤ t:=by unfold t Perch.boil; nlinarith only [w, sq_nonneg (Perch.y (β₀)-5)]
  have funds:2 ≤ Real.exp (t*((3:ℝ)/8)) :=
    (show (2:ℝ) ≤ _ from by linarith only [rich]).trans (Real.add_one_le_exp _)
  have realm:1 ≤ (L₀).clock.monitor A.k:=Real.one_le_exp (sq_nonneg _)
  refine ⟨Real.one_le_rpow realm op,?_⟩
  obtain ⟨i,step⟩:=Nat.exists_eq_succ_of_ne_zero old.ne'
  have loan:= (WilsonPhysicalStationDatedSalary.bank R i).1
  change A.k=i+1 at step
  rw [← step] at loan
  have quoted:=Real.rpow_le_rpow (by positivity : 0 ≤ ((R.family.S.block i).val:ℝ))
    (book i (by omega)) (by norm_num : (0:ℝ) ≤ 1/8)
  change (C₀) ≤ ((R.family.S.block i).val:ℝ)^((1:ℝ)/8) at loan
  calc
    _ ≤ ((L₀).clock.monitor A.k)^((1:ℝ)/8)*err R A.k :=
      mul_le_mul_of_nonneg_right (loan.trans quoted) (Real.exp_pos _).le
    _ = (Real.exp (t*((3:ℝ)/8)))⁻¹ := by
      change (Real.exp t)^((1:ℝ)/8)*Real.exp (t*(-1/2))=_
      rw [← Real.exp_mul,← Real.exp_add,← Real.exp_neg]
      congr 1; ring
    _ ≤ (1:ℝ)/2 := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) funds

end YM.Integration.WilsonPhysicalStationFiledGate
end
