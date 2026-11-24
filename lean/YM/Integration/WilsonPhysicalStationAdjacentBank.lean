import YM.Integration.WilsonPhysicalStationDatedSalary
import YM.Integration.WilsonPhysicalStationFiledGate

/-! The real adjacent block pays both original factory column counts. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationAdjacentBank
open Filter Function RG Labels Source Lattice Wilson Next.Rank Next.Rank.East Next.Rank.Price
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph Work.G08 Next.Foundations
open WilsonPhysicalStationRawReading (err)
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G)
local notation "C" => R.family
local notation "A" => R.family.path.levels
def stock (i:ℕ):ℝ:=(((C).S.block i).val:ℝ)^((1:ℝ)/16)

theorem first (i:ℕ): 1+((A).params (i+1)).columns  ≤  stock R i := by
  let s:=((A).params (i+1)).columns
  let j:=(A).clock.J (i+1)
  let u:=R.w.K (j+1)
  let l:=(((C).S.block i).val:ℝ)
  have hl:0 ≤ l:=by dsimp [l];positivity
  have hU:1 ≤ u:=R.w.prices _
  have hS:1 ≤ s:=((A).params _).columns_ge
  have booked:100000*u^6*(1+s)^2  ≤  l^((1:ℝ)/8) :=R.b.clock.bank i
  have caps : (1+s)^2 ≤ 100000*u^6*(1+s)^2:=
    le_mul_of_one_le_left (sq_nonneg _) ((by norm_num : (1:ℝ) ≤ 100000).trans (le_mul_of_one_le_right (by norm_num) (one_le_pow₀ hU)))
  have sq:(stock R i)^2=l^((1:ℝ)/8):=by
    change (l^((1:ℝ)/16))^2=_
    rw [←Real.rpow_mul_natCast hl];norm_num
  exact (sq_le_sq₀ (by linarith only [hS]:0 ≤ 1+s) (Real.rpow_nonneg hl _)).mp (by change (1+s)^2 ≤ (stock R i)^2;rw [sq];exact caps.trans booked)

theorem block_mono {m k:ℕ} (dates:m ≤ k) :
    (((C).S.block m).val:ℝ)  ≤  (((C).S.block k).val:ℝ) := by
  exact_mod_cast (show ((C).S.block m).val ≤ ((C).S.block k).val by
    rw [←(A).fits.sameFactor m,←(A).fits.sameFactor k]
    exact (A).fits.monotoneL ((A).fits.mono (Nat.succ_le_succ dates)))

theorem both (m:ℕ) (positive:0 < m):
    1+((A).params m).columns ≤ stock R m ∧ 1+((A).params (m+1)).columns ≤ stock R m := by
  obtain ⟨i,rfl⟩:=Nat.exists_eq_succ_of_ne_zero positive.ne'
  refine ⟨(first R i).trans ?_,first ..⟩
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (block_mono R (Nat.le_succ i)) (by norm_num)

theorem brick (m:ℕ): stock R m*Bid.barunit ((C).S.block m)=
    (((C).S.block m).val:ℝ)^(-(5:ℝ)/16) := by
  let l:=(((C).S.block m).val:ℝ)
  have hl:0 < l:=by dsimp [l];exact_mod_cast ((C).S.block m).pos
  change l^((1:ℝ)/16)*(l^((1:ℝ)/8))⁻¹^3=l^(-(5:ℝ)/16)
  rw [←Real.rpow_neg hl.le,←Real.rpow_mul_natCast hl.le,←Real.rpow_add hl]
  norm_num

theorem heat (m k:ℕ) (shelter:(((C).S.block m).val:ℝ) ≤ (A).clock.monitor k) :
    stock R m*err R k ≤ ((A).clock.monitor k)^(-(7:ℝ)/16) ∧
      stock R m^2*err R k ≤ ((A).clock.monitor k)^(-(3:ℝ)/8) := by
  let β:=(A).clock.hatBeta k
  let E:=(A).clock.monitor k
  have hE:0 < E:=Real.exp_pos _
  have fee:err R k=E^(-(1:ℝ)/2):=by
    change Real.exp (Perch.boil β * (-(1:ℝ)/2))=(Real.exp (Perch.boil β))^(-(1:ℝ)/2)
    rw [←Real.exp_mul]
  have mat:stock R m ≤ E^((1:ℝ)/16):=Real.rpow_le_rpow (Nat.cast_nonneg _) shelter (by norm_num)
  have nonneg:0 ≤ stock R m:=Real.rpow_nonneg (Nat.cast_nonneg ((C).S.block m).val) _
  rw [fee]
  constructor
  · calc
      _  ≤  E^((1:ℝ)/16)*E^(-(1:ℝ)/2):=mul_le_mul_of_nonneg_right mat (Real.rpow_nonneg hE.le _)
      _ = _:=by rw [←Real.rpow_add hE];norm_num;rfl
  · calc
      _  ≤  (E^((1:ℝ)/16))^2*E^(-(1:ℝ)/2):=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ nonneg mat _) (Real.rpow_nonneg hE.le _)
      _ = _:=by rw [←Real.rpow_mul_natCast hE.le,←Real.rpow_add hE];norm_num;rfl

end YM.Integration.WilsonPhysicalStationAdjacentBank
end
