import YM.Integration.WilsonPhysicalStationLowerReceiver
import YM.Integration.WilsonPhysicalStationBasisIncome
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedContrastBill
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS Cells
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open Next.Rank Next.Rank.Station Next.Rank.Perch Next.Rank.Price
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){S:Table R.family.book}{h e:ℕ}
open WilsonPhysicalStationLowerReceiver (ear)

theorem order {T:ℝ}(large:1≤T)(q Q:ℕ):T^Q≤T^q*T^(Q-q):=by
  by_cases yes:q≤Q
  · rw [←pow_add,Nat.add_sub_of_le yes]
  · rw [Nat.sub_eq_zero_of_le (le_of_not_ge yes),pow_zero,mul_one]
    exact pow_le_pow_right₀ large (le_of_not_ge yes)

theorem stationed {T:ℝ}(big:1≤T)(q Q depth:ℕ)(x:ℂ)(w:ℝ)
    (fee:((depth:ℝ)+1)*T^((Q-q:ℕ):ℝ)*‖x‖≤w):
    ‖x‖*T^Q≤w/((depth:ℝ)+1)*T^q:=by
  rw [Real.rpow_natCast] at fee
  have budget:‖x‖*T^(Q-q)≤w/((depth:ℝ)+1):=by
    apply (le_div_iff₀ (by positivity : 0<(depth:ℝ)+1)).2
    calc _ =((depth:ℝ)+1)*T^(Q-q)*‖x‖:=by ring
         _ ≤ _:=fee
  calc
    _ ≤ ‖x‖*(T^q*T^(Q-q)):=mul_le_mul_of_nonneg_left (order big q Q) (norm_nonneg _)
    _ = (‖x‖*T^(Q-q))*T^q:=by ring
    _ ≤ _:=mul_le_mul_of_nonneg_right budget (pow_nonneg (zero_le_one.trans big) q)
theorem joined (x:Points 2)(z:S.Field e)(fine coarse W:S.Field h)(χ Γ:ℂ)
    {T:ℝ}(positive:0≤T)(q Q:ℕ)(B A:ℝ)
    (upper:‖ear R x z (fine-W)-χ*Γ‖*T^Q≤B*T^q)
    (same:‖ear R x z coarse-Γ‖*T^Q≤A*T^q):
    ‖ear R x z ((fine-χ • coarse)-W)‖*T^Q≤T^q*(B+‖χ‖*A):=by
  let L:=ear R (S:=S) (e:=h) x z
  have swap:L ((fine-χ • coarse)-W)=(L (fine-W)-χ*Γ)-χ*(L coarse-Γ):=by simp only [map_sub,map_smul,smul_eq_mul]; ring
  change ‖L ((fine-χ • coarse)-W)‖*T^Q≤_
  rw [swap]
  calc
    _ ≤ (‖L (fine-W)-χ*Γ‖+‖χ*(L coarse-Γ)‖)*T^Q:=mul_le_mul_of_nonneg_right (norm_sub_le ..) (pow_nonneg positive _)
    _ = ‖L (fine-W)-χ*Γ‖*T^Q+‖χ‖*(‖L coarse-Γ‖*T^Q):=by rw [norm_mul];ring
    _ ≤ B*T^q+‖χ‖*(A*T^q):=add_le_add upper (mul_le_mul_of_nonneg_left same (norm_nonneg _))
    _ = _:=by ring
end YM.Integration.WilsonPhysicalStationMixedContrastBill
end
