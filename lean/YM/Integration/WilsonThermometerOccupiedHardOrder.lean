import YM.Integration.WilsonThermometerReceivedHardNodes

/-! One extra fixed outgoing hard order pays the restored face in the actual coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOccupiedHardOrder
open Lattice RG Wilson PhysicalNext PhysicalNext.Repeat Legato Pert.Asymptotics
variable {G:Gauge}(R:Run G){N per f:ℕ}
local notation "heat" => R.alloy.B.a.clock.hatBeta (f+1)
local notation "g" => regulatorRun R.family N per (f+1)

theorem original (live:f+1≤N)(warm:3≤heat)(p l:ℕ):
    let q:=p+l+88
    let T:=heat^q/3
    1≤T ∧ 3*T≤heat^q ∧ ∀ (e B c δ : ℝ), 0 ≤ e → 0 ≤ c → g^l*e ≤ B →
      g^88*δ ≤ 10*(e*c)/T → δ ≤ 30*(B*c)*g^p:=by
  intro q T
  have hp:0<heat:=by linarith
  have unit:1≤heat:=by linarith
  have ready:heat≤heat^q:=by
    simpa only [pow_one] using pow_le_pow_right₀ unit (show 1≤q by dsimp [q];omega)
  have three:3≤heat^q:=warm.trans ready
  refine ⟨(le_div_iff₀ (by norm_num:0<(3:ℝ))).2 (by simpa using three),le_of_eq (by dsimp [T];ring),?_⟩
  intro e B c δ he hc debit drop
  have gp:=ActualRunKernelPackets.regulator_pos R N per (f+1) live
  let β:=(R.family.path.rep N per (f+1)).beta
  have band:= (R.makes.wilson.represents N per (f+1) live).band
  have bpos:0<β:=(div_pos hp (by norm_num:0<(2:ℝ))).trans_le band.1
  have btop:β≤2*heat:=band.2
  have bound:Real.sqrt β≤heat:=(Real.sqrt_le_iff).mpr ⟨hp.le,btop.trans (by nlinarith [mul_nonneg hp.le (show 0≤heat-2 by linarith)])⟩
  have small:heat⁻¹≤g:=(inv_le_inv₀ hp (Real.sqrt_pos.2 bpos)).2 bound
  have inv:(heat^q)⁻¹≤g^q:=by
    rw [←inv_pow];exact pow_le_pow_left₀ (inv_nonneg.mpr hp.le) small q
  apply (le_of_mul_le_mul_left (a:=g^88) _ (pow_pos gp _))
  calc
    g^88*δ ≤ 10*(e*c)/T:=drop
    _ = (30*(e*c))*(heat^q)⁻¹:=by dsimp [T];ring
    _ ≤ (30*(e*c))*g^q:=mul_le_mul_of_nonneg_left inv (by positivity)
    _ = (30*(g^p*g^88))*((g^l*e)*c):=by dsimp [q];rw [pow_add,pow_add];ring
    _ ≤ (30*(g^p*g^88))*(B*c):=by gcongr
    _ = _:=by ring

end YM.Integration.WilsonThermometerOccupiedHardOrder
