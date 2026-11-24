import YM.Integration.WilsonEmittedOriginalCalendar
import YM.Integration.WilsonMeasuredProtectedSectionRate
/-! Pass the earned regular cost at the receiving coupling through the actual physical projection. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedReportedRate
open Finset Filter RG Wilson Lattice Source Labels PhysicalNext Repeat Legato Pert.Asymptotics
open WilsonEmittedProtectedReturn Push.Local Planned.GuardedAtom Trace.Physical RG16
open scoped BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple)

include simple in
theorem adjacent : ∀ᶠ i:ℕ in atTop,∀N per,i<N →
    regulatorRun R.family N per i  ≤  3*regulatorRun R.family N per (i+1) :=by
  filter_upwards [RG01.Physical.nextHat simple R.family.path.levels] with i next N per live
  let lo:=(R.family.path.rep N per i).beta
  let up:=(R.family.path.rep N per (i+1)).beta
  have hp:0<lo:=RG02.Actual.coupling_pos R.makes.wilson live.le
  have jp:0<up:=RG02.Actual.coupling_pos R.makes.wilson live
  have low:R.family.path.levels.clock.hatBeta i/2  ≤  lo:= (R.makes.wilson.represents N per i live.le).band.1
  have high:up  ≤  2*R.family.path.levels.clock.hatBeta (i+1):=(R.makes.wilson.represents N per (i+1) live).band.2
  have invoice:up ≤ 8*lo:=by linarith only [low,high,next]
  have test:Real.sqrt up ≤ 3*Real.sqrt lo:=by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    nlinarith only [invoice,hp,Real.sq_sqrt hp.le]
  change (Real.sqrt lo)⁻¹ ≤ 3*(Real.sqrt up)⁻¹
  rw [←one_div,←div_eq_mul_inv,div_le_div_iff₀ (Real.sqrt_pos.mpr hp) (Real.sqrt_pos.mpr jp)]
  simpa only [one_mul] using test

include simple in
theorem funded (slow:∀i,((R.family.S.block i).val:ℝ) ≤ Real.log (2+Real.log (R.family.path.levels.clock.hatBeta i)))
    (d q:ℕ) {ε:ℝ} (ep:0<ε) : ∃δ>0,∀ᶠ i:ℕ in atTop,∀N per m, i<N → m ≤ i →
    ∀W:Rep G (R.family.side i per), W.p=R.family.path.levels.budget i → W.p.supportExponent ≤ 100 →
    ∀a M:ℝ,0 ≤ a → 0 ≤ M → a ≤ δ*(regulatorRun R.family N per i)^(q+2)*M →
      factor R.family.params (R.family.localSection d) W.p.supportExponent
        (R.family.path.levels.params i).columns*a ≤  (ε*(regulatorRun R.family N per m)^q)*M :=by
  obtain ⟨ρ,pos,gate⟩:=WilsonMeasuredProtectedSectionRate.original R simple slow d q ep
  let δ:=ρ/3^(q+2)
  have δ0:0<δ:=div_pos pos (by positivity)
  refine ⟨δ,δ0,?_⟩
  filter_upwards [gate,adjacent R simple] with i funded right N per m live prior W same signed a M ap mp bill
  apply funded N per m live prior W same signed a M ap mp
  let a₀:=regulatorRun R.family N per i
  let a₁:=regulatorRun R.family N per (i+1)
  have zp:0 ≤ a₀:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have jump:=pow_le_pow_left₀ zp (right N per live) (q+2)
  rw [mul_pow] at jump
  exact bill.trans <| (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left jump δ0.le) mp).trans_eq (by
    dsimp only [δ];field_simp)

end YM.Integration.WilsonEmittedReportedRate
end
