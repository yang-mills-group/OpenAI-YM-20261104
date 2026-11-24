import YM.WilsonCoeffUV.Emit.ReportingClocks
import YM.Integration.WilsonPositionProgramInversionWindowCost
import YM.Integration.WilsonIndependentCapturedDates

/-! The normalized cover's comparison factor throughout the original
lower interval on the issued super-wide inversion board. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace YM.Integration.WilsonPositionProgramLowerWindowPrice
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonPositionProgramReporterBand
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)(D:XSpace.Run)

def quota (i:ℕ):ℝ:=
  i*Real.log D.ratio+(1+(Real.log 3)⁻¹)*(D.reserve:ℝ)*i*i*Real.log D.ratio

theorem original (simple:G.Simple){s:ℕ}(B:Band R D s):
    let L:=R.family.path.levels
    ∀ᶠ t:ℕ in atTop,let m:=B.reporter+t
    zz L m ≤ (B.index t:ℝ)*Real.log D.ratio ∧
    ∀b:ℕ,B.lower t ≤ b → b ≤ m →
      Compar L.S (zz L) b m ≤ quota D (B.index t) := by
  intro L
  have ages:Tendsto (fun t:ℕ=>B.reporter+t) atTop atTop:=
    tendsto_atTop_mono (fun t=>Nat.le_add_left t B.reporter) tendsto_id
  filter_upwards [((RG05Readout.lambda_growth simple L).comp ages).eventually_ge_atTop 3] with t sold
  intro m
  have grow:(3:ℝ)≤RG16.Lambda L m:=sold
  have lb:1≤Real.log (L.clock.hatBeta m):=by dsimp [RG16.Lambda] at grow; linarith
  have zzprice:zz L m≤ (B.index t:ℝ)*Real.log D.ratio:=by
    calc
      zz L m ≤ RG16.Lambda L m := by
        dsimp [zz,RG16.Lambda]
        linarith [Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one lb)]
      _ ≤ (RG16.Lambda L m)^((3:ℝ)/2) :=by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (show (1:ℝ)≤RG16.Lambda L m by linarith)
            (by norm_num : (1:ℝ)≤3/2)
      _ ≤ _ :=B.floor t
  refine ⟨zzprice,?_⟩
  intro b lo hi
  have zlower:zz L b≤(B.index t:ℝ)*Real.log D.ratio:=((WilsonCoeffUV.Layout.short_mono L simple) hi).trans zzprice
  have old:L.S.scale (B.lower t)≤L.S.scale b:=(WilsonIndependentCapturedDates.increasing R).monotone lo
  have gap:=WilsonIndependentCapturedDates.gap R D B t
  have scale:L.S.scale m-L.S.scale b ≤ (D.reserve:ℝ)*(B.index t:ℝ)*(B.index t:ℝ)*Real.log D.ratio:=by
    change L.S.scale m-L.S.scale (B.lower t)=_ at gap
    linarith
  have count:=WilsonPositionProgramInversionWindowCost.count L.S b (m-b)
  rw [show b+(m-b)=m by omega] at count
  have q:(0:ℝ)<Real.log 3:=Real.log_pos (by norm_num)
  have num:((m-b:ℕ):ℝ) ≤ (Real.log 3)⁻¹*((D.reserve:ℝ)*(B.index t:ℝ)*(B.index t:ℝ)*Real.log D.ratio):=by
    rw [mul_comm, ←div_eq_mul_inv]
    exact (le_div_iff₀ q).mpr (count.trans scale)
  dsimp [Compar,quota]
  linarith

end YM.Integration.WilsonPositionProgramLowerWindowPrice
end
