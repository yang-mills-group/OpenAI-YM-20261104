import YM.Integration.WilsonReportHarvestSlabFees

/-! The fixed earlier Wilson door sets a finite price before any later
turn, period or source size. It consumes the original cubic invoice once. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabReserve
open Lattice Wilson Labels RG Source Extra.Histories Push Local
open Planned.GuardedAtom Guard MergeProof Accent Menu Marker RG05Readout
open RG05Readout.Many RG05Readout.Address Bid Pressure Copper Ac GridApprox.Nil
open Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage
open Next.Rank.Station Ribbons
open scoped BigOperators Classical
variable {G:Gauge} (C:Family G)
theorem original (simple:G.Simple) (b d:ℕ) :
    ∃charge:ℝ,1≤charge ∧ ∀t,b+1<t→∀k (Q:ℝ),1≤Q→∀ δ E:ℝ,0≤δ→
      2*δ*(WilsonAllDateHarvestIntervalPrice.bill C (b+1) t (d+1) k Q)^3≤E/charge →
      bling C.path.levels b*(2*δ*(4*(1/Many.fee C t (b+1) d k 3 Q)))≤E := by
  obtain ⟨F,fpos,paid⟩:=WilsonReportHarvestSlabFees.original C simple (b+1) d
  let x:=bling C.path.levels b
  let charge:=max 1 (4*x*F)
  have one:1≤charge:=le_max_left ..
  have rate:4*x*F≤charge:=le_max_right ..
  have cpos:0<charge:=zero_lt_one.trans_le one
  have xpos:0<x:=Real.exp_pos _
  refine ⟨charge,one,fun t bt k Q q δ E pos receipt=>?_⟩
  let B:=WilsonAllDateHarvestIntervalPrice.bill C (b+1) t (d+1) k Q
  let fee:=Many.fee C t (b+1) d k 3 Q
  have hf:=paid t bt k Q q
  have bpos:0≤B:=by
    have beta:0≤C.path.levels.clock.hatBeta t:=zero_le_one.trans (C.path.levels.fits.delayed t).le
    exact mul_nonneg (mul_nonneg (pow_nonneg beta _) (zero_le_one.trans q))
      (pow_nonneg (div_pos (C.S.a_pos _) (C.S.a_pos _)).le _)
  have ink:0≤2*δ*B^3:=mul_nonneg (mul_nonneg (by norm_num) pos) (pow_nonneg bpos _)
  calc x*(2*δ*(4*(1/fee)))=8*x*δ*fee⁻¹:=by rw [one_div];ring
       _ ≤ 8*x*δ*(F*B^3):=mul_le_mul_of_nonneg_left hf.2 (by positivity)
       _ = (2*δ*B^3)*(4*x*F):=by ring
       _ ≤ (2*δ*B^3)*charge:=mul_le_mul_of_nonneg_left rate ink
       _ ≤ E:=(le_div_iff₀ cpos).1 receipt

end YM.Integration.WilsonReportHarvestSlabReserve
