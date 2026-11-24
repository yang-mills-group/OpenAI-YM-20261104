import YM.Integration.WilsonReportHarvestSlabSigned
import YM.Integration.WilsonAllDateHarvestIntervalPrice

/-! Price the actual capture radius by exactly one cubic historical bill.
The remaining finite price depends only on the held capture scale and
engineering degree, before either period or ultraviolet cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabFees
open MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Push Local
open Planned.GuardedAtom Guard MergeProof Accent Menu Marker RG05Readout
open RG05Readout.Many RG05Readout.Address Bid Pressure Copper Ac GridApprox.Nil
open Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage
open Next.Rank.Station Ribbons
open scoped BigOperators Classical
variable {G:Gauge} (C:Family G)

theorem original (simple:G.Simple) (n d:ℕ) :
    ∃F:ℝ,0<F ∧ ∀t,n<t→∀k (Q:ℝ),1≤Q →
      0<Many.fee C t n d k 3 Q ∧
      (Many.fee C t n d k 3 Q)⁻¹≤F*(WilsonAllDateHarvestIntervalPrice.bill C n t (d+1) k Q)^3 := by
  let rho:=Bandage.renal C.path.levels n
  let step:=((C.S.block n).val:ℝ)⁻¹^(4+d)
  let E:=Real.exp (((C.path.levels.budget n).supportExponent+1/2)*peepers C.path.levels n)
  let c:=min (1/2:ℝ) (rho*step)
  let s:=rho/3*c/E
  have rp:0<rho:=Real.rpow_pos_of_pos (zero_lt_one.trans (C.path.levels.fits.delayed (n+1))) _
  have length:0<((C.S.block n).val:ℝ):=by exact_mod_cast (C.S.block n).property
  have stepPos:0<step:=pow_pos (inv_pos.mpr length) _
  have xp:0<E:=Real.exp_pos _
  have cp:0<c:=lt_min (by norm_num) (mul_pos rp stepPos)
  have sp:0<s:=div_pos (mul_pos (div_pos rp (by norm_num)) cp) xp
  refine ⟨s⁻¹^3,pow_pos (inv_pos.mpr sp) _,fun t nt k Q hQ=>?_⟩
  let B:=WilsonAllDateHarvestIntervalPrice.bill C n t (d+1) k Q
  let w:=RG05Readout.Many.envelope C t (d+1) k Q (n+1)
  let ζ:=Many.syrup C t n d k 3 Q
  have one:1≤B:=by
    have hL:1≤C.S.a n/C.S.a t:=(one_le_div (C.S.a_pos t)).2 (C.S.strictAnti.antitone nt.le)
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (C.path.levels.fits.delayed t).le) hQ) (one_le_pow₀ hL)
  have wp:0<w:=mul_pos (rust_paid _).1 (grantw (totalpos (zero_lt_one.trans_le hQ) _))
  let j:=(Stock.census Unit).fire ()
  have paid:=WilsonAllDateHarvestIntervalPrice.modes C simple (d:=d+1) (k:=k) n.le_succ nt hQ j
    (show j.val.card≤1 by simp [j,Census.fire])
  have enough:1≤B*w:=by simpa only [Poly.toll,j,Census.fire,Finset.prod_singleton,pow_one] using paid
  have bound:c≤B*Many.crust C t n d k Q:=by
    change c≤B*min (1/2:ℝ) (rho*w*step)
    by_cases hf:1/2≤rho*w*step
    · rw [min_eq_left hf]
      exact (min_le_left _ _).trans (le_mul_of_one_le_left (by norm_num) one)
    · rw [min_eq_right (le_of_not_ge hf)]
      calc c ≤ rho*step := min_le_right _ _
           _ ≤ (rho*step)*(B*w) := le_mul_of_one_le_right (mul_pos rp stepPos).le enough
           _ = _ := by ring
  have cup:0<Many.crust C t n d k Q:=lt_min (by norm_num) (mul_pos (mul_pos rp wp) stepPos)
  have zp:0<ζ:=div_pos (mul_pos (div_pos rp (by norm_num)) cup) xp
  have earns:s≤B*ζ:=by
    calc s ≤ (rho/3)*(B*Many.crust C t n d k Q)/E :=
             div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left bound (by positivity)) xp.le
         _ = _ := by change _=B*(rho/3*Many.crust C t n d k Q/E);ring
  have inv : ζ⁻¹ ≤ s⁻¹ * B := by
    rw [inv_eq_one_div,←div_eq_inv_mul]
    exact (div_le_div_iff₀ zp sp).2 (by simpa only [one_mul,mul_comm B] using earns)
  refine ⟨pow_pos zp _,?_⟩
  have charge:=pow_le_pow_left₀ (inv_nonneg.mpr zp.le) inv 3
  simpa only [Many.fee,inv_pow,mul_pow] using charge

end YM.Integration.WilsonReportHarvestSlabFees
