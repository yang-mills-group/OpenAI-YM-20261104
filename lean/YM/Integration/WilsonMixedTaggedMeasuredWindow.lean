import YM.FullVolume.Cross
import YM.Integration.WilsonMeasuredWindow
import YM.RG05Readout.Many.Iota
import YM.OPE.Exchange.Regime

/-! The original first crossing and its first reporting stop supply the
spatial and date bounds for the full lower-interval marker bill. The paid
slow-block inequality is exactly the second component of the funded pace. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedMeasuredWindow
open Filter Lattice OPE OPE.Log PhysicalNext.Repeat.Legato
open scoped Classical Topology
variable {G:Gauge} (R:Run G)

private theorem paced (slow:∀j,((R.family.S.block j).val:ℝ) ≤ Real.log (RG05Readout.Lambda R.family.path.levels j))
    (j:ℕ) : ((R.family.S.block j).val:ℝ) ≤ WilsonAdmissionScale.logarithm R.family.path.levels j := by
  let b:ℝ:=(R.family.S.block j).val
  let x:=WilsonAdmissionScale.logarithm R.family.path.levels j
  have strong : (2:ℕ) ≤ (R.family.S.block j).val := by have h:=R.family.S.block_large j; omega
  have hb : 2 ≤ b := by
    change (2:ℝ) ≤ ((R.family.S.block j).val:ℝ)
    exact_mod_cast strong
  have hx : 0 ≤ x := Real.log_nonneg (R.family.path.levels.fits.delayed j).le
  have lo : b ≤ Real.log (2+x) := slow j
  have two : (2:ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1:ℝ)]
  have rest : b ≤ Real.exp (b-1) := by linarith only [Real.add_one_le_exp (b-1)]
  have grow : b+2 ≤ Real.exp b := calc
    b+2 ≤ 2*b := by linarith
    _ ≤ Real.exp 1*Real.exp (b-1) := mul_le_mul two rest (by linarith only [hb]) (Real.exp_pos 1).le
    _=Real.exp b := by rw [←Real.exp_add]; congr 1; ring
  have upper := (Real.le_log_iff_exp_le (by linarith only [hx] : 0 < 2+x)).mp lo
  change b ≤ x
  linarith only [grow,upper]

theorem original (simple:G.Simple) (K:ℕ) (hk:0 < K)
    (slow:∀j,((R.family.S.block j).val:ℝ) ≤ Real.log (RG05Readout.Lambda R.family.path.levels j)) :
    let C:=R.family
    let m:=WilsonMeasuredWindow.stop C.path.levels simple K
    let b:=fun r=>RG05Readout.crossLevel C.S r-1-1
    Tendsto m (𝓝[>] (0:ℝ)) atTop ∧ ∀ᶠ r in 𝓝[>] (0:ℝ),
      b r+1 < m r ∧ C.S.a (b r)/C.S.a (m r) ≤ (RG05Readout.Lambda C.path.levels (m r))^(K+3) ∧ 
        ((m r-b r:ℕ):ℝ) ≤ ((K+3:ℕ):ℝ)*(1+Real.log (RG05Readout.Lambda C.path.levels (m r))) := by
  intro C m b
  have pace:=paced R slow
  have dates:=WilsonMeasuredWindow.stop_tendsto C.path.levels simple K hk
  have zoom:Tendsto (fun r:ℝ=>OPE.run r) (𝓝[>] (0:ℝ)) atTop := by
    simpa only [Function.comp_def,Real.log_inv,OPE.run] using
      (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero)
  have physical:RateIs (𝓝[>] (0:ℝ)) OPE.run id (-1) := OPE.loglife tendsto_id
  obtain ⟨dated,bracket⟩ := RG05Readout.pace_crossing C.path.levels.fits.mesh zoom physical
  refine ⟨dates,?_⟩
  filter_upwards [bracket,dated.grows.eventually_ge_atTop 2,physical.pos] with r ends depth hr
  let q:=RG05Readout.crossLevel C.S r
  have high:2 ≤ q:=depth
  have prev:b r+1=q-1 := by change q-1-1+1=q-1; omega
  have left:C.S.a (b r+1+1) < r := by rw [prev,show q-1+1=q by omega]; exact ends.1
  have right:r ≤ C.S.a (b r+1) := by rw [prev]; exact ends.2
  have before : b r+1 < m r := WilsonMeasuredWindow.before_stop C.path.levels simple K hk hr (b r+1) right
  have bm : b r ≤ m r := by omega
  let A:=C.path.levels
  let mast:=RG05Readout.Lambda A (m r)
  have span : C.S.a (b r+1)/C.S.a (m r) ≤ mast^(K+2) :=
    WilsonMeasuredWindow.ratio_le A simple K pace hk hr (b r+1) right left
  have nonneg : 0 ≤ WilsonAdmissionScale.logarithm A (m r) := Real.log_nonneg (A.fits.delayed _).le
  have pay : WilsonAdmissionScale.logarithm A (m r) ≤ mast := by
    change WilsonAdmissionScale.logarithm A (m r) ≤ 2+WilsonAdmissionScale.logarithm A (m r)
    linarith
  have pos : 0 ≤ mast := nonneg.trans pay
  have block : ((C.S.block (b r)).val:ℝ) ≤ mast :=
    (pace _).trans ((WilsonAdmissionScale.logarithm_monotone A simple bm).trans pay)
  have ratio : C.S.a (b r)/C.S.a (m r) ≤ mast^(K+3) := calc
    _ = ((C.S.block (b r)).val:ℝ)*(C.S.a (b r+1)/C.S.a (m r)) := by
      have same := C.S.embeds_scale (C.S.oneStep (b r) 0)
      change C.S.a (b r+1)*((C.S.block (b r)).val:ℝ)=C.S.a (b r) at same
      rw [←same]
      ring
    _ ≤ mast*mast^(K+2) := mul_le_mul block span (div_pos (C.S.a_pos _) (C.S.a_pos _)).le pos
    _ = _ := (mul_comm _ _).trans (pow_succ mast (K+2)).symm
  refine ⟨before,ratio,?_⟩
  have rent := Real.log_le_log (div_pos (C.S.a_pos _) (C.S.a_pos _)) ratio
  rw [Real.log_div (C.S.a_pos _).ne' (C.S.a_pos _).ne',Real.log_pow] at rent
  have ha (j:ℕ) : Real.log (C.S.a j) = -C.S.scale j := by simp [Schedule.scale]
  rw [ha,ha] at rent
  have dates:=RG05Readout.Many.tall (C:=C) _ _ bm
  change ((m r-b r:ℕ):ℝ) ≤ ((K+3:ℕ):ℝ)*(1+Real.log mast)
  linarith only [rent,dates,(Nat.cast_nonneg (K+3) : (0:ℝ) ≤ (K+3:ℕ))]

end YM.Integration.WilsonMixedTaggedMeasuredWindow
