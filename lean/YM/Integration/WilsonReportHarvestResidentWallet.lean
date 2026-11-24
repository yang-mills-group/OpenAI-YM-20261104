import YM.RG05Readout.Many.Pick
import YM.Extra.WILSON_STARTUP.Fast

/-! The genuine dated singleton norm on each color, including every intervening transport weight. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestResidentWallet
open Finset Filter Lattice RG Wilson Marker Extra.Histories RG05Readout.Many
open PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge}

private theorem string_one (C:Family G){m j:ℕ}(mj:m≤j):
    1≤RG05Readout.Address.stringCost C mj:=by
  induction j,mj using Nat.le_induction with
  | base=>rw [RG05Readout.Address.string_base]
  | succ j mj ih=>
    rw [RG05Readout.Address.string_next mj]
    exact one_le_mul_of_one_le_of_one_le (RG05Readout.Address.lamp_nn (C:=C) j) ih

/-- Before every late tuning date, a single wallet covers every subset of at most L genuine residents. -/
theorem weights (C:Family G)(simple:G.Simple)(k h L:ℕ):
    ∀ᶠm:ℕ in atTop,∀j:ℕ,m≤j→∀d:ℕ,∀{V:Type}[DecidableEq V]{J:Census V}
      (Q:V→ℝ), (∀v,0<Q v)→(∀v,Q v≤(C.path.levels.clock.hatBeta m)^h)→
      ∀s:J.Mode,s.val.card≤L→1≤(C.path.levels.clock.hatBeta j)^((k+h)*L)*
        Real.exp ((L:ℝ)*(C.S.scale j-C.S.scale m))*
        Poly.toll (fun v=>RG05Readout.Many.envelope C m d k (Q v) j) s:=by
  filter_upwards [RG05Readout.Address.string_paid (C:=C) (by norm_num:0<(1:ℝ))]
    with m funded j mj d V inst J Q qp cap s card
  let x:=C.path.levels.clock.hatBeta j
  let f:=RG05Readout.Address.stringCost C mj
  let e:=C.S.scale j-C.S.scale m
  have x1:1≤x:=(C.path.levels.fits.delayed j).le
  have xp:0<x:=zero_lt_one.trans_le x1
  have ef:0≤e:=sub_nonneg.mpr ((OPE.scale_mono C.S).monotone mj)
  have f1:1≤f:=string_one C mj
  have fp:0<f:=zero_lt_one.trans_le f1
  have fcap:f≤Real.exp e:=by simpa only [one_mul] using funded j mj
  have qhigh (v:V):Q v≤x^h:=(cap v).trans
    (pow_le_pow_left₀ (zero_lt_one.trans (C.path.levels.fits.delayed m)).le
      (WilsonStartup.Timing.hat_mono C.path.levels (Gauge.slopeConstant_pos simple).le mj) h)
  have width (v:V):RG05Readout.Many.envelope C m d k (Q v) j=(x^k*(Q v*f))⁻¹:=by
    unfold RG05Readout.Many.envelope RG05Readout.Many.west
    rw [rust_above mj,one_mul]
    unfold markWidth
    rw [total_upper mj,mul_inv_rev,div_eq_mul_inv,mul_comm]
  let unit:=x^(k+h)*Real.exp e
  have unit1:1≤unit:=one_le_mul_of_one_le_of_one_le (one_le_pow₀ x1) (Real.one_le_exp ef)
  have amount:0<∏v∈s.val,(x^k*(Q v*f)):=prod_pos fun v _=>mul_pos (pow_pos xp _) (mul_pos (qp v) fp)
  have ranged (v:V):x^k*(Q v*f)≤unit:=calc
    _≤x^k*(x^h*Real.exp e):=mul_le_mul_of_nonneg_left (mul_le_mul (qhigh v) fcap fp.le (pow_nonneg xp.le _)) (pow_nonneg xp.le _)
    _=unit:=by dsimp only [unit];rw [pow_add,mul_assoc]
  have total:(∏v∈s.val,(x^k*(Q v*f)))≤x^((k+h)*L)*Real.exp ((L:ℝ)*e):=calc
    _≤∏_v∈s.val,unit:=prod_le_prod (fun v _=>mul_nonneg (pow_nonneg xp.le _) (mul_nonneg (qp v).le fp.le)) (fun v _=>ranged v)
    _=unit^s.val.card:=prod_const _
    _≤unit^L:=pow_le_pow_right₀ unit1 card
    _=_:=by dsimp only [unit];rw [mul_pow,←pow_mul,←Real.exp_nat_mul]
  simp only [Poly.toll,width,Finset.prod_inv_distrib]
  rw [←div_eq_mul_inv]
  exact (le_div_iff₀ amount).mpr (by simpa only [one_mul] using total)
end YM.Integration.WilsonReportHarvestResidentWallet
