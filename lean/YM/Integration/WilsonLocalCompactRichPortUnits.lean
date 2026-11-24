import YM.Integration.WilsonLocalCompactRichPortClock

/-! Engineering units of the rich port and the physical reporting coupling. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactRichPortUnits
open Filter Lattice RG Wilson RG16 Precision OPE OPE.Log Trace.Pilot PhysicalNext.Repeat.Legato Pert.Asymptotics Real
open private square from YM.Integration.WilsonLocalCompactClock
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
local notation "C" => R.family
local notation "A" => R.family.path.levels

theorem compared (simple:G.Simple) {i m N:ℕ} (im:i ≤ m) (cut:m≤N) (per:ℕ):
    regulatorRun C N per m≤2*regulatorRun C N per i:=by
  let g:=regulatorRun C N per
  let a:=(C).path.β N per i
  let z:=(C).path.β N per m
  have lo:= (R.makes.wilson.represents N per m cut).band.1
  have p:= (R.makes.wilson.represents N per i (im.trans cut)).band
  change (A).clock.hatBeta m/2≤z at lo
  change (A).clock.hatBeta i/2≤a ∧ a≤2*(A).clock.hatBeta i at p
  have ap:0<a:=by linarith only [p.1,(A).fits.delayed i]
  have zp:0<z:=by linarith only [lo,(A).fits.delayed m]
  have cmp:a≤4*z:=by linarith only [p.2,lo,WilsonStartup.Timing.hat_mono A (G.slopeConstant_pos simple).le im]
  have gp (k):0≤g k:=inv_nonneg.mpr (sqrt_nonneg _)
  apply (sq_le_sq₀ (gp m) (mul_nonneg (by norm_num) (gp i))).1
  rw [square R cut,mul_pow,square R (im.trans cut),show (2:ℝ)^2*(1/a)=4/a by ring]
  exact (div_le_div_iff₀ zp ap).2 (by simpa only [one_mul] using cmp)

theorem original (simple:G.Simple)(pace:∀m,((R.family.S.block m).val:ℝ)≤Real.log (RG16.Lambda R.family.path.levels m))
    (M B:ℝ)(mp:0<M)(bp:20<B) (h q:ℕ) {ε:ℝ}(ep:0<ε):
    ∀ᶠ m:ℕ in atTop,let b:=RG16.Literal.port C (8*M) B (mul_pos (by norm_num) mp) m
    ∀N,m≤N→∀per,let g:=regulatorRun C N per
      ((C).S.a b/(C).S.a m)^h*g m^(q+1)≤ε*g m^q:=by
  let c:ℝ:=2^(q+1)
  have cp:0<c:=by dsimp [c];positivity
  filter_upwards [WilsonMacroscopicRichReportingRate.original R simple pace M B mp bp h q (div_pos ep cp),
    RG16.Literal.port_small C simple (8*M) B (mul_pos (by norm_num) mp) (by linarith only [bp])] with m rate cut b N live per g
  let a:=((C).S.a b/(C).S.a m)^h
  have ap:0≤a:=pow_nonneg (div_nonneg ((C).S.a_pos _).le ((C).S.a_pos _).le) _
  have bound:=pow_le_pow_left₀ (inv_nonneg.mpr (sqrt_nonneg _)) (compared R simple cut.le live per) (q+1)
  rw [mul_pow] at bound
  calc a*g m^(q+1)≤a*(c*g (b+1)^(q+1)):=mul_le_mul_of_nonneg_left bound ap
    _=c*(a*g (b+1)^(q+1)):=by ring
    _≤c*((ε/c)*g m^q):=mul_le_mul_of_nonneg_left (rate N per live) cp.le
    _=ε*g m^q:=by field_simp

end YM.Integration.WilsonLocalCompactRichPortUnits
