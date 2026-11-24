import YM.Integration.WilsonReportingForestBlocks
import YM.Integration.WilsonHeldRetainedActionRate

/-! The local physical Taylor radius is a measured coupling times a fixed
logarithmic cost even for all bonds incident on the registered parents. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredChartTaylorRate
open Filter Lattice RG Wilson OPE.Therm RG16 Pert.Asymptotics
open PhysicalNext.Repeat.Legato
open WilsonPhysicalLocalPlaquetteForest WilsonPhysicalLocalPlaquetteReserve WilsonReportingForestBlocks
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels

theorem logarithmic (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda A m))
    (H:ℕ) : ∀ᶠ j:ℕ in atTop,∀per (D:ℕ),let L:=((A).clock.op j per).ratio.count.val
      D≤extent H L → area D L*cool A (j+1)≤tariff (H+4)*Real.log ((A).clock.hatBeta (j+1))^20*(Real.sqrt ((A).clock.hatBeta (j+1)))⁻¹ := by
  have grows:=(Next.Rank.Station.hat_rate A simple).comp (tendsto_add_atTop_nat 1)
  filter_upwards [(Real.tendsto_log_atTop.comp grows).eventually_ge_atTop (1:ℝ)] with j hs per D L hd
  let b:=(A).clock.hatBeta (j+1)
  let s:=Real.log b
  change 1≤ s at hs
  have s4:1≤ s^4:=one_le_pow₀ hs
  have ld:(L:ℝ)≤2+s:=(slow j).trans ((Real.log_le_self (Literal.lambda_pos R.family j).le).trans
    ((Literal.lambda_mono R.family simple).monotone (Nat.le_succ j)))
  have l3:(L:ℝ)≤3*s:=by linarith only [hs,ld]
  have l4:(L:ℝ)≤3*s^4:=l3.trans (mul_le_mul_of_nonneg_left (le_self_pow₀ hs (by decide:4≠0)) (by norm_num))
  have h0:0≤(H:ℝ):=H.cast_nonneg
  have h4:(H:ℝ)≤H*s^4:=by simpa only [mul_one] using mul_le_mul_of_nonneg_left s4 h0
  have de:(D:ℝ)≤H+8*(L:ℝ)+1:=by exact_mod_cast hd
  have big:(D:ℝ)≤9*((H+4:ℕ):ℝ)*s^4:=by push_cast;nlinarith only [de,l4,h4,h0,s4]
  have room:=(scalar (H+4) D L hs big l3).2
  change area D L*((Real.sqrt b)⁻¹*s^12)≤(tariff (H+4)*s^20)*(Real.sqrt b)⁻¹
  calc _=(area D L*s^12)*(Real.sqrt b)⁻¹:=by ring
       _≤_:=mul_le_mul_of_nonneg_right room (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- A Taylor error of degree q+1 costs arbitrarily little relative to the
measured power q. C and K can be the complete source coefficient mass and
the authentic exponential-chart scale, fixed before the period and cutoff. -/
theorem purchased (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda A m))
    (H q:ℕ) (C K:ℝ) (c0:0≤C) (k0:0≤K) {ε:ℝ} (he:0<ε) :
    ∀ᶠ j:ℕ in atTop,∀N per, j+1≤N → ∀D (δ:ℝ), let L:=((A).clock.op j per).ratio.count.val
      D≤extent H L → 0≤δ → δ≤K*(area D L*cool A (j+1)) →
      C*δ^(q+1) ≤ ε*regulatorRun R.family N per (j+1)^q := by
  let W:=K*tariff (H+4)
  let X:=C*W^(q+1)*2^q
  have tr:0≤tariff (H+4):=by unfold tariff;positivity
  have wp:0≤W:=mul_nonneg k0 tr
  have grows:=(Next.Rank.Station.hat_rate A simple).comp (tendsto_add_atTop_nat 1)
  filter_upwards [logarithmic R simple slow H,grows.eventually (small X (20*(q+1)) he)]
    with j shape pay N per live D δ L room δ0 allowed
  let b:=(A).clock.hatBeta (j+1)
  let s:=Real.log b
  let hg:=(Real.sqrt b)⁻¹
  let g:=regulatorRun R.family N per (j+1)
  have b1:1<b:=(A).fits.delayed _
  have bp:0<b:=zero_lt_one.trans b1
  have sp:0≤ s:=(Real.log_pos b1).le
  have hp:0≤hg:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson live))
  have band : R.family.path.β N per (j+1) ≤ 2*b := (R.makes.wilson.represents N per (j+1) live).band.2
  have upper: R.family.path.β N per (j+1) ≤ 4*b:=by linarith only [band,bp]
  have sq:=Real.sqrt_le_sqrt upper
  rw [Real.sqrt_mul (by norm_num:0≤(4:ℝ)),show Real.sqrt 4=2 by norm_num] at sq
  have fineBeta : 0<R.family.path.β N per (j+1) := Overlay.beta_positive R.makes.wilson live
  have compared : 1/Real.sqrt b ≤ 2/Real.sqrt (R.family.path.β N per (j+1)) :=
    (div_le_div_iff₀ (Real.sqrt_pos.mpr bp) (Real.sqrt_pos.mpr fineBeta)).mpr (by simpa only [one_mul] using sq)
  have ratio:hg≤2*g:=by
    change (Real.sqrt b)⁻¹ ≤ 2*(Real.sqrt (R.family.path.β N per (j+1)))⁻¹
    simpa only [div_eq_mul_inv,one_mul] using compared
  have sized:δ≤W*s^20*hg:=(allowed.trans (mul_le_mul_of_nonneg_left (shape per D room) k0)).trans_eq (by dsimp [W,s,hg,b];ring)
  change X*s^(20*(q+1))*hg≤ε at pay
  calc
    C*δ^(q+1) ≤ C*(W*s^20*hg)^(q+1) := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ δ0 sized _) c0
    _ = (C*W^(q+1)*s^(20*(q+1))*hg)*hg^q := by
      rw [mul_pow,mul_pow,←pow_mul,pow_succ hg q];ring
    _ ≤ (C*W^(q+1)*s^(20*(q+1))*hg)*(2*g)^q :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp ratio _) (by positivity)
    _ = (X*s^(20*(q+1))*hg)*g^q := by rw [mul_pow];dsimp [X];ring
    _ ≤ ε*g^q := mul_le_mul_of_nonneg_right pay (pow_nonneg gp.le _)

end YM.Integration.WilsonRegisteredChartTaylorRate
