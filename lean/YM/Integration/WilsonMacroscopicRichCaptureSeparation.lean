import YM.Integration.WilsonMacroscopicRichReportingRate

/-! Actual distance between the reported source, its original capture cells, and a moving exterior. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichCaptureSeparation
open Filter Lattice Wilson RG OPE Spec RG16 RG16.Literal Pert.Asymptotics Real
open PhysicalNext.Repeat.Legato
open private logs from YM.Integration.WilsonMacroscopicRichReportingRate
open scoped Classical Topology
variable {G:Gauge}(R:Run G)

/-- There are only three additional powers of the original logarithmic chart radius. -/
theorem mesh (simple:G.Simple)(pace:∀m,((R.family.S.block m).val:ℝ)≤log (Lambda R.family.path.levels m))
    (M B:ℝ)(hm:0<M)(hb:20<B):∀ᶠ m:ℕ in atTop,
    let b:=port R.family (8*M) B (mul_pos (by norm_num) hm) m
    ∀ρ:ℝ,(Lambda R.family.path.levels m)^B≤ρ → R.family.S.a b≤(8*M)*(Lambda R.family.path.levels m)^3*(R.family.S.a m*ρ):=by
  have hp:0<8*M:=by positivity
  filter_upwards [outer_bound R.family simple (8*M) B hp (by linarith only [hb]) pace] with m outer
  intro b ρ lo
  let L:=Lambda R.family.path.levels m
  have lp:0<L:=lambda_pos R.family m
  have ao:R.family.S.a b≤(8*M*(L^(B+1))*L^2)*R.family.S.a m:=(div_le_iff₀ (R.family.S.a_pos m)).mp outer
  have expand:L^(B+1)=L^B*L:=by rw [rpow_add lp,rpow_one]
  have le: L^B≤ρ:=lo
  calc R.family.S.a b≤(8*M*L^(B+1)*L^2)*R.family.S.a m:=ao
       _=(8*M)*L^3*(R.family.S.a m*L^B):=by rw [expand];ring
       _≤_:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left le (R.family.S.a_pos m).le) (mul_nonneg hp.le (pow_nonneg lp.le _))

/-- A collar of any fixed logarithmic width around the actual near capture is negligible relative to r/g_m. -/
theorem regulator (simple:G.Simple)(pace:∀m,((R.family.S.block m).val:ℝ)≤log (Lambda R.family.path.levels m))
    (M B:ℝ)(hm:0<M)(hb:20<B)(D:ℕ){ε:ℝ}(ep:0<ε):∀ᶠ m:ℕ in atTop,
    let b:=port R.family (8*M) B (mul_pos (by norm_num) hm) m
    ∀N p,m≤N →∀ρ:ℝ,(Lambda R.family.path.levels m)^B≤ρ →
      R.family.S.a b*(Lambda R.family.path.levels m)^D*(regulatorRun R.family N p m)≤ε*(R.family.S.a m*ρ):=by
  let A:=R.family.path.levels
  have up:0<16*M:=by positivity
  filter_upwards [mesh R simple pace M B hm hb,logs R simple (3+D) (div_pos ep up)] with m occupied small
  intro b N p live ρ lo
  let L:=Lambda A m;let x:=A.clock.hatBeta m;let v:=R.family.path.β N p m
  have low:x/2≤v:=(R.makes.wilson.represents N p m live).band.1
  have xp:0<x:=zero_lt_one.trans (A.fits.delayed m)
  have vp:0<v:=RG02.Actual.coupling_pos R.makes.wilson live
  let g:=regulatorRun R.family N p m
  have gp:0≤g:=inv_nonneg.mpr (sqrt_nonneg v)
  have sx:0<sqrt x:=sqrt_pos.2 xp
  have sv:0<sqrt v:=sqrt_pos.2 vp
  have root:sqrt x≤2*sqrt v:=by
    have t:=sqrt_le_sqrt (show x≤4*v by linarith only [low,vp]);rw [sqrt_mul (by norm_num:(0:ℝ)≤4)] at t;norm_num at t ⊢;exact t
  have gg:g≤2/sqrt x:=by have t:1/sqrt v≤2/sqrt x:=(div_le_div_iff₀ sv sx).2 (by simpa using root);simpa [g,regulatorRun,v,div_eq_mul_inv] using t
  have lp:0<L:=lambda_pos R.family m
  have ps:0<ρ:=lt_of_lt_of_le (rpow_pos_of_pos lp B) lo
  have positive:0<R.family.S.a m*ρ:=mul_pos (R.family.S.a_pos m) ps
  have cost: L^(3+D)≤ε/(16*M)*sqrt x:=small
  have paid:8*M*(L^(3+D)*g)≤ε:=by
    calc _ ≤8*M*((ε/(16*M)*sqrt x)*(2/sqrt x)):=mul_le_mul_of_nonneg_left (mul_le_mul cost gg gp (mul_nonneg (div_nonneg ep.le up.le) sx.le)) (by positivity)
         _=ε:=by field_simp [hm.ne',sx.ne'];ring
  calc _ ≤ ((8*M)*L^3*(R.family.S.a m*ρ))*L^D*g:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (occupied ρ lo) (pow_nonneg lp.le _)) gp
       _=(8*M*(L^(3+D)*g))*(R.family.S.a m*ρ):=by rw [pow_add];ring
       _≤_:=mul_le_mul_of_nonneg_right paid positive.le
end YM.Integration.WilsonMacroscopicRichCaptureSeparation
