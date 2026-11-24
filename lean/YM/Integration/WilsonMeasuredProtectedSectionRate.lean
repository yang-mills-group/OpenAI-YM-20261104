import YM.Integration.WilsonMeasuredProtectedColumnFare

/-! The registered physical section at fixed rank costs two additional
powers of the actual adjacent coupling, uniformly before both regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredProtectedSectionRate
open Filter Lattice RG Wilson Labels Push.Local Planned.GuardedAtom
open Trace.Physical PhysicalNext Repeat Legato Roost Org Pert.Asymptotics RG16
open scoped Classical Topology

variable {G:Gauge} (R:Run G)

theorem band (simple:G.Simple) {m j N per:ℕ} (mj:m≤j) (live:j≤N) :
    regulatorRun R.family N per j ≤ 2*regulatorRun R.family N per m :=by
  let A:=R.family.path.levels
  let y:=(R.family.path.rep N per j).beta
  let x:=(R.family.path.rep N per m).beta
  have yp:0<y:=RG02.Actual.coupling_pos R.makes.wilson live
  have xp:0<x:=RG02.Actual.coupling_pos R.makes.wilson (mj.trans live)
  have l:A.clock.hatBeta j/2≤y :=(R.makes.wilson.represents N per j live).band.1
  have r:x≤2*A.clock.hatBeta m :=(R.makes.wilson.represents N per m (mj.trans live)).band.2
  have mono:A.clock.hatBeta m≤A.clock.hatBeta j:=(Real.log_le_log_iff
    (zero_lt_one.trans (A.fits.delayed m)) (zero_lt_one.trans (A.fits.delayed j))).mp
      (WilsonAdmissionScale.logarithm_monotone A simple mj)
  have xr:=Real.sqrt_pos.mpr xp
  have yr:=Real.sqrt_pos.mpr yp
  change (Real.sqrt y)⁻¹≤2*(Real.sqrt x)⁻¹
  rw [←div_eq_mul_inv,le_div_iff₀ xr,inv_mul_le_iff₀ yr]
  nlinarith only [r,l,mono,Real.sq_sqrt xp.le,Real.sq_sqrt yp.le,xr,yr]

private def fee (d:ℕ) :=
  Real.exp (102*atomTiles (R.family.localSection d))*(1+5*|readPrice R.family.params (R.family.labels.level d)|)

private theorem positive (d:ℕ) : 0<fee R d :=by unfold fee;positivity

theorem original (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (d q:ℕ) {ε:ℝ} (ep:0<ε) :
    ∃δ>0,∀ᶠ i:ℕ in atTop,∀ (N per m:ℕ), i < N → m ≤ i →
      ∀W:Rep G (R.family.side i per), W.p=R.family.path.levels.budget i → W.p.supportExponent≤100 →
      ∀ (a M:ℝ),0≤a → 0≤M → a≤δ*(regulatorRun R.family N per (i+1))^(q+2)*M →
      factor R.family.params (R.family.localSection d) W.p.supportExponent
        (R.family.path.levels.params i).columns*a ≤ (ε*(regulatorRun R.family N per m)^q)*M :=by
  let D:=fee R d
  have Dpos:0<D:=positive R d
  let δ:=ε/(D*2^q)
  have δpos:0<δ:=div_pos ep (mul_pos Dpos (by positivity))
  refine ⟨δ,δpos,?_⟩
  have rise:Tendsto R.family.path.levels.clock.hatBeta atTop atTop:=
    tendsto_atTop_add_const_left _ _ (R.family.path.levels.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  filter_upwards [WilsonCapturedPrimarySection.priced R simple slow,
    (tendsto_add_atTop_nat 1).eventually (rise.eventually (eventually_ge_atTop (2:ℝ)))]
    with i columns thin N per m live earlier W _ fixed a M ha hM earns
  let A:=R.family.path.levels
  let g:=regulatorRun R.family N per (i+1)
  let h:=regulatorRun R.family N per m
  let w:=(A.params i).columns
  let r:=readPrice R.family.params (R.family.labels.level d)
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (RG02.Actual.coupling_pos R.makes.wilson live))
  have hp:0<h:=inv_pos.mpr (Real.sqrt_pos.mpr (RG02.Actual.coupling_pos R.makes.wilson (earlier.trans live.le)))
  have born : 1 ≤ (R.family.path.rep N per (i+1)).beta :=by
    have lower:R.family.path.levels.clock.hatBeta (i+1)/2≤(R.family.path.rep N per (i+1)).beta:=
      (R.makes.wilson.represents N per (i+1) live).band.1
    linarith only [thin,lower]
  have cheap:g≤1:=inv_le_one_of_one_le₀ (by simpa using Real.sqrt_le_sqrt born)
  have l:w*g^2≤4:=(le_div_iff₀ (pow_pos gp 2)).mp (columns N per live)
  have wn:0≤w:=zero_le_one.trans (A.params i).columns_ge
  have g2:g^2≤1:=pow_le_one₀ gp.le cheap
  have scaled:(1+w)*g^2≤5:=by nlinarith only [l,g2]
  have rg:(1+w)*g^2*r≤5*|r|:=((mul_le_mul_of_nonneg_left (le_abs_self r)
    (mul_nonneg (by linarith only [wn]) (sq_nonneg g))).trans
    (mul_le_mul_of_nonneg_right scaled (abs_nonneg r)))
  have priced:(atomPrice R.family.params (R.family.labels.level d) w)*g^2≤1+5*|r|:=by
    change (1+(1+w)*r)*g^2≤_
    nlinarith only [rg,g2]
  let S:=R.family.localSection d
  have expo:Real.exp ((W.p.supportExponent+2)*atomTiles S)≤Real.exp (102*atomTiles S):=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith only [fixed]) (Nat.cast_nonneg _))
  have raw:factor R.family.params S W.p.supportExponent w*g^2≤D:=by
    change Real.exp ((W.p.supportExponent+2)*atomTiles S)*atomPrice R.family.params (R.family.labels.level d) w*g^2 ≤ _
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left priced (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_right expo (by positivity))
  have unit:factor R.family.params S W.p.supportExponent w≤D/g^2:=(le_div_iff₀ (pow_pos gp _)).mpr raw
  have changeDate:g^q≤2^q*h^q:=by
    rw [←mul_pow];exact pow_le_pow_left₀ gp.le (band R simple (earlier.trans (Nat.le_succ i)) live) q
  calc
    _ ≤ (D/g^2)*(δ*g^(q+2)*M) := (mul_le_mul_of_nonneg_right unit ha).trans
      (mul_le_mul_of_nonneg_left earns (div_nonneg Dpos.le (sq_nonneg g)))
    _ = (ε/2^q)*g^q*M :=by dsimp [δ];rw [pow_add];field_simp [Dpos.ne',gp.ne']
    _ ≤ (ε/2^q)*(2^q*h^q)*M:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left changeDate (div_nonneg ep.le (by positivity))) hM
    _ = _ :=by dsimp [h];field_simp

end YM.Integration.WilsonMeasuredProtectedSectionRate
end
