import YM.Integration.WilsonRootedHeldAffineJoint
import YM.Integration.WilsonVacuumPreResetRenderIncome
import YM.Integration.WilsonPhysicalHistoryRetainedSpringTemperature

/-! Uniform all-orders cut-mean expense for the genuine previous signed site.
    A single reporting date is chosen before every ultraviolet regulator,
    period, compact exterior, retained component, original tree, and tag. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedHeldAffineRate
open Filter Function Lattice Wilson RG Pressure Precision Comparison.RG02
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Physical WilsonLimitConstruction OriginalMarkedRunAction
open WilsonRootedHeldPacketGerm Push.Uniform RG01.Sounder
open scoped Topology BigOperators Classical
variable {G:Gauge}

def shape (G:Gauge)(k:ℕ):ℝ:=(2+|linkBill G 1|)*(1+|Work.F02.slotConst G|)^k

theorem path (G:Gauge)(k n:ℕ)(h:k≤n){σ:ℝ}(hs:0<σ):
    tariff G k 1 σ≤(1+4*σ⁻¹)*shape G n:=by
  have radius:σ/2≤Work.F02.radius σ:= by
    dsimp only [Work.F02.radius]
    linarith only [Real.add_one_le_exp (σ/2)]
  have hr:0<Work.F02.radius σ:=lt_of_lt_of_le (half_pos hs) radius
  have group:1+2/Work.F02.radius σ≤1+4*σ⁻¹:=by
    apply add_le_add_right
    rw [div_le_iff₀ hr,←div_eq_mul_inv,div_mul_eq_mul_div,le_div_iff₀ hs]
    linarith only [radius]
  simp only [tariff,composeCost,Nat.factorial_one,Nat.cast_one,pow_one,one_mul]
  calc
    _≤((1+4*σ⁻¹)*(2+|linkBill G 1|))*(1+|Work.F02.slotConst G|)^n := by
      have hslot:|Work.F02.slotConst G|^k≤(1+|Work.F02.slotConst G|)^n:=
        (pow_le_pow_left₀ (abs_nonneg _) (by linarith) k).trans
          (pow_le_pow_right₀ (by linarith [abs_nonneg (Work.F02.slotConst G)]) h)
      apply mul_le_mul _ hslot (pow_nonneg (abs_nonneg _) _) (by positivity)
      exact (mul_le_mul_of_nonneg_left (by linarith only [le_abs_self (linkBill G 1)])
        (by positivity)).trans (mul_le_mul_of_nonneg_right group (by positivity))
    _= _:=by unfold shape; ring

private theorem numeric {g b σ D l ε:ℝ}{j n k K:ℕ}
    (gp:0<g)(small:g≤1/2)(bp:0<b)(band:(g^2)⁻¹≤2*b)(hs:0<σ)(width:σ⁻¹≤g⁻¹)
    (D0:0≤D)(income:D≤3*g⁻¹)(l0:0≤l)(weight:l≤2*(g^2)⁻¹)
    (k0:k≤K)(stage:n+5≤j)(eps:30*shape G K*g≤ε):
    l*(D*tariff G k 1 σ)*b^(-(j:ℝ))≤ε*g^n:=by
  have pos:0<shape G K:=by unfold shape; positivity
  have g1:g≤1:=small.trans (by norm_num)
  have ig:2≤g⁻¹:=(le_inv_comm₀ (by norm_num) gp).2 (by simpa using small)
  have base:g⁻¹≤b:= by
    rw [←inv_pow] at band
    nlinarith only [band,mul_nonneg (inv_nonneg.mpr gp.le) (sub_nonneg.mpr ig)]
  have cut:b^(-(j:ℝ))≤g^(n+5):=by
    rw [Real.rpow_neg bp.le,Real.rpow_natCast,←inv_pow]
    exact (pow_le_pow_left₀ (inv_nonneg.mpr bp.le) ((inv_le_comm₀ bp gp).2 base) j).trans
      (pow_le_pow_of_le_one gp.le g1 stage)
  have fees:tariff G k 1 σ≤(5*g⁻¹)*shape G K:=(path G k K k0 hs).trans
    (mul_le_mul_of_nonneg_right (by linarith only [ig,width]) pos.le)
  have bill:l*(D*tariff G k 1 σ)≤(2*(g^2)⁻¹)*(3*g⁻¹*((5*g⁻¹)*shape G K)):=by
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left fees D0) l0).trans
    apply mul_le_mul weight _ (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right income (by positivity)
  calc
    _≤(2*(g^2)⁻¹)*(3*g⁻¹*((5*g⁻¹)*shape G K))*g^(n+5):=
      mul_le_mul bill cut (Real.rpow_nonneg bp.le _) (by positivity)
    _=(30*shape G K*g)*g^n:=by rw [pow_add]; field_simp [gp.ne']; ring
    _≤ _:=mul_le_mul_of_nonneg_right eps (pow_nonneg gp.le _)

theorem original (R:Run G)(simple:G.Simple)(credit:Credit)(v:ℕ→Gear G→ℝ)
    (rows:FundedMarkedCoverRows.prices v R.kit)(through K n:ℕ){ε:ℝ}(ep:0<ε):
    let V:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,∀N per:ℕ,m+1<N→∀σ:ℝ,0<σ→σ⁻¹≤zz V (m+1)→
      let D:=credit.buy (zz V (m+1))+zz V (m+1)*V.clock.loopCap (m+1)
      ∀(Z:SeriesA G),Draw Z σ D→∀a∈Z,a.grade≤K→
      let g:=Pert.Asymptotics.regulatorRun R.family N per (m+1)
      let p:=finitePitch R N (m+1) through g
      |siteWeight a g p| *(D*tariff G (a.rise+2) 1 σ)*
        (betaF G (V.clock.hatBeta m) (R.rolls.L (V.clock.J (m+1))))^(-(V.clock.J m:ℝ))≤ε*g^n:=by
  intro V
  obtain ⟨_,heat⟩:=cofinal_temperature R simple v rows through
  let small:=min (1/2:ℝ) (ε/(30*shape G (K+2)))
  have sh:0<shape G (K+2):=by unfold shape; positivity
  have low:0<small:=lt_min (by norm_num) (div_pos ep (by positivity))
  let wage:Credit:=⟨1,1,le_rfl⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually heat,WilsonVacuumPreResetRenderIncome.original R simple credit (η:=1) zero_lt_one,
    (tendsto_add_atTop_nat 1).eventually (exp_at_band wage V simple 1 zero_lt_one),
    (tendsto_add_atTop_nat 1).eventually (IterationFour.Currency.g_small simple R.makes small low),
    V.fits.deep.eventually_ge_atTop (n+5)] with m warm bank spend short far
  intro N per late σ hs width D Z paid a ha grade g p
  have band:=(R.makes.wilson.represents N per (m+1) late.le).band
  change V.clock.hatBeta (m+1)/2≤R.family.path.β N per (m+1) ∧ R.family.path.β N per (m+1)≤2*V.clock.hatBeta (m+1) at band
  have βpos:0<R.family.path.β N per (m+1):=(half_pos (WardBin.hot V (m+1))).trans_le band.1
  have beta:(g^2)⁻¹=R.family.path.β N per (m+1):=by
    change (((Real.sqrt (R.family.path.β N per (m+1)))⁻¹)^2)⁻¹=_
    rw [inv_pow,inv_inv,Real.sq_sqrt βpos.le]
  obtain ⟨gp,-,Dcap,-,-⟩:=bank N per (by omega)
  obtain ⟨-,-,p0,p1,read,-⟩:=warm N late per
  have cost:|siteWeight a g p|≤2*(g^2)⁻¹:=by
    rw [siteWeight,abs_mul,abs_pow]
    have term:|Integral.temperature g*p|≤2*(g^2)⁻¹:=by
      rw [abs_mul,abs_of_nonneg (show 0≤Integral.temperature g from by unfold Integral.temperature; positivity),
        abs_of_nonneg (show 0≤p by linarith only [p0])]
      exact (mul_le_mul_of_nonneg_left (p1.trans (by norm_num)) (inv_nonneg.mpr (sq_nonneg g))).trans_eq (mul_comm ..)
    exact (mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) read)).trans term
  have smallg:g≤ small:=(short N per late.le).le
  have money:=spend (R.family.path.β N per (m+1)) band.1
  change Real.exp (1* (zz V (m+1))^1)≤g^(-(1:ℝ)) at money
  simp only [one_mul,pow_one,Real.rpow_neg_one] at money
  rw [Real.rpow_neg_one] at Dcap
  have realb:V.clock.hatBeta (m+1)=betaF G (V.clock.hatBeta m) (R.rolls.L (V.clock.J (m+1))):=
    Push.PriceCompiler.beta_eq R.alloy.B.valid m
  rw [←realb]
  apply numeric gp (smallg.trans (min_le_left _ _)) (WardBin.hot V _) (beta ▸ band.2) hs
    (width.trans ((by linarith only [Real.add_one_le_exp (zz V (m+1))]:zz V (m+1)≤Real.exp (zz V (m+1))).trans money))
    paid.1 ((le_abs_self _).trans Dcap) (abs_nonneg _) cost (Nat.add_le_add_right (a.rankA.trans grade) 2) far
  simpa only [mul_comm] using (le_div_iff₀ (by positivity :0<30*shape G (K+2))).mp
    (smallg.trans (min_le_right _ _))

end YM.Integration.WilsonRootedHeldAffineRate
