import YM.Integration.WilsonSeparatedPrefixMovingFiledSeats
import YM.Integration.WilsonIndependentMovingRosterAllFineClock
import YM.Integration.WilsonThermometerAncestralCalendar

/-! The engineering power of the actual measured station salary on its
original optical window is fixed by its field height before the finite
thermal order is selected. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingFiledFiscal
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Next.Foundations WilsonLimitConstruction XSpace
open WilsonPositionProgramTrialStationHome (chargeAt elapsed)
open WilsonCoeffUV.Bank.Ticket (zz)
open private salary from YM.Integration.WilsonIndependentMovingRosterAllFineClock
open scoped BigOperators Classical
variable {G:Gauge}

theorem heat (P:Run G)(m N per:ℕ)(hi:m ≤ N):
    0<Pert.Asymptotics.regulatorRun P.family N per m ∧
    P.family.path.levels.clock.hatBeta m ≤ (3*(Pert.Asymptotics.regulatorRun P.family N per m)⁻¹)^2:=by
  have cold:=P.family.path.levels.fits.delayed m
  have band:= (P.makes.wilson.represents N per m hi).band.1
  have hp:0 < P.family.path.β N per m:=lt_of_lt_of_le (half_pos (zero_lt_one.trans cold)) band
  change P.family.path.levels.clock.hatBeta m/2 ≤ P.family.path.β N per m at band
  constructor
  · exact inv_pos.mpr (Real.sqrt_pos.mpr hp)
  · change _ ≤ (3*(Real.sqrt (P.family.path.β N per m))⁻¹⁻¹)^2
    rw [inv_inv,mul_pow,Real.sq_sqrt hp.le]
    linarith only [band,hp]

theorem window (P:Run G)(m K N per:ℕ)(mid:m ≤ K)(top:K ≤ N)(A:ℝ)(_ap:0 ≤ A)
    (cold:3 ≤ P.family.path.levels.clock.hatBeta m):
    let L:=P.family.path.levels
    let g:=Pert.Asymptotics.regulatorRun P.family N per m
    let x:=-Real.log g
    1 ≤ x → L.S.a m/L.S.a K ≤ g^(-A) →
      1 ≤ zz L m ∧ zz L m ≤ WilsonPositionProgramTrialStationHome.age L m K ∧ WilsonPositionProgramTrialStationHome.age L m K ≤ (8+2*A)*x ∧
      Real.exp (elapsed L m K)=L.S.a m/L.S.a K:=by
  intro L g x warm opt
  let T:=L.clock.hatBeta m
  have hp:=heat P m N per (mid.trans top)
  have gp:0<g:=hp.1
  have tp:0<T:=lt_of_lt_of_le (by norm_num:0<(3:ℝ)) cold
  have shade:=Real.log_le_log tp hp.2
  change Real.log T≤Real.log ((3*g⁻¹)^2) at shade
  rw [Real.log_pow,Real.log_mul (by norm_num) (inv_ne_zero gp.ne'),Real.log_inv] at shade
  have log3:1 ≤ Real.log T:=by
    rw [←Real.exp_le_exp,Real.exp_log tp];exact Real.exp_one_lt_three.le.trans cold
  have cheap:Real.log (3:ℝ) ≤ 2:=by linarith only [Real.log_le_sub_one_of_pos (by norm_num:0<(3:ℝ))]
  have a:1 ≤ zz L m:=by change 1≤1+Real.log (Real.log T);linarith only [Real.log_nonneg log3]
  have z:zz L m ≤ 8*x:=by
    change 1+Real.log (Real.log T)≤_
    have ll:=Real.log_le_sub_one_of_pos (zero_lt_one.trans_le log3)
    dsimp only [x] at warm ⊢;norm_num at shade;linarith only [warm,cheap,shade,ll]
  have ratio:Real.exp (elapsed L m K)=L.S.a m/L.S.a K:=by
    have eq:=pace_rep L.S m K
    rw [Real.exp_neg] at eq
    exact (inv_eq_iff_eq_inv.mp eq.symm).trans (by simp [paceT])
  have span:=Real.log_le_log (Real.exp_pos (elapsed L m K)) (ratio.trans_le opt)
  rw [Real.log_exp,Real.log_rpow gp] at span
  have duration:=WilsonSeparatedPrefixMovingCalendar.days L.S m K mid
  have elapsed₀:0 ≤ elapsed L m K:=(Nat.cast_nonneg (K-m)).trans duration
  refine ⟨a,?_,?_,ratio⟩
  · unfold WilsonPositionProgramTrialStationHome.age;linarith only [elapsed₀,Nat.cast_nonneg (α:=ℝ) (K-m)]
  · dsimp only [WilsonPositionProgramTrialStationHome.age,x]
    dsimp only [x] at z;change ((K-m:ℕ):ℝ) ≤ elapsed L m K at duration
    nlinarith only [z,span,duration]

theorem original (P:Run G)(simple:G.Simple)(Q:SealR G)(e:ℕ)(B Z:Credit)(A η:ℝ)
    (ap:0 ≤ A)(gain:0<η):
    ∀ᶠ m:ℕ in atTop,∀K N per:ℕ,m ≤ K → K ≤ N →
    let L:=P.family.path.levels
    let g:=Pert.Asymptotics.regulatorRun P.family N per m
    L.S.a m/L.S.a K ≤ g^(-A) →
      |chargeAt L Q e B Z m K| ≤ ((Fintype.card (Alma Q.F):ℝ)*(e+1)*(Fintype.card (Alma Q.F):ℝ))*
        g^(-(A*Q.h+η)):=by
  obtain ⟨x₀,invest⟩:=eventually_atTop.1 (salary (B.prodC Z) (8+2*A) η gain)
  let v:=max 1 x₀
  filter_upwards [(RG01.Physical.hats simple P.family.path.levels).eventually_ge_atTop (max 3 (9*Real.exp (2*v)))]
    with m late K N per low top L g opt
  have hp:=heat P m N per (low.trans top)
  have gp:0<g:=hp.1
  have cold:3 ≤ L.clock.hatBeta m:=(le_max_left _ _).trans late
  have hot:9*Real.exp (2*v) ≤ (3*g⁻¹)^2:=((le_max_right _ _).trans late).trans hp.2
  have high:v ≤ -Real.log g:=by
    have ineq:Real.exp (2*v) ≤ (g⁻¹)^2:=by nlinarith only [hot]
    have logged:=Real.log_le_log (Real.exp_pos _) ineq
    rw [Real.log_exp,Real.log_pow,Real.log_inv] at logged;norm_num at logged;linarith only [logged]
  have sale:=window P m K N per low top A ap cold ((le_max_left ..).trans high) opt
  have c:=invest (-Real.log g) ((le_max_right ..).trans high) (WilsonPositionProgramTrialStationHome.age L m K) (zero_le_one.trans (sale.1.trans sale.2.1)) sale.2.2.1
  rw [Credit.products] at c
  have B0:0 ≤ B.buy (zz L m):=zero_le_one.trans (B.purchase sale.1)
  have Z0:0 ≤ Z.buy (WilsonPositionProgramTrialStationHome.age L m K):=zero_le_one.trans (Z.purchase (sale.1.trans sale.2.1))
  have bound:B.buy (zz L m)*Z.buy (WilsonPositionProgramTrialStationHome.age L m K) ≤ g^(-η):=by
    rw [Real.rpow_def_of_pos gp]
    exact ((mul_le_mul_of_nonneg_right (B.elder sale.1 sale.2.1) Z0).trans c).trans_eq (by congr 1;ring)
  let fixed:ℝ:=(Fintype.card (Alma Q.F):ℝ)*(e+1)*(Fintype.card (Alma Q.F):ℝ)
  have hpower:(Real.exp (elapsed L m K))^Q.h ≤ (g^(-A))^Q.h:=pow_le_pow_left₀ (Real.exp_pos _).le (sale.2.2.2.trans_le opt) _
  have nonnegative:0 ≤ chargeAt L Q e B Z m K:=by unfold chargeAt;positivity
  rw [abs_of_nonneg nonnegative]
  calc
    _=fixed*((Real.exp (elapsed L m K))^Q.h*(B.buy (zz L m)*Z.buy (WilsonPositionProgramTrialStationHome.age L m K))):=by dsimp [chargeAt,fixed];ring
    _ ≤ fixed*((g^(-A))^Q.h*g^(-η)):=mul_le_mul_of_nonneg_left (mul_le_mul hpower bound (mul_nonneg B0 Z0)
      (pow_nonneg (Real.rpow_nonneg gp.le _) _)) (by dsimp only [fixed];positivity)
    _=_:=by rw [←Real.rpow_natCast (g^(-A)) Q.h,←Real.rpow_mul gp.le,←Real.rpow_add gp];congr 2;ring

end YM.Integration.WilsonSeparatedPrefixMovingFiledFiscal
